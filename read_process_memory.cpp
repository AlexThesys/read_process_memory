#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <windows.h>
#include <psapi.h>
#include <tlhelp32.h>
#include <tchar.h>
#include <assert.h>
#include <emmintrin.h>
#include <omp.h>
#include <mutex>
#include <condition_variable>
#include <vector> // temp

#define MAX_BUFFER_SIZE 0x1000
#define MAX_PATTERN_LEN 0x40
#define MAX_PID_STR_LEN 16
#define MAX_OMP_THREADS 8
#define MAX_MEMORY_USAGE_IDEAL 0X40000000

enum input_type {
    it_hex,
    it_ascii,
    it_error_type,
};

typedef struct search_data {
    input_type type;
    uint64_t value;
    const char* pattern;
    size_t pattern_len;
} search_data;

static const char* page_state[] = {"MEM_COMMIT", "MEM_FREE", "MEM_RESERVE"};
static const char* page_type[] = {"MEM_IMAGE", "MEM_MAPPED", "MEM_PRIVATE"};
static const char* page_protect[] = {"PAGE_EXECUTE", "PAGE_EXECUTE_READ", "PAGE_EXECUTE_READWRITE", "PAGE_EXECUTE_WRITECOPY", "PAGE_NOACCESS", "PAGE_READONLY", 
                                    "PAGE_READWRITE", "PAGE_WRITECOPY", "PAGE_TARGETS_INVALID", "UNKNOWN"};

static int list_processes();
static int list_process_modules(DWORD dw_pid);
static int list_process_threads(DWORD dw_owner_pid);
static int traverse_heap_list(DWORD dw_pid);
static void print_error(TCHAR const* msg);

inline int is_hex(const char *pattern, size_t pattern_len) {
    return (((pattern_len > 2) && (pattern[pattern_len - 1] == 'h' || pattern[pattern_len - 1] == 'H'))
        || ((pattern_len > 3) && (pattern[0] == '0' && pattern[1] == 'x')));
}

static const char* get_page_state(DWORD state) {
    const char *result = NULL;
    switch (state) {
    case MEM_COMMIT:
        result = page_state[0];
        break;
    case MEM_FREE:
        result = page_state[1];
        break;
    case MEM_RESERVE:
        result = page_state[2];
        break;
    }
    return result;
}

static void print_page_type(DWORD state) {
    printf("Type:");
    if (state == MEM_IMAGE) {
        printf(" %s\n", page_type[0]);
    } else {
        if (state & MEM_MAPPED) {
            printf(" %s ", page_type[1]);
        }
        if (state & MEM_PRIVATE) {
            printf(" %s ", page_type[2]);
        }
        puts("");
    }
}

static const char* get_page_protect(DWORD state) {
    // lets not comlicate things with other available options for now
    state &= ~(PAGE_GUARD | PAGE_NOCACHE | PAGE_WRITECOMBINE);

    const char* result;
    switch (state) {
    case PAGE_EXECUTE:
        result = page_protect[0];
        break;
    case PAGE_EXECUTE_READ:
        result = page_protect[1];
        break;
    case PAGE_EXECUTE_READWRITE:
        result = page_protect[2];
        break;
    case PAGE_EXECUTE_WRITECOPY:
        result = page_protect[3];
        break;
    case PAGE_NOACCESS:
        result = page_protect[4];
        break;
    case PAGE_READONLY:
        result = page_protect[5];
        break;
    case PAGE_READWRITE:
        result = page_protect[6];
        break;
    case PAGE_WRITECOPY:
        result = page_protect[7];
        break;
    case PAGE_TARGETS_INVALID:
        result = page_protect[8];
        break;
    default:
        result = page_protect[9];
        break;
    }
    return result;
}
 
static void parse_input(const char* pattern, search_data *data) {
    if (data->pattern_len > MAX_PATTERN_LEN) {
        fprintf(stderr, "Pattern exceeded maximum size of %d. Exiting...", MAX_PATTERN_LEN);
        data->type = it_error_type;
        return;
    }
    uint64_t value = 0;
    char* end;
    value = strtoull(pattern, &end, 0x10);
    const int is_hex = (pattern != end);

    if (is_hex) {
        data->type = it_hex;
        data->value = value;
        data->pattern = (const char*)&data->value;
        if (*end == 'h' || *end == 'H') {
            data->pattern_len = size_t(end - pattern);
        } else if (pattern[0] == '0' && (pattern[1] == 'x' || pattern[1] == 'X')) {
            data->pattern_len -= 1;
        }
        data->pattern_len /= 2;
        if (data->pattern_len <= sizeof(uint64_t)) {
            puts("\nSearching for a hex value...\n");
        } else {
            printf("Max supported hex value size: %d bytes!\n", (int)sizeof(uint64_t));
            data->type = it_error_type;
        }
    } else {
        data->type = it_ascii;
        data->pattern = pattern;
        puts("\nSearching for an ascii string...\n");
    }
}

#define _max(x,y) (x) > (y) ? (x) : (y)
#define _min(x,y) (x) < (y) ? (x) : (y)
#define step (sizeof(__m128i) / sizeof(uint8_t))

static const uint8_t* strstr_u8(const uint8_t* str, size_t str_sz, const uint8_t* substr, size_t substr_sz) {
    if (/*!substr_sz || */(str_sz < substr_sz))
        return NULL;

    const __m128i first = _mm_set1_epi8(substr[0]);
    const __m128i last = _mm_set1_epi8(substr[substr_sz - 1]);
    const uint8_t skip_first = (uint8_t)(substr_sz > 2);
    const size_t cmp_size = substr_sz - (1llu << skip_first);

    for (size_t j = 0, sz = str_sz - substr_sz; j <= sz; j += step) {
        const uint8_t* f = str + j;
        const uint8_t* l = str + j + substr_sz - 1;
        __m128i xmm0 = _mm_loadu_si128(reinterpret_cast<const __m128i*>(f));
        __m128i xmm1 = _mm_loadu_si128(reinterpret_cast<const __m128i*>(l));

        xmm0 = _mm_cmpeq_epi8(first, xmm0);
        xmm1 = _mm_cmpeq_epi8(last, xmm1);
        xmm0 = _mm_and_si128(xmm0, xmm1);

        uint32_t mask = (uint32_t)_mm_movemask_epi8(xmm0);

        const uint8_t max_offset = (uint8_t)_min(step, str_sz - (j + substr_sz) + 1);
        const uint32_t max_offset_mask = (1 << max_offset) - 1;
        mask &= max_offset_mask;
        unsigned long bit = 0;

        while (_BitScanForward(&bit, mask)) {
            const uint32_t offset = bit;
            const uint8_t* m0 = str + j + offset + skip_first;
            const uint8_t* m1 = substr + skip_first;
            if (memcmp(m0, m1, cmp_size) == 0)
                return (str + j + offset);

            mask ^= (1 << bit); // clear bit
        }
    }

    return NULL;
}

static std::mutex g_err_mtx;
static std::mutex g_mtx;
static std::condition_variable g_cv;
static LONG g_memory_usage_bytes = 0; // accessed from different threads
static int g_max_omp_threads = MAX_OMP_THREADS;
static int g_show_failed_readings = 0;

static void find_pattern(HANDLE process, const char* pattern, size_t pattern_len) {
    std::vector<std::vector<const char*>> match;
    std::vector<const char*> p;
    std::vector<MEMORY_BASIC_INFORMATION> info;
    size_t max_memory_usage = MAX_MEMORY_USAGE_IDEAL;

    puts("Searching committed memory...");
    puts("\n------------------------------------\n");
    {
        const char* _p = NULL;
        MEMORY_BASIC_INFORMATION _info;
        for (_p = NULL; VirtualQueryEx(process, _p, &_info, sizeof(_info)) == sizeof(_info); _p += _info.RegionSize) {
            if (_info.State == MEM_COMMIT) {
                info.push_back(_info);
                p.push_back(_p);
                max_memory_usage = _max(max_memory_usage, _info.RegionSize);
            }
        }
    }
    const size_t num_regions = info.size();
    match.resize(num_regions);

    const int num_threads = _min(g_max_omp_threads, omp_get_num_procs());
    omp_set_num_threads(num_threads);   
#pragma omp parallel for schedule(dynamic, 1) shared(match,p,info)
    for (int64_t i = 0;  i < (int64_t)num_regions; i++) {
        assert((info[i].Type == MEM_MAPPED || info[i].Type == MEM_PRIVATE || info[i].Type == MEM_IMAGE));
        size_t region_size = info[i].RegionSize;
        {
            std::unique_lock<std::mutex> lk(g_mtx);
            while (true) {
                g_cv.wait(lk, [max_memory_usage] { return (g_memory_usage_bytes < max_memory_usage); });
                if (g_memory_usage_bytes < max_memory_usage) {
                    g_memory_usage_bytes += region_size;
                    break;
                }
            }
        }

        char* buffer = (char*)malloc(region_size);
        if (!buffer) {
            puts("Heap allocation failed!");
            break;;
        }

        SIZE_T bytes_read;
        const BOOL res = ReadProcessMemory(process, p[i], buffer, region_size, &bytes_read);
        if (!res || (bytes_read != region_size)) {
            if (!g_show_failed_readings) {
                if (!res) {
                    continue;
                } else {
                    region_size = bytes_read;
                }
            } else {
                std::unique_lock<std::mutex> lk(g_err_mtx);
                if (info[i].Type == MEM_IMAGE) {
                    char module_name[MAX_PATH];
                    if (GetModuleFileNameExA(process, (HMODULE)info[i].AllocationBase, module_name, MAX_PATH)) {
                        puts("------------------------------------\n");
                        printf("Module name: %s\n", module_name);
                    }
                }
                printf("Base addres: 0x%p\tAllocation Base: 0x%p\tRegion Size: 0x%llx\nState: %s\tProtect: %s\t",
                    info[i].BaseAddress, info[i].AllocationBase, info[i].RegionSize, get_page_protect(info[i].Protect), get_page_state(info[i].State));
                print_page_type(info[i].Type);
                if (!res) {
                    fprintf(stderr, "Failed reading process memory. Error code: %lu\n\n", GetLastError());
                    continue;
                } else {
                    region_size = bytes_read;
                    printf("Process memory not read in it's entirety! 0x%llx bytes skipped out of 0x%llx\n\n", (region_size - bytes_read), region_size);
                }
            }
        }

        if (bytes_read >= pattern_len) {
            const char* buffer_ptr = buffer;
            size_t buffer_size = region_size;

            while (buffer_size >= pattern_len) {
                const char* old_buf_ptr = buffer_ptr;
                buffer_ptr = (const char*)strstr_u8((const uint8_t*)buffer_ptr, buffer_size, (const uint8_t*)pattern, pattern_len);
                if (!buffer_ptr) {
                    break;
                }

                const size_t buffer_offset = buffer_ptr - buffer;
                match[i].push_back(p[i] + buffer_offset);

                buffer_ptr++;
                buffer_size -= (buffer_ptr - old_buf_ptr);
            }
        }
        free(buffer);
        {
            std::unique_lock<std::mutex> lk(g_mtx);
            g_memory_usage_bytes -= region_size;
        }
        g_cv.notify_all(); // permitted to be called concurrentely
    }

    size_t num_matches = 0;
    for (size_t i = 0; i < num_regions; i++) {
        if (match[i].size()) {
            if (info[i].Type == MEM_IMAGE) {
                char module_name[MAX_PATH];
                if (GetModuleFileNameExA(process, (HMODULE)info[i].AllocationBase, module_name, MAX_PATH)) {
                    puts("------------------------------------\n");
                    printf("Module name: %s\n", module_name);
                }
            }
            printf("Base addres: 0x%p\tAllocation Base: 0x%p\tRegion Size: 0x%llx\nState: %s\tProtect: %s\t",
                info[i].BaseAddress, info[i].AllocationBase, info[i].RegionSize, get_page_protect(info[i].Protect), get_page_state(info[i].State));
            print_page_type(info[i].Type);
            for (const char* m : match[i]) {
                printf("Match at address: 0x%p\n", m);
            }

            puts("");
            num_matches++;
        }
    }

    if (!num_matches) {
        puts("No matches found.");
    }
}

static constexpr int check_architecture_ct() {
#if defined(__x86_64__) || defined(_M_X64)
    return 1;
#elif defined(i386) || defined(__i386__) || defined(__i386) || defined(_M_IX86)
    return 1;
#else
    return 0;
#endif
}
static_assert(check_architecture_ct(), "Only x86-64 architecture is supported at the moment!");

static int check_architecture_rt() {
    SYSTEM_INFO SystemInfo;
    GetSystemInfo(&SystemInfo);
    return int(SystemInfo.wProcessorArchitecture == PROCESSOR_ARCHITECTURE_AMD64
                || SystemInfo.wProcessorArchitecture == PROCESSOR_ARCHITECTURE_INTEL);
}

const char* cmd_args[] = { "-h", "--help", "-f", "--show-failed-readings", "-t=", "--threads=" };

static void parse_cmd_args(int argc, const char** argv) {
    for (int i = 1; i < argc; i++) {
        if ((0 == strcmp(argv[1], cmd_args[0])) || (0 == strcmp(argv[1], cmd_args[1]))) {
            puts("-t=<num_threads> || --threads==\t\t -- limits the number of OMP threads");
            puts("-f || --show-failed-readings\t\t -- show the regions, that failed to be read\n");
        } else if ((0 == strcmp(argv[i], cmd_args[2])) || (0 == strcmp(argv[i], cmd_args[3]))) {
            g_show_failed_readings = 1;
        } else if ((argv[i] == strstr(argv[i], cmd_args[4])) || (argv[i] == strstr(argv[i], cmd_args[5]))) {
            const char* num_t = (argv[i][1] == '-') ? (argv[i] + strlen(cmd_args[5])) : (argv[i] + strlen(cmd_args[4]));
            char* end = NULL;
            size_t arg_len = strlen(num_t);
            DWORD num_threads = strtoul(num_t, &end, is_hex(num_t, arg_len) ? 16 : 10);
            if (num_t != end) {
                num_threads = _max(1, num_threads);
                g_max_omp_threads = _min(num_threads, g_max_omp_threads);
            }
        }
        // ...
    }
}

int main(int argc, const char** argv) {
    if (!check_architecture_rt()) {
        puts("Only x86-64 architecture is supported at the moment!");
        return 1;
    }

    parse_cmd_args(argc, argv);

    char pattern[MAX_PATTERN_LEN];
    char pid_str[MAX_PID_STR_LEN];
    size_t pid_len = -1;
    int stop = 'n';
    int res;
    int symbol = (int)'n';

    puts("List system's processes? y/n");
    symbol = getchar();
    if (symbol == (int)'y' || symbol == (int)'Y') {
        list_processes();
        puts("\n\n====================================\n");
    }

    do {
        int use_same_pid = 0;
        if (pid_len != -1) {
            puts("Use same PID? y/n");
            while ((getchar()) != '\n'); // flush stdin
            symbol = getchar();
            use_same_pid = (symbol == (int)'y' || symbol == (int)'Y');
        }

        if (!use_same_pid) {
            if (pid_len != -1) {
                puts("List system's processes? y/n");
                while ((getchar()) != '\n'); // flush stdin
                symbol = getchar();
                if (symbol == (int)'y' || symbol == (int)'Y') {
                    list_processes();
                    puts("\n\n====================================\n");
                }
            }
            puts("Input PID: ");
            res = scanf_s("%s", pid_str, (unsigned int)sizeof(pid_str));
            if (EOF == res || 0 == res) {
                puts("Error reading PID!");
                return 1;
            }
            pid_len = strlen(pid_str);
        }

        char* end = NULL;
        const DWORD pid = strtoul(pid_str, &end, is_hex(pid_str, pid_len) ? 16 : 10);
        if (pid_str == end) {
            puts("Invalid PID! Exiting...");
            return 1;
        }

        if (!use_same_pid) {
            puts("List process's modules? y/n");
            while ((getchar()) != '\n'); // flush stdin
            symbol = getchar();
            if (symbol == (int)'y' || symbol == (int)'Y') {
                list_process_modules(pid);
                puts("\n\n====================================\n");
            }

            puts("List process's threads? y/n");
            while ((getchar()) != '\n'); // flush stdin
            symbol = getchar();
            if (symbol == (int)'y' || symbol == (int)'Y') {
                list_process_threads(pid);
                puts("\n\n====================================\n");
            }

            puts("Travers process's heap list (slow)? y/n");
            while ((getchar()) != '\n'); // flush stdin
            symbol = getchar();
            if (symbol == (int)'y' || symbol == (int)'Y') {
                traverse_heap_list(pid);
                puts("\n\n====================================\n");
            }
        }

        puts("Input pattern (hex value or ascii string (no whitespace)): ");
        res = scanf_s("%s", pattern, (unsigned int)sizeof(pattern));
        if (EOF == res || 0 == res) {
            puts("Error reading pattern!");
            return 1;
        }
        const size_t pattern_len = strlen(pattern);
        assert(pattern_len != 0);

        search_data data;
        data.pattern_len = pattern_len;

        parse_input(pattern, &data);
        if (data.type == it_error_type) {
            return 1;
        }

        HANDLE process = OpenProcess(PROCESS_VM_READ | PROCESS_QUERY_INFORMATION, false, pid);
        if (process == NULL) {
            fprintf(stderr, "Failed opening the process. Error code: %lu\n", GetLastError());
            return 1;
        }

        char proc_name[MAX_PATH];
        if (GetModuleFileNameExA(process, NULL, proc_name, MAX_PATH)) {
            printf("Process name: %s\n\n", proc_name);
        }

        find_pattern(process, data.pattern, data.pattern_len);

        CloseHandle(process);

        puts("====================================\n");
        puts("\nContinue search? y/n");
        while ((getchar()) != '\n'); // flush stdin
        stop = getchar();
    } while (stop == (int)'y' || stop == (int)'Y');

    return 0;
}

static int list_processes() {
    HANDLE hProcessSnap;
    HANDLE hProcess;
    PROCESSENTRY32 pe32;
    DWORD dwPriorityClass;

    // Take a snapshot of all processes in the system.
    hProcessSnap = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0);
    if (hProcessSnap == INVALID_HANDLE_VALUE) {
        print_error(TEXT("CreateToolhelp32Snapshot (of processes)"));
        return(FALSE);
    }

    // Set the size of the structure before using it.
    pe32.dwSize = sizeof(PROCESSENTRY32);

    // Retrieve information about the first process,
    // and exit if unsuccessful
    if (!Process32First(hProcessSnap, &pe32)) {
        print_error(TEXT("Process32First")); // show cause of failure
        CloseHandle(hProcessSnap);          // clean the snapshot object
        return(FALSE);
    }

    // Now walk the snapshot of processes, and
    // display information about each process in turn
    do {
        _tprintf(TEXT("\n\n====================================================="));
        _tprintf(TEXT("\nPROCESS NAME:  %s"), pe32.szExeFile);
        _tprintf(TEXT("\n-------------------------------------------------------"));

        // Retrieve the priority class.
        dwPriorityClass = 0;
        hProcess = OpenProcess(PROCESS_ALL_ACCESS, FALSE, pe32.th32ProcessID);
        if (hProcess == NULL) {
            print_error(TEXT("OpenProcess"));
        } else {
            dwPriorityClass = GetPriorityClass(hProcess);
            if (!dwPriorityClass)
                print_error(TEXT("GetPriorityClass"));
            CloseHandle(hProcess);
        }

        _tprintf(TEXT("\n  Process ID        = 0x%08X"), pe32.th32ProcessID);
        _tprintf(TEXT("\n  Thread count      = %d"), pe32.cntThreads);
        _tprintf(TEXT("\n  Parent process ID = 0x%08X"), pe32.th32ParentProcessID);
        _tprintf(TEXT("\n  Priority base     = %d"), pe32.pcPriClassBase);
        if (dwPriorityClass)
            _tprintf(TEXT("\n  Priority class    = %d"), dwPriorityClass);

    } while (Process32Next(hProcessSnap, &pe32));

    CloseHandle(hProcessSnap);
    return(TRUE);
}

static int list_process_modules(DWORD dw_pid) {
    HANDLE hModuleSnap = INVALID_HANDLE_VALUE;
    MODULEENTRY32 me32;

    // Take a snapshot of all modules in the specified process.
    hModuleSnap = CreateToolhelp32Snapshot(TH32CS_SNAPMODULE, dw_pid);
    if (hModuleSnap == INVALID_HANDLE_VALUE) {
        print_error(TEXT("CreateToolhelp32Snapshot (of modules)"));
        return(FALSE);
    }

    // Set the size of the structure before using it.
    me32.dwSize = sizeof(MODULEENTRY32);

    // Retrieve information about the first module,
    // and exit if unsuccessful
    if (!Module32First(hModuleSnap, &me32)) {
        print_error(TEXT("Module32First"));  // show cause of failure
        CloseHandle(hModuleSnap);           // clean the snapshot object
        return(FALSE);
    }

    // Now walk the module list of the process,
    // and display information about each module
    do {
        _tprintf(TEXT("\n\n     MODULE NAME:     %s"), me32.szModule);
        _tprintf(TEXT("\n     Executable     = %s"), me32.szExePath);
        _tprintf(TEXT("\n     Process ID     = 0x%08X"), me32.th32ProcessID);
        _tprintf(TEXT("\n     Ref count (g)  = 0x%04X"), me32.GlblcntUsage);
        _tprintf(TEXT("\n     Ref count (p)  = 0x%04X"), me32.ProccntUsage);
        _tprintf(TEXT("\n     Base address   = 0x%08X"), (DWORD)me32.modBaseAddr);
        _tprintf(TEXT("\n     Base size      = 0x%x"), me32.modBaseSize);

    } while (Module32Next(hModuleSnap, &me32));

    CloseHandle(hModuleSnap);
    return(TRUE);
}

typedef struct stack_info {
    DWORD_PTR sp;
    SIZE_T size;
} stack_info;

static int get_thread_stack_base(HANDLE hThread, HANDLE process, stack_info *res) {
    CONTEXT context;
    context.ContextFlags = CONTEXT_CONTROL;
    GetThreadContext(hThread, &context);
#ifdef _WIN64
    DWORD_PTR sp = context.Rsp; // Stack pointer for 64-bit
#else
    DWORD_PTR sp = context.Esp; // Stack pointer for 32-bit
#endif

    int stack_base_found = 0;
    MEMORY_BASIC_INFORMATION _info;
    if (VirtualQueryEx(process, (LPCVOID)sp, &_info, sizeof(_info)) == sizeof(_info)) {
        if (_info.State == MEM_COMMIT && _info.Type == MEM_PRIVATE) {
            res->sp = (DWORD_PTR)_info.BaseAddress;
            res->size = _info.RegionSize;
            stack_base_found = 1;
        }
    }

    return stack_base_found;
}

static int list_process_threads(DWORD dw_owner_pid) {
    HANDLE hThreadSnap = INVALID_HANDLE_VALUE;
    THREADENTRY32 te32;
    stack_info si = { NULL, 0 };

    // Take a snapshot of all running threads  
    hThreadSnap = CreateToolhelp32Snapshot(TH32CS_SNAPTHREAD, 0);
    if (hThreadSnap == INVALID_HANDLE_VALUE)
        return (FALSE);

    // Fill in the size of the structure before using it. 
    te32.dwSize = sizeof(THREADENTRY32);

    // Retrieve information about the first thread,
    // and exit if unsuccessful
    if (!Thread32First(hThreadSnap, &te32)) {
        print_error(TEXT("Thread32First")); // show cause of failure
        CloseHandle(hThreadSnap);
        return (FALSE);
    }

    HANDLE process = OpenProcess(PROCESS_VM_READ | PROCESS_QUERY_INFORMATION, false, dw_owner_pid);
    if (process == NULL) {
        fprintf(stderr, "Failed opening the process. Error code: %lu\n", GetLastError());
        CloseHandle(hThreadSnap);
        return (FALSE);
    }

    // Now walk the thread list of the system,
    // and display information about each thread
    // associated with the specified process
    do {
        if (te32.th32OwnerProcessID == dw_owner_pid) {
            HANDLE hThread = OpenThread(THREAD_ALL_ACCESS, FALSE, te32.th32ThreadID);
            if (hThread != NULL) {
                if (!get_thread_stack_base(hThread, process, &si)) {
                    puts("Failed acquiring stack base!");
                }
                CloseHandle(hThread);
            }

            _tprintf(TEXT("\n\n     THREAD ID         = 0x%08X"), te32.th32ThreadID);
            _tprintf(TEXT("\n     Base priority     = %d"), te32.tpBasePri);
            _tprintf(TEXT("\n     Delta priority    = %d"), te32.tpDeltaPri);
            _tprintf(TEXT("\n     Stack Base        = 0x%p"), si.sp);
            _tprintf(TEXT("\n     Stack Size        = 0x%llx"), si.size);
            _tprintf(TEXT("\n"));
        }
    } while (Thread32Next(hThreadSnap, &te32));

    CloseHandle(process);
    CloseHandle(hThreadSnap);
    return(TRUE);
}

#define NUM_VALUES 0x100

struct entropy_context {
    size_t freq[NUM_VALUES];
};

static void entropy_init(entropy_context * ctx) {
    memset(ctx->freq, 0, sizeof(ctx->freq));
}

static void entropy_calculate_frequencies(entropy_context* ctx, const uint8_t* data, size_t  size) {
    // Calculate frequencies of each byte
    for (size_t i = 0; i < size; i++) {
        ctx->freq[data[i]]++;
    }
}

static double entropy_compute(entropy_context* ctx, size_t size) {
    double entropy = 0.0;
    const double sz = (double)size;
    for (int i = 0; i < NUM_VALUES; i++) {
        if (ctx->freq[i] != 0) {
            double probability = (double)ctx->freq[i] / sz;
            entropy -= probability * log2(probability);
        }
    }

    return entropy;
}

static int traverse_heap_list(DWORD dw_pid) {
    HEAPLIST32 hl;

    HANDLE hHeapSnap = CreateToolhelp32Snapshot(TH32CS_SNAPHEAPLIST, dw_pid);

    hl.dwSize = sizeof(HEAPLIST32);

    if (hHeapSnap == INVALID_HANDLE_VALUE) {
        printf("CreateToolhelp32Snapshot failed (%d)\n", GetLastError());
        return 1;
    }

    if (Heap32ListFirst(hHeapSnap, &hl)) {
        puts("List all heap blocks? y/n");
        while ((getchar()) != '\n'); // flush stdin
        char symbol = getchar();
        const int list_all_blocks = !!(symbol == (int)'y' || symbol == (int)'Y');
        puts("Compute entropy? (extra slow) y/n");
        while ((getchar()) != '\n'); // flush stdin
        symbol = getchar();
        int compute_entropy = !!(symbol == (int)'y' || symbol == (int)'Y');
        HANDLE process = 0;
        if (compute_entropy) {
            process = OpenProcess(PROCESS_VM_READ | PROCESS_QUERY_INFORMATION, false, dw_pid);
            if (process == NULL) {
                fprintf(stderr, "Failed opening the process. Error code: %lu\n", GetLastError());
                puts("Entropy won't be computed!");
                compute_entropy = 0;
            }
        }
        entropy_context e_ctx;
        size_t total_size_blocks = 0;
        do {
            HEAPENTRY32 he;
            ZeroMemory(&he, sizeof(HEAPENTRY32));
            he.dwSize = sizeof(HEAPENTRY32);
            if (Heap32First(&he, dw_pid, hl.th32HeapID)) {
                printf("\n---- Heap ID: 0x%x ----\n", hl.th32HeapID);

                ULONG_PTR start_address = he.dwAddress;
                ULONG_PTR end_address = start_address;
                SIZE_T last_block_size = 0;

                uint8_t* ent_buffer = NULL;
                size_t max_block_size = 0;
                if (compute_entropy) {
                    entropy_init(&e_ctx);
                }
                do {
                    if (list_all_blocks) {
                        printf("Start address: 0x%p Block size: 0x%x\n", he.dwAddress, he.dwBlockSize);
                    }

                    if (compute_entropy) {
                        if (max_block_size < he.dwBlockSize) {
                            max_block_size = he.dwBlockSize;
                            uint8_t* buf = (uint8_t*)realloc(ent_buffer, he.dwBlockSize);
                            if (buf) {
                                ent_buffer = buf;
                            } else {
                                fprintf(stderr, "Buffer allocation faied! Error code: %lu\n", GetLastError());
                                CloseHandle(process);
                                CloseHandle(hHeapSnap);
                                return FALSE;
                            }
                        }
                        SIZE_T bytes_read;
                        if (ReadProcessMemory(process, (LPCVOID)he.dwAddress, (LPVOID)ent_buffer, he.dwBlockSize, &bytes_read) && (bytes_read == he.dwBlockSize)) {
                            entropy_calculate_frequencies(&e_ctx, ent_buffer, he.dwBlockSize);
                            total_size_blocks += he.dwBlockSize;
                        } else {
                            printf("Start address: 0x%p Block size: 0x%x\n", he.dwAddress, he.dwBlockSize);
                            fprintf(stderr, "Failed reading process memory. Error code: %lu\n", GetLastError());
                        }
                    }

                    start_address = _min(start_address, he.dwAddress);
                    if (end_address < he.dwAddress) {
                        end_address = he.dwAddress;
                        last_block_size = he.dwBlockSize;
                    }

                    he.dwSize = sizeof(HEAPENTRY32);
                } while (Heap32Next(&he));
                end_address += last_block_size;
                printf("\nStart Address: 0x%p\n", start_address);
                printf("End Address: 0x%p\n", end_address);
                printf("Size: 0x%llx\n", ptrdiff_t(end_address - start_address));
                if (compute_entropy) {
                    const double entropy = entropy_compute(&e_ctx, total_size_blocks);
                    printf("Entropy: %.2F\n", entropy);
                    free(ent_buffer);
                }
            }
            hl.dwSize = sizeof(HEAPLIST32);
        } while (Heap32ListNext(hHeapSnap, &hl));

        if (compute_entropy) {
            CloseHandle(process);
        }
    } else {
        printf("Cannot list first heap (%d)\n", GetLastError());
    }
    CloseHandle(hHeapSnap);

    return 0;
}

static void print_error(TCHAR const* msg) {
    DWORD eNum;
    TCHAR sysMsg[256];
    TCHAR* p;

    eNum = GetLastError();
    FormatMessage(FORMAT_MESSAGE_FROM_SYSTEM | FORMAT_MESSAGE_IGNORE_INSERTS,
        NULL, eNum,
        MAKELANGID(LANG_NEUTRAL, SUBLANG_DEFAULT), // Default language
        sysMsg, 256, NULL);

    // Trim the end of the line and terminate it with a null
    p = sysMsg;
    while ((*p > 31) || (*p == 9))
        ++p;
    do { *p-- = 0; } while ((p >= sysMsg) &&
        ((*p == '.') || (*p < 33)));

    // Display the message
    _tprintf(TEXT("\n  WARNING: %s failed with error %d (%s)"), msg, eNum, sysMsg);
}