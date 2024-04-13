#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <windows.h>
#include <psapi.h>
#include <tlhelp32.h>
#include <tchar.h>
#include <assert.h>

#define MAX_BUFFER_SIZE 0x1000
#define MAX_PATTERN_LEN 0x40
#define MAX_PID_STR_LEN 16

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
    if (is_hex && (data->pattern_len > (sizeof(uint64_t) * 2 + 2))) {
        printf("Max supported hex value size: %d bytes!\n", (int)sizeof(uint64_t));
        data->type = it_error_type;
        return;
    }

    if (is_hex) {
        data->type = it_hex;
        data->value = value;
        data->pattern = (const char*)&data->value;
        if (*end == 'h' || *end == 'H') {
            data->pattern_len -= 1;
        } else if (pattern[0] == '0' && (pattern[1] == 'x' || pattern[1] == 'X')) {
            data->pattern_len -= 2;
        }
        data->pattern_len /= 2;
        puts("\nSearching for a hex value...\n");
    } else {
        data->type = it_ascii;
        data->pattern = pattern;
        puts("\nSearching for an ascii string...\n");
    }
}

static void find_pattern(HANDLE process, const char* pattern, size_t pattern_len) {
    unsigned char* p = NULL;
    MEMORY_BASIC_INFORMATION info;
    char stack_buffer[MAX_BUFFER_SIZE]; // Assuming a maximum block size of 4096 bytes
    char *heap_buffer = NULL;

    puts("Searching committed memory...\n");
    size_t num_found_total = 0;
    for (p = NULL; VirtualQueryEx(process, p, &info, sizeof(info)) == sizeof(info); p += info.RegionSize) {
        if (info.State == MEM_COMMIT) {
            assert((info.Type == MEM_MAPPED || info.Type == MEM_PRIVATE || info.Type == MEM_IMAGE));
            char* buffer = NULL;
            if (info.RegionSize <= MAX_BUFFER_SIZE) {
                buffer = stack_buffer;
                heap_buffer = NULL;
            } else {
                heap_buffer = (char*)malloc(info.RegionSize);
                buffer = heap_buffer;
            }

            SIZE_T bytes_read;
            ReadProcessMemory(process, p, buffer, info.RegionSize, &bytes_read);

            if (bytes_read >= pattern_len) {
                char module_name[MAX_PATH];
                int m_name_found = 0;
                if (info.Type == MEM_IMAGE) {
                    m_name_found = GetModuleFileNameExA(process, (HMODULE)info.AllocationBase, module_name, MAX_PATH);
                }

                int print_once = 1;
                size_t num_found = 0;
                for (size_t i = 0, sz = bytes_read - pattern_len; i < sz; i++) {
                    if (memcmp(buffer + i, pattern, pattern_len) == 0) {
                        if (print_once) {
                            if (m_name_found) {
                                printf("Module name: %s\n", module_name);
                            }
                            printf("Base addres: 0x%p\tAllocation Base: 0x%p\tRegion Size: 0x%llx\nState: %s\tProtect: %s\t", 
                                info.BaseAddress, info.AllocationBase, info.RegionSize, get_page_protect(info.Protect), get_page_state(info.State));
                            print_page_type(info.Type);
                            print_once = 0;
                        }
                        printf("Match at address: 0x%p\n", p + i);
                        num_found++;
                    }
                }
                if (num_found) {
                puts("");
                num_found_total += num_found;
                }
            }
            free(heap_buffer);
        }
    }
    if (!num_found_total) {
        puts("No matches found.");
    }
}

int main() {
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

            puts("Travers process's heap list? y/n");
            while ((getchar()) != '\n'); // flush stdin
            symbol = getchar();
            if (symbol == (int)'y' || symbol == (int)'Y') {
                traverse_heap_list(pid);
                puts("\n\n====================================\n");
            }
        }

        puts("Input pattern (hex value or ascii string): ");
        res = scanf_s("%s", pattern, (unsigned int)sizeof(pattern));
        if (EOF == res || 0 == res) {
            puts("Error reading pattern!");
            return 1;
        }
        const size_t pattern_len = strlen(pattern);

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

        puts("\n====================================\n");
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
    if (hProcessSnap == INVALID_HANDLE_VALUE)
    {
        print_error(TEXT("CreateToolhelp32Snapshot (of processes)"));
        return(FALSE);
    }

    // Set the size of the structure before using it.
    pe32.dwSize = sizeof(PROCESSENTRY32);

    // Retrieve information about the first process,
    // and exit if unsuccessful
    if (!Process32First(hProcessSnap, &pe32))
    {
        print_error(TEXT("Process32First")); // show cause of failure
        CloseHandle(hProcessSnap);          // clean the snapshot object
        return(FALSE);
    }

    // Now walk the snapshot of processes, and
    // display information about each process in turn
    do
    {
        _tprintf(TEXT("\n\n====================================================="));
        _tprintf(TEXT("\nPROCESS NAME:  %s"), pe32.szExeFile);
        _tprintf(TEXT("\n-------------------------------------------------------"));

        // Retrieve the priority class.
        dwPriorityClass = 0;
        hProcess = OpenProcess(PROCESS_ALL_ACCESS, FALSE, pe32.th32ProcessID);
        if (hProcess == NULL)
            print_error(TEXT("OpenProcess"));
        else
        {
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
    if (hModuleSnap == INVALID_HANDLE_VALUE)
    {
        print_error(TEXT("CreateToolhelp32Snapshot (of modules)"));
        return(FALSE);
    }

    // Set the size of the structure before using it.
    me32.dwSize = sizeof(MODULEENTRY32);

    // Retrieve information about the first module,
    // and exit if unsuccessful
    if (!Module32First(hModuleSnap, &me32))
    {
        print_error(TEXT("Module32First"));  // show cause of failure
        CloseHandle(hModuleSnap);           // clean the snapshot object
        return(FALSE);
    }

    // Now walk the module list of the process,
    // and display information about each module
    do
    {
        _tprintf(TEXT("\n\n     MODULE NAME:     %s"), me32.szModule);
        _tprintf(TEXT("\n     Executable     = %s"), me32.szExePath);
        _tprintf(TEXT("\n     Process ID     = 0x%08X"), me32.th32ProcessID);
        _tprintf(TEXT("\n     Ref count (g)  = 0x%04X"), me32.GlblcntUsage);
        _tprintf(TEXT("\n     Ref count (p)  = 0x%04X"), me32.ProccntUsage);
        _tprintf(TEXT("\n     Base address   = 0x%08X"), (DWORD)me32.modBaseAddr);
        _tprintf(TEXT("\n     Base size      = %d"), me32.modBaseSize);

    } while (Module32Next(hModuleSnap, &me32));

    CloseHandle(hModuleSnap);
    return(TRUE);
}

static int list_process_threads(DWORD dw_owner_pid) {
    HANDLE hThreadSnap = INVALID_HANDLE_VALUE;
    THREADENTRY32 te32;

    // Take a snapshot of all running threads  
    hThreadSnap = CreateToolhelp32Snapshot(TH32CS_SNAPTHREAD, 0);
    if (hThreadSnap == INVALID_HANDLE_VALUE)
        return(FALSE);

    // Fill in the size of the structure before using it. 
    te32.dwSize = sizeof(THREADENTRY32);

    // Retrieve information about the first thread,
    // and exit if unsuccessful
    if (!Thread32First(hThreadSnap, &te32))
    {
        print_error(TEXT("Thread32First")); // show cause of failure
        CloseHandle(hThreadSnap);          // clean the snapshot object
        return(FALSE);
    }

    // Now walk the thread list of the system,
    // and display information about each thread
    // associated with the specified process
    do
    {
        if (te32.th32OwnerProcessID == dw_owner_pid)
        {
            _tprintf(TEXT("\n\n     THREAD ID      = 0x%08X"), te32.th32ThreadID);
            _tprintf(TEXT("\n     Base priority  = %d"), te32.tpBasePri);
            _tprintf(TEXT("\n     Delta priority = %d"), te32.tpDeltaPri);
            _tprintf(TEXT("\n"));
        }
    } while (Thread32Next(hThreadSnap, &te32));

    CloseHandle(hThreadSnap);
    return(TRUE);
}

static int traverse_heap_list(DWORD dw_pid) {
    HEAPLIST32 hl;

    HANDLE hHeapSnap = CreateToolhelp32Snapshot(TH32CS_SNAPHEAPLIST, dw_pid);

    hl.dwSize = sizeof(HEAPLIST32);

    if (hHeapSnap == INVALID_HANDLE_VALUE)
    {
        printf("CreateToolhelp32Snapshot failed (%d)\n", GetLastError());
        return 1;
    }

    if (Heap32ListFirst(hHeapSnap, &hl))
    {
        do
        {
            HEAPENTRY32 he;
            ZeroMemory(&he, sizeof(HEAPENTRY32));
            he.dwSize = sizeof(HEAPENTRY32);

            if (Heap32First(&he, dw_pid, hl.th32HeapID))
            {
                printf("\nHeap ID: %d\n", hl.th32HeapID);
                do
                {
                    printf("Start address: %p Block size: %d\n", he.dwAddress, he.dwBlockSize);

                    he.dwSize = sizeof(HEAPENTRY32);
                } while (Heap32Next(&he));
            }
            hl.dwSize = sizeof(HEAPLIST32);
        } while (Heap32ListNext(hHeapSnap, &hl));
    }
    else printf("Cannot list first heap (%d)\n", GetLastError());

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