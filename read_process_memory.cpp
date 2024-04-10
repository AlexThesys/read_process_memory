#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <windows.h>
#include <psapi.h>
#include <assert.h>

#define MAX_BUFFER_SIZE 0x1000
#define MAX_PATTERN_LEN 0x40
#define MAX_PID_STR_LEN 16
#define MAX_PATH 256

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

int is_hex(const char *pattern, size_t pattern_len) {
    return (((pattern_len > 2) && (pattern[pattern_len - 1] == 'h' || pattern[pattern_len - 1] == 'H'))
        || ((pattern_len > 3) && (pattern[0] == '0' && pattern[1] == 'x')));
}

const char* get_page_state(DWORD state) {
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

void print_page_type(DWORD state) {
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

const char* get_page_protect(DWORD state) {
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
        printf("Max supported hex value size: %d bytes!\n", sizeof(uint64_t));
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
        puts("Searching for a hex value...\n");
    } else {
        data->type = it_ascii;
        data->pattern = pattern;
        puts("Searching for an ascii string...\n");
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
                for (int i = 0, sz = bytes_read - pattern_len; i < sz; i++) {
                    if (memcmp(buffer + i, pattern, pattern_len) == 0) {
                        if (print_once) {
                            if (m_name_found) {
                                printf("Module name: %s\n", module_name);
                            }
                            printf("Base addres: 0x%p\tAllocation Base: 0x%p\tRegion Size: 0x%x\nState: %s\tProtect: %s\t", 
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
    int pid_len = -1;
    int stop = 'n';
    int res;
    do {
        int use_same_pid = 0;
        if (pid_len != -1) {
            puts("Use same PID? y/n");
            while ((getchar()) != '\n'); // flush stdin
            const int reuse_pid = getchar();
            use_same_pid = (reuse_pid == (int)'y' || reuse_pid == (int)'Y');
        }

        if (!use_same_pid) {
            puts("Input PID: ");
            res = scanf_s("%s", pid_str, sizeof(pid_str));
            if (EOF == res || 0 == res) {
                puts("Error reading PID!");
                return 1;
            }
            pid_len = strlen(pid_str);
        }

        char* end = NULL;
        const uint64_t pid = strtoull(pid_str, &end, is_hex(pid_str, pid_len) ? 16 : 10);
        if (pid_str == end) {
            puts("Invalid PID! Exiting...");
            return 1;
        }

        puts("Input pattern (hex value or ascii string): ");
        res = scanf_s("%s", pattern, sizeof(pattern));
        if (EOF == res || 0 == res) {
            puts("Error reading pattern!");
            return 1;
        }
        const int pattern_len = strlen(pattern);

        search_data data;
        data.pattern_len = (size_t)pattern_len;

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

        puts("\n Continue search? y/n");
        while ((getchar()) != '\n'); // flush stdin
        stop = getchar();
    } while (stop == (int)'y' || stop == (int)'Y');

    return 0;
}
