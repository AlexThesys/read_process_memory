#include <stdio.h>
#include <windows.h>
#include <string.h>
#include <stdint.h>

#define MAX_BUFFER_SIZE 0x1000
#define MAX_PATTERN_LEN 0x40

enum input_type {
    it_hex,
    it_ascii,
    it_error_type,
};

struct search_data {
    input_type type;
    int64_t value;
};

static const char* page_state[] = {"MEM_COMMIT", "MEM_FREE", "MEM_RESERVE"};
static const char* page_type[] = {"MEM_IMAGE", "MEM_MAPPED", "MEM_PRIVATE"};
static const char* page_protect[] = {"PAGE_EXECUTE", "PAGE_EXECUTE_READ", "PAGE_EXECUTE_READWRITE", "PAGE_EXECUTE_WRITECOPY", "PAGE_NOACCESS", "PAGE_READONLY", 
                                    "PAGE_READWRITE", "PAGE_WRITECOPY", "PAGE_TARGETS_INVALID", "UNKNOWN"};

const char* get_page_state(DWORD state) {
    const char *result = NULL;
    switch (state) {
    case 0x1000 :
        result = page_state[0];
        break;
    case 0x10000:
        result = page_state[1];
        break;
    case 0x2000:
        result = page_state[2];
        break;
    }
    return result;
}

const char* get_page_type(DWORD state) {
    const char* result = NULL;
    switch (state) {
    case 0x1000000:
        result = page_type[0];
        break;
    case 0x40000:
        result = page_type[1];
        break;
    case 0x20000:
        result = page_type[2];
        break;
    }
    return result;
}

const char* get_page_protect(DWORD state) {
    // lets not comlicate things with other available options for now
    state &= ~(0x100 | 0x200 | 0x400);

    const char* result;
    switch (state) {
    case 0x10:
        result = page_protect[0];
        break;
    case 0x20:
        result = page_protect[1];
        break;
    case 0x40:
        result = page_protect[2];
        break;
    case 0x80:
        result = page_protect[3];
        break;
    case 0x01:
        result = page_protect[4];
        break;
    case 0x02:
        result = page_protect[5];
        break;
    case 0x04:
        result = page_protect[6];
        break;
    case 0x08:
        result = page_protect[7];
        break;
    case 0x40000000:
        result = page_protect[8];
        break;
    default:
        result = page_protect[9];
        break;
    }
    return result;
}
 
static void parse_input(const char* pattern, search_data *data) {
    if (strlen(pattern) > MAX_PATTERN_LEN) {
        fprintf(stderr, "Pattern exceeded maximum size of %d. Exiting...", MAX_PATTERN_LEN);
        data->type = it_error_type;
        return;
    }

    const size_t len = strlen(pattern);
    if (((len > 2) && (pattern[len - 1] == 'h' || pattern[len - 1] == 'H'))
        || ((len > 3) && (pattern[0] == '0' && pattern[1] == 'x'))) {
        if (len > (sizeof(int64_t) * 2 + 2)) {
            puts("Maximus supported search size is QWORD");
            data->type = it_error_type;
        }
        else {
            char* end;
            const int64_t value = strtoll(pattern, &end, 0x10);
            if (pattern != end) {
                data->type = it_hex;
                data->value = value;
            } else {
                puts("Invalid hex value provided");
                data->type = it_error_type;
            }
        }
    } else {
        data->type = it_ascii;
    }
}

static void find_pattern(HANDLE process, const char* pattern) {
    unsigned char* p = NULL;
    MEMORY_BASIC_INFORMATION info;
    char stack_buffer[MAX_BUFFER_SIZE]; // Assuming a maximum block size of 4096 bytes
    const int pattern_len = strlen(pattern);
    char *heap_buffer = NULL;

    puts("Searching committed memory...");

    for (p = NULL; VirtualQueryEx(process, p, &info, sizeof(info)) == sizeof(info); p += info.RegionSize) {
        if (info.State == MEM_COMMIT && (info.Type == MEM_MAPPED || info.Type == MEM_PRIVATE || info.Type == MEM_IMAGE)) {
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

            int print_once = 1;
            if (bytes_read >= pattern_len) {
                for (int i = 0; i < bytes_read - pattern_len; i++) {
                    if (memcmp(buffer + i, pattern, pattern_len) == 0) {
                        if (print_once) {
                            printf("Base addres: 0x%p\tAllocation Base: 0x%p\tRegion Size: 0x%x\nState: %s\tProtect: %s\tType: %s\n", 
                                info.BaseAddress, info.AllocationBase, info.RegionSize, get_page_protect(info.Protect), get_page_state(info.State), get_page_type(info.Type));
                            print_once = 0;
                        }
                        printf("Match at address: 0x%p\n", p + i);
                    }
                }
            }
            free(heap_buffer);
        }
    }
}

int main(int argc, char** argv) {
    if (argc != 3) {
        fprintf(stderr, "Insufficient number of arguments!\n Usage: %s <PID> <pattern> in either hex or ascii\n", argv[0]);
        return 1;
    }

    int pid;
    sscanf_s(argv[1], "%i", &pid);
    const char* pattern = argv[2];

    search_data data;
    parse_input(pattern, &data);
    if (data.type != it_error_type) {
        if (data.type == it_hex) {
            pattern = (const char*)&data.value;
        } // else --> it already points to the right thing
    } else {
        return 1;
    }

    HANDLE process = OpenProcess(PROCESS_VM_READ | PROCESS_QUERY_INFORMATION, false, pid);
    if (process == NULL) {
        fprintf(stderr, "Failed opening the process. Error code: %lu\n", GetLastError());
        return 1;
    }

    find_pattern(process, pattern);

    CloseHandle(process);
    return 0;
}
