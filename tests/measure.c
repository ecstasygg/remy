#define _GNU_SOURCE
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <time.h>
#include <unistd.h>

static uint64_t ticks(void)
{
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now)) {
        perror("clock_gettime");
        exit(1);
    }
    return (uint64_t)now.tv_sec * UINT64_C(1000000000) + now.tv_nsec;
}

int main(int argc, char **argv)
{
    if (argc != 2) return 1;
    FILE *file = fopen(argv[1], "rb");
    if (!file) return 1;
    if (fseek(file, 0, SEEK_END)) {
        fclose(file);
        return 1;
    }
    long size = ftell(file);
    long page = sysconf(_SC_PAGESIZE);
    if (size <= 0 || size > 65536 || page <= 0 || fseek(file, 0, SEEK_SET)) {
        fclose(file);
        return 1;
    }
    size_t offset = ((size_t)size + page - 1) / page * page;
    size_t capacity = offset + page;
    unsigned char *image = mmap(NULL, capacity, PROT_READ | PROT_WRITE,
                               MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (image == MAP_FAILED) {
        fclose(file);
        return 1;
    }
    int failed = fread(image, 1, size, file) != (size_t)size;
    failed |= fclose(file) != 0;
    if (failed) {
        munmap(image, capacity);
        return 1;
    }
    unsigned char bridge[] = {0x53,0x49,0x89,0xf8,0x49,0x89,0xf1,0x48,0xb8,
                             0,0,0,0,0,0,0,0,0xff,0xd0,0x5b,0xc3};
    uint64_t address = (uintptr_t)image;
    memcpy(bridge + 9, &address, sizeof(address));
    memcpy(image + offset, bridge, sizeof(bridge));
    if (mprotect(image, capacity, PROT_READ | PROT_EXEC)) {
        munmap(image, capacity);
        return 1;
    }
    uint64_t (*pixel)(uint64_t, uint64_t, uint64_t) = (void *)(image + offset);
    uint64_t checksum = 0;
    uint64_t begin = ticks();
    for (uint64_t t = 0; t < 64; t++) {
        for (uint64_t y = 0; y < 112; y++) {
            for (uint64_t x = 0; x < 160; x++) {
                checksum += pixel(x, y, 2*t) & 15;
            }
        }
    }
    uint64_t elapsed = ticks() - begin;
    printf("%" PRIu64 " %" PRIu64 "\n", elapsed / 64, checksum);
    return munmap(image, capacity) != 0;
}
