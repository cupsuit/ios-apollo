/*
 * Bounded Flattened Device Tree parser.
 *
 * Supports FDT version 17. Every structure/string/property access is
 * checked against totalsize and its corresponding block size.
 */
#include "fdt.h"

#define FDT_MAGIC       0xd00dfeedU
#define FDT_HEADER_SIZE 40U

#define FDT_BEGIN_NODE  1U
#define FDT_END_NODE    2U
#define FDT_PROP        3U
#define FDT_NOP         4U
#define FDT_END         9U

#define FDT_MAX_DEPTH 64U

struct fdt_layout {
uintptr_t base;
uint32_t total;
uint32_t struct_off, struct_size;
uint32_t strings_off, strings_size;
};

static uint32_t read_be32(uintptr_t p)
{
const volatile uint8_t *b = (const volatile uint8_t *)p;

return ((uint32_t)b[0] << 24) |
       ((uint32_t)b[1] << 16) |
       ((uint32_t)b[2] << 8) |
       (uint32_t)b[3];
}

static uint64_t read_be64(uintptr_t p)
{
return ((uint64_t)read_be32(p) << 32) |
       read_be32(p + 4);
}

static int range_ok(uint32_t off, uint32_t len, uint32_t total)
{
return off <= total && len <= total - off;
}

static int ranges_overlap(uint32_t a, uint32_t alen,
  uint32_t b, uint32_t blen)
{
return a < b + blen && b < a + alen;
}

static int layout_init(uintptr_t fdt, struct fdt_layout *l)
{
uint32_t magic, total, off_struct, off_strings, off_rsv;
uint32_t version, last, size_strings, size_struct;
uint32_t p;

if (!fdt || fdt > UINTPTR_MAX - FDT_HEADER_SIZE)
return 0;

magic = read_be32(fdt);
total = read_be32(fdt + 4);

if (magic != FDT_MAGIC || total < FDT_HEADER_SIZE)
return 0;
if (fdt > UINTPTR_MAX - total)
return 0;

off_struct  = read_be32(fdt + 8);
off_strings = read_be32(fdt + 12);
off_rsv     = read_be32(fdt + 16);
version     = read_be32(fdt + 20);
last        = read_be32(fdt + 24);
size_strings = read_be32(fdt + 32);
size_struct  = read_be32(fdt + 36);

/* This parser intentionally supports the complete v17 header. */
if (version != 17 || last > 17 || last < 16)
return 0;

if ((off_struct & 3U) || (off_rsv & 7U))
return 0;

if (!size_struct || !size_strings)
return 0;

if (!range_ok(off_struct, size_struct, total) ||
    !range_ok(off_strings, size_strings, total))
return 0;

if (off_struct < FDT_HEADER_SIZE ||
    off_strings < FDT_HEADER_SIZE ||
    off_rsv < FDT_HEADER_SIZE)
return 0;

if (ranges_overlap(off_struct, size_struct,
   off_strings, size_strings))
return 0;

/*
 * Validate the memory reservation map. It consists of 16-byte
 * address/size entries and a zero/zero terminator. It must end
 * before either structure or strings block.
 */
p = off_rsv;
for (;;) {
uint64_t address, size;

if (!range_ok(p, 16, total))
return 0;

if (ranges_overlap(p, 16, off_struct, size_struct) ||
    ranges_overlap(p, 16, off_strings, size_strings))
return 0;

address = read_be64(fdt + p);
size = read_be64(fdt + p + 8);

p += 16;

if (!address && !size)
break;

/* Reject overflowing reservation ranges. */
if (size && address > UINT64_MAX - size)
return 0;
}

l->base = fdt;
l->total = total;
l->struct_off = off_struct;
l->struct_size = size_struct;
l->strings_off = off_strings;
l->strings_size = size_strings;

return 1;
}

static int bounded_string_equal(uintptr_t p, uint32_t remaining,
const char *wanted)
{
uint32_t i = 0;

if (!remaining || !wanted)
return 0;

while (i < remaining) {
char c = *(const volatile char *)(p + i);

if (c != wanted[i])
return 0;
if (!c)
return 1;
i++;
}

return 0;
}

static int bounded_string_valid(uintptr_t p, uint32_t remaining)
{
    uint32_t i;

    if (!remaining)
        return 0;

    for (i = 0; i < remaining; i++) {
        if (*(const volatile uint8_t *)(p + i) == 0)
            return i != 0;
    }

    return 0;
}

static int find_chosen_property(const struct fdt_layout *l,
const char *wanted, uint64_t *result)
{
uint32_t pos = 0;
unsigned depth = 0;
unsigned tokens = 0;
uint8_t chosen_stack[FDT_MAX_DEPTH] = {0};
uint8_t child_stack[FDT_MAX_DEPTH] = {0};
int root_seen = 0;
int root_closed = 0;
int found = 0;
uint64_t value = 0;

const uint32_t struct_size = l->struct_size;
const uintptr_t structure = l->base + l->struct_off;
const uintptr_t strings = l->base + l->strings_off;

while (pos <= struct_size && struct_size - pos >= 4) {
uint32_t token = read_be32(structure + pos);
pos += 4;

if (++tokens > struct_size / 4 + 1)
return 0;

switch (token) {
case FDT_BEGIN_NODE: {
uint32_t start = pos;
uint32_t remaining = struct_size - pos;
uint32_t name_len = 0;
int is_chosen;

if (root_closed || depth >= FDT_MAX_DEPTH)
return 0;

while (name_len < remaining &&
       *(const volatile char *)(structure + start +
 name_len))
name_len++;

if (name_len == remaining)
return 0;

/* Root node must have an empty name. */
if (!depth) {
if (root_seen || name_len != 0)
return 0;
root_seen = 1;
}

is_chosen = (depth == 1 &&
     bounded_string_equal(structure + start,
  name_len + 1,
  "chosen"));

/*
 * The chosen node is a direct child of root.
 * Properties of its descendants are not accepted.
 */
if (depth)
    child_stack[depth - 1] = 1;
chosen_stack[depth] = (uint8_t)is_chosen;
/* a new node starts with no children (the slot may hold a closed sibling's flag) */
child_stack[depth] = 0;
depth++;

pos = start + name_len + 1;
if (pos > UINT32_MAX - 3)
return 0;
pos = (pos + 3U) & ~3U;

if (pos > struct_size)
return 0;

/* chosen_stack[1] identifies the exact root child /chosen. */
break;
}

case FDT_END_NODE:
if (!depth)
return 0;
depth--;
if (!depth)
root_closed = 1;
break;

case FDT_PROP: {
uint32_t len, nameoff;
uint32_t padded;
uintptr_t val;
int in_chosen;
if (!depth || root_closed ||
    child_stack[depth - 1] ||
    struct_size - pos < 8)
return 0;

len = read_be32(structure + pos);
nameoff = read_be32(structure + pos + 4);
pos += 8;

if (len > struct_size - pos || len > UINT32_MAX - 3U)
return 0;

padded = (len + 3U) & ~3U;
if (padded < len || padded > struct_size - pos)
return 0;

if (nameoff >= l->strings_size ||
    !bounded_string_valid(strings + nameoff,
                          l->strings_size - nameoff))
return 0;

/*
 * A property is in /chosen only at depth 2.
 * The structure walker has already validated the
 * node nesting and all intervening tokens.
 */
in_chosen = (depth == 2 && chosen_stack[1]);

if (in_chosen &&
    bounded_string_equal(strings + nameoff,
 l->strings_size - nameoff,
 wanted)) {
if (found || (len != 4 && len != 8))
return 0;

val = structure + pos;

if (len == 4)
value = read_be32(val);
else
value = read_be64(val);

found = 1;
}

pos += padded;
break;
}
case FDT_NOP:
if (!root_seen || root_closed || !depth)
    return 0;
break;

case FDT_END:
if (!root_seen || !root_closed || depth != 0 ||
    pos != struct_size)
    return 0;

if (found)
*result = value;
return found;

default:
return 0;
}
}

return 0;
}

int fdt_chosen_u64(uintptr_t fdt, const char *prop, uint64_t *out)
{
struct fdt_layout layout;
uint64_t value = 0;

if (!prop || !out)
return 0;

if (!layout_init(fdt, &layout))
return 0;

if (!find_chosen_property(&layout, prop, &value))
return 0;

*out = value;
return 1;
}
