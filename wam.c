
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <assert.h>

#define myass(x) #x
#define fuck(x) myass(x)
#define pos  __FILE__ ":" fuck(__LINE__)

// remove to disable logging
#define LOGGING

#ifdef LOGGING
#define info(msg, ...) fprintf(stderr, "[" pos " INFO] " msg "\n", ##__VA_ARGS__ )
#define error(msg, ...) fprintf(stderr, "\x1b[91m[" pos " ERROR] " msg "\x1b[0m\n", ##__VA_ARGS__ )
#else
#define info(msg, ...) (void)msg
#define error(msg, ...) (void)msg
#endif

typedef uint8_t bool;
#define true ((bool)1)
#define false ((bool)0)

// Different Jargon from actual prolog
//      Atom -> value
//      Term -> Atom | F/N (Term_1 .. Term_N)

typedef uint16_t CellRef;
typedef CellRef FunctorName;

typedef enum __attribute__((__packed__)) {
    CK_REF  = 10,
    CK_STR  = 15,
    CK_FNCT = 20
} CellKind;

typedef struct {
    CellKind kind;
    uint8_t arity;
    CellRef ref;
} Cell;

Cell cell_new_ref(CellRef ref) {
    return (Cell){CK_REF, 0, ref};
}
Cell cell_new_str(CellRef ref) {
    return (Cell){CK_STR, 0, ref};
}
Cell cell_new_functor(FunctorName name, uint8_t arity) {
    return (Cell){CK_FNCT, arity, name};
}

void put_cell(Cell cell, FILE *file) {
    //info("got cell (%d, %d, %d)", cell.kind, cell.arity, cell.ref);
    switch (cell.kind) {
        case CK_STR:
            fprintf(file, "STR %d", cell.ref);
            break;
        case CK_REF:
            fprintf(file, "REF %d", cell.ref);
            break;
        case CK_FNCT:
            fprintf(file, "%d/%d", cell.ref, cell.arity);
            break;
        default:
      //      error("kind missed when putting cell");
    }
}

typedef struct {
    Cell* data;
    CellRef capacity;
    CellRef size;
} Heap;
Heap heap_new(CellRef size) {
    return (Heap){
        (Cell*)malloc(sizeof(Cell) * size),
        size, 0
    };
}
static void heap_drop(Heap heap) {
    free(heap.data);
}
static Cell heap_get(const Heap *heap, CellRef ref) {
    if (ref > heap -> capacity) {
        error( "Out Of Heap read (index %d, size %d)",
            ref, heap -> capacity);
        abort();
    }
    return heap -> data[ref];
}
static void heap_set(Heap *heap, CellRef ref, Cell value) {
    if (ref > heap -> capacity) {
        error("Out Of Heap write (index %d, size %d)",
            ref, heap -> capacity);
        abort();
    }
    heap -> data[ref] = value;
}
static void heap_expand(Heap *heap, CellRef amount) {
    if (heap -> size + amount > heap -> capacity) {
        // resize
    }
    heap -> size += amount;
}
static void heap_push(Heap *heap, Cell value) {
    heap_expand(heap, 1);
    heap -> data[heap -> size - 1] = value;
}

typedef struct {
    Heap heap;
    Cell *regs;
    CellRef H;
    CellRef S;
    bool write_mode;
} Machine;

static Machine machine_new(CellRef base_size, CellRef nregs) {
    return (Machine) {
        heap_new(base_size),
        (Cell*)malloc(sizeof(Cell) * nregs),
        (CellRef)0, (CellRef)0,
        false,
    };
}
static void machine_drop(Machine machine) {
    heap_drop(machine.heap);
    free(machine.regs);
}

static bool is_var(const Heap *heap, CellRef ref) {
    Cell refd = heap_get(heap, ref);
    return (bool)(refd.kind == CK_REF && refd.ref == ref);
}

// notes:
//  -- If the cellref returned is a ref, it's most likely a variable
static CellRef deref(const Heap* heap, CellRef x) {
    Cell xd = heap_get(heap, x); // mut
    while (xd.kind == CK_REF && !is_var(heap, x)) {
        x = xd.ref;
        xd = heap_get(heap, x);
    }
    return x;
}

static bool bind(Heap* heap, CellRef lhs, CellRef rhs) {
    CellRef
        lhs_real = deref(heap, lhs),
        rhs_real = deref(heap, rhs);
    if (is_var(heap, lhs_real)) {
        heap_set(heap, lhs_real, cell_new_ref(rhs_real));
        return true;
    } else if (is_var(heap, rhs_real)) {
        heap_set(heap, rhs_real, cell_new_ref(lhs_real));
        return true;
    }
    return false;
}
typedef uint16_t RegInd;
typedef enum {
    IS_SET_VAR,
    IS_SET_VAL,
    IS_SET_STR,

    IS_GET_STR,
    IS_UNIF_VAR,
    IS_UNIF_VAL,
} InstructionKind;
struct __attribute__((__packed__)) _setvar {RegInd reg;};
struct __attribute__((__packed__)) _setval {RegInd reg;};
struct __attribute__((__packed__)) _setstr {
    uint8_t arity; FunctorName name; RegInd reg;
} ;
typedef struct {
    InstructionKind kind;
    union {
    struct _setvar setvar;
    struct _setval setval;
    struct _setstr setstr;
    };
} Instr;

static bool machine_eval_instr(Machine *machine, Instr *data) {
    const CellRef H = machine->heap.size;
    switch (data -> kind) {
        case IS_SET_VAR:
            info("pushing REF cell");
            heap_push(&machine -> heap, cell_new_ref(H));
            info("\tcopying into register");
            machine -> regs[data -> setval.reg] = heap_get(&machine -> heap, H);
            return true;
        break;
        case IS_SET_VAL:
            info("pushing register");
            heap_push(&machine -> heap, machine -> regs[data -> setval.reg]);
        break;
        case IS_SET_STR:
            info("push STR cell");
            heap_push(&machine -> heap,
                cell_new_str(machine -> heap.size + 1));
            info("\tpush functor");
            heap_push(&machine -> heap,
                cell_new_functor(data -> setstr.name, data -> setstr.arity));
            info("\tcopying into register");
            machine -> regs[data -> setstr.reg] = heap_get(&machine -> heap, H);
            return true;
        break;
        default:
            error("Unrecognised instruction %d", data -> kind);
            abort();
            break;
    }
    return true;
}

void print_term(const Heap *heap, char **names, CellRef term) {
    CellRef term_real = deref(heap, term);
    Cell term_value = heap_get(heap, term_real);
    info("term dereferenced from %d to %d", term, term_real);
    info("printing cell of type %d @ %d \n",
        term_value.kind, term_real);

    fputc('\t', stderr);put_cell(term_value, stderr);fputc('\n', stderr);

    switch (term_value.kind) {
        case CK_REF:
            info("printing ref");
            assert(term_value.ref == term_real);
            printf("_%d", term_real);
        break;
        case CK_STR:
            info("printing structure");
            Cell funct = heap_get(heap, term_value.ref);
            fputs(names[funct.ref], stdout);
            if (funct.arity > 0) {
                info("printing args for functor");
                fputs("(", stdout);
                for (int i = 1; i <= funct.arity; i+=1) {
                    print_term(heap, names, term_value.ref + i);
                    if (i != funct.arity) fputs(", ", stdout);
                }
                fputs(")", stdout);
            }
        break;
        case CK_FNCT:
            error("encountered functor data during cell traversal");
            abort();
            break;
        default:
            error("Unrecognised cell id (%d)", term_value.kind);
            abort();
        break;
    }
}

char *names[] = {
    "f",
    "a"
};
int main(void) {
    Machine machine = machine_new(4, 32);

    // encoding the term `f(a)` -> `_1 = a, _0 = f(_1)`
    // tis little endian
    Instr cur = {0};
    cur.kind = IS_SET_STR ;cur.setstr = (struct _setstr){0, 1, 1};
    machine_eval_instr(&machine, &cur);
    cur.kind = IS_SET_STR; cur.setstr = (struct _setstr){1, 0, 0};
    machine_eval_instr(&machine, &cur);
    cur.kind = IS_SET_VAL; cur.setval = (struct _setval){1};
    machine_eval_instr(&machine, &cur);

    puts("registers:");
    for (int i = 0; i < 2; i += 1) {
        Cell cell = machine.regs[i];
        fputc('\t',stdout);
        put_cell(cell, stdout);
        fputc('\n',stdout);
    }
    puts("heap:");
    for (int i = 0; i < machine.heap.size; i += 1) {
        Cell cell = heap_get(&machine.heap, i);
        printf("\t%d@", i);
        put_cell(cell, stdout);
        fputc('\n', stdout);
    }
    print_term(&machine.heap, names, (CellRef)2);
    puts("");

    machine_drop(machine);

    return 0;
}