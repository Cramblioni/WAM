
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
#define true  (bool)(1)
#define false (bool)(0)

// Different Jargon from actual prolog
//      Atom -> value
//      Term -> Atom | F/N (Term_1 .. Term_N)

typedef uint16_t CellRef;
typedef CellRef FunctorName;

typedef enum __attribute__((__packed__)) {
    CK_REF, //  = 10,
    CK_STR, //  = 15,
    CK_FNCT, // = 20
} CellKind;

typedef struct {
    CellKind kind;
    uint8_t arity;
    CellRef ref;
} Cell;

static Cell cell_new_ref(CellRef ref) {
    return (Cell){CK_REF, 0, ref};
}
static Cell cell_new_str(CellRef ref) {
    return (Cell){CK_STR, 0, ref};
}
static Cell cell_new_functor(FunctorName name, uint8_t arity) {
    return (Cell){CK_FNCT, arity, name};
}

static Cell cell_packref(CellRef a, CellRef b) {
    assert(sizeof(Cell) == 2 * sizeof(CellRef));
    Cell res = { 0 };
    *((CellRef*)&res + 0) = a;
    *((CellRef*)&res + 1) = b;

    return res;
}
static void cell_unpackref(Cell val, CellRef *a, CellRef *b) {
    assert(sizeof(Cell) == 2 * sizeof(CellRef));
    *a = *((CellRef*)&val + 0);
    *b = *((CellRef*)&val + 1);
}

static bool functor_eq(Cell f1, Cell f2) {
    if (f1.kind != CK_FNCT || f2.kind != CK_FNCT) {
        return false;
    }
    if (f1.ref != f2.ref) {
        return false;
    }
    if (f1.arity != f2.arity) {
        return false;
    }
    return true;
}

static void put_cell(Cell cell, FILE *file) {
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
    info("creating new heap of size %d", size);
    size *= 2;
    return (Heap){
        .data = (Cell*)malloc(sizeof(Cell) * size),
        .capacity = size,
        .size = 0
    };
}
static void heap_drop(Heap heap) {
    info("freeing heap");
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
static void heap_push(Heap *heap, Cell value) {
    info("pushing into heap %d/%d", heap -> size, heap -> capacity);
    heap -> data[heap -> size] = value;
    heap -> size += 1;
}
static Cell heap_pop(Heap *heap) {
    return heap -> data[heap -> size--];
}
static bool heap_empty(Heap *heap) {
    return (bool)(heap -> size == 0);
}

typedef struct {
    CellRef ref;
    Cell cell;
} Register;

static Register from_heap(Heap *heap, CellRef ref) {
    return (Register){
        .ref  = ref,
        .cell = heap_get(heap, ref),
    };
}

typedef struct {
    Heap heap;
    Register *regs;
    CellRef S;
    bool write_mode;
} Machine;

static Machine machine_new(CellRef base_size, CellRef nregs) {
    info("Allocating block for %d registers (size %d bytes)",
        nregs, sizeof(Register) * nregs);
    return (Machine) {
        heap_new(base_size),
        (Cell*)malloc(sizeof(Register) * nregs),
        (CellRef)0,
        false,
    };
}
static void machine_drop(Machine machine) {
    info("Dropping heap");
    heap_drop(machine.heap);
    info("freeing machine registers");
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

static bool unify(Heap *heap, CellRef a1, CellRef a2) {
    bool fail = false;
    Heap pdl = heap_new(16);
    heap_push(&pdl, cell_packref(a1, a2));
    while (!(heap_empty(&pdl) || fail)) {
        CellRef d1, d2;
        cell_unpackref(heap_pop(&pdl), &d1, &d2);
        if (d1 == d2) { continue; }
        Cell a = heap_get(heap, d1), b = heap_get(heap, d2);
        if (a.kind == CK_REF || b.kind == CK_REF)
            bind(heap, d1, d2);
        else {
            Cell f1 = heap_get(heap, a.ref), f2 = heap_get(heap, b.ref);
            if (f1.ref != f2.ref || f1.arity != f2.arity) {
                fail = true;
                continue;
            }
            for (CellRef i = 1; i <= f1.arity; i += 1) {
                heap_push(&pdl, cell_packref(a.ref + i, b.ref + 1));
            }
        }
    }
    heap_drop(pdl);
    return (bool)!fail;
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
struct __attribute__((__packed__)) _setstr {
    uint8_t arity; FunctorName name;
} ;
typedef struct {
    InstructionKind kind;
    RegInd reg;
    union {
    struct _setstr setstr;
    };
} Instr;

static bool machine_eval_instr(Machine *machine, Instr *data) {
    info("machine eval step");
    info("\tmachine heap capacity %d", machine -> heap.capacity);
    const CellRef H = machine->heap.size;
    switch (data -> kind) {
        case IS_SET_VAR:
            info("pushing REF cell");
            heap_push(&machine -> heap, cell_new_ref(H));
            info("\tcopying into register");
            machine -> regs[data -> reg] = from_heap(&machine -> heap, H);
            return true;
        break;
        case IS_SET_VAL:
            info("pushing register");
            heap_push(&machine -> heap, machine -> regs[data -> reg].cell);
        break;
        case IS_SET_STR:
            info("push STR cell");
            heap_push(&machine -> heap,
                cell_new_str(machine -> heap.size + 1));
            info("\tpush functor");
            heap_push(&machine -> heap,
                cell_new_functor(data -> setstr.name, data -> setstr.arity));
            info("\tcopying into register");
            machine -> regs[data -> reg] = from_heap(&machine -> heap, H);
            return true;
        break;
        case IS_UNIF_VAR:
            info("unifying variable");
            if (!machine -> write_mode) {
                machine -> regs[data -> reg] = from_heap(&machine -> heap, machine -> S);
                machine -> S += 1;
                return true;
            } else {
                heap_push(&machine -> heap, cell_new_ref(H));
                info("\tcopying into register");
                machine -> regs[data -> reg] = from_heap(&machine -> heap, H);
                return true;
            }
            machine -> S += 1;
            break;
        case IS_UNIF_VAL:
            info("unifying value");
            if (!machine -> write_mode) {
                unify(&machine -> heap, machine -> regs[data -> reg].ref, machine -> S - 1);
                return true;
            } else {
                heap_push(&machine -> heap, machine -> regs[data -> reg].cell);
            }
            machine -> S += 1;
            break;
        case IS_GET_STR:
            const CellRef Sd = deref(&machine -> heap, machine -> regs[data -> reg].ref);
            const Cell Sc = heap_get(&machine -> heap, Sd);
            if (Sc.kind == CK_FNCT) {
                error("Encounter functor data");
                abort();
            }
            if (Sc.kind == CK_REF) {
                heap_push(&machine -> heap, cell_new_str(H + 1));
                heap_push(&machine -> heap, cell_new_functor(data -> setstr.name, data -> setstr.arity));
                bind(&machine -> heap, Sd, H);
                machine -> write_mode = true;

            } else if (data -> setstr.name == Sc.ref || data -> setstr.arity == Sc.arity) {
                machine -> S += 1;
                machine -> write_mode = false;
            } else {
                return false;
            }
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
    // info("term dereferenced from %d to %d", term, term_real);
    // info("printing cell of type %d @ %d \n",
    //    term_value.kind, term_real);

    // fputc('\t', stderr);put_cell(term_value, stderr);
    // fputc('\n', stderr);

    switch (term_value.kind) {
        case CK_REF:
            // info("printing ref");
            assert(term_value.ref == term_real);
            printf("_%d", term_real);
        break;
        case CK_STR:
            // info("printing structure");
            Cell funct = heap_get(heap, term_value.ref);
            fputs(names[funct.ref], stdout);
            if (funct.arity > 0) {
                // info("printing args for functor");
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
    Machine machine = machine_new(8, 4);
    info("\tcreated machine with heap capacity %d", machine.heap.capacity);

    // encoding the term `f(a)` -> `_1 = a, _0 = f(_1)`
    // tis little endian
    Instr cur = {0};
        // cur.kind = IS_SET_STR; cur.reg = 1; cur.setstr = (struct _setstr){0, 1};
        cur.kind = IS_SET_VAR; cur.reg = 1; cur.setstr = (struct _setstr){0};
    machine_eval_instr(&machine, &cur);
        cur.kind = IS_SET_STR; cur.reg = 0; cur.setstr = (struct _setstr){1, 0};
    machine_eval_instr(&machine, &cur);
        cur.kind = IS_SET_VAL; cur.reg = 1;
    machine_eval_instr(&machine, &cur);

    puts("registers:");
    for (int i = 0; i < 2; i += 1) {
        Cell cell = machine.regs[i].cell;
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
    print_term(&machine.heap, names, machine.regs[0].ref);
    puts("");
    puts("creating query");

        cur.kind = IS_GET_STR; cur.reg = 1; cur.setstr = (struct _setstr){0, 1};
    machine_eval_instr(&machine, &cur);
        cur.kind = IS_GET_STR; cur.reg = 0; cur.setstr = (struct _setstr){1, 0};
    machine_eval_instr(&machine, &cur);
        cur.kind = IS_UNIF_VAL; cur.reg = 1;
    machine_eval_instr(&machine, &cur);


    puts("registers:");
    for (int i = 0; i < 2; i += 1) {
        Cell cell = machine.regs[i].cell;
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
    puts("");


    print_term(&machine.heap, names, machine.regs[0].ref);
    puts("");

    info("Dropping Machine");
    machine_drop(machine);

    return 0;
}