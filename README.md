# Simple M_0L_0-esque wam implementation thingy

## abstract machine instructions

### building terms
The abstract machine has two stack ( a heap stack and control stack ). The
abstract machine also has registers (stored in the control stack). Registers
store references to cells. The abstract machine has two modes, READ and WRITE.
WRITE constructs terms, READ matches terms. There are a couple of repeat
instructions, this is because we'll interact with READ and WRITE in different
ways.

For building terms, we just write to the heap. These are instruction that
only build terms, they do not effect `S`. They're rule agnostic.
Building instructions:
- `set_variable [reg: register]`
    pushes a REF cell that references H into H and copies it into `reg`
- `set_value [reg: register]`
    copies `reg` into `H`
- `set_structure [f: functor] [reg: register]`
    sets `reg` to `H`. Constructs the head of a structure and copies it to reg

### unifying terms
For unifying terms, we read from and write to the heap. This is dependent on
mode, and does effect the `S` register. These walk along the written term
written by the building instructions. In READ mode, they function as a way
to load information from the term into registers (failing at mismatch), while
in WRITE mode, they function like the building instructions. This can be
thought of as unifying their register parameter with the contents of the `S`
register. We still have to handle the S register.
Unifying instructions:
- `unify_variable [reg: register]`
    - `READ`: copies the heap cell at `S` into `reg`
    - `WRITE`: behaves like `set_variable $reg`, but increments `S`.
- `unify_value [reg: register]`
    - `READ`: invoke `unify($reg, %S)`, the success of `unify` is the success
              of this instruction.
    - `WRITE`: behaves like `set_structure $reg`, but increments `S`.
- `get_structure [f: functor] [reg: register]`
    If `reg` contains a variable, set the current mode to write mode and
    act like `set_structure $f $reg`, but update `S`. If `reg` is a STR cell,
    check if the functors match (failing if they don't), then update `S`
    respectively.

### related notes
Our C implementation adds a reference to the Environment (currently just the
heap). This is because I don't want to make them global. You can if you decide
to re-implement this. So this README says still applies, it's just I've done it
slightly different.

there is a `bind` procedure for binding two addresses. This assumes that
atleast one of it's arguments is a variable. This is where future updates are
performed on previously existing terms. You can use `bind` to perform occurs
checks if your needs do be. Since this is the only place we update pre-existing
variables, we can use this to store what needs to be undone when popping stuff
off the local stack. Useful.

the `unify` procedure takes two addresses and unifies them, it returns a
boolean value to denote success of unification. The way this is described is
hellish. Look at the bottom for what is written in the paper (items:2).
### notes on compiling

For these to work we need to allocate the registers (map registers to terms)
in a way that let's us flatten our representation. For building terms, we want
a term to built only referencing built term. This is because our instructions
build terms and copy them into registers. So, we decompose the query term
`?- f(a)` into `_1 = a, _0 = f(_1)`. This ensures registers are populated
before they're used.

When accounting for arguments, Cry.

## demo
To match a head, we unify, to run a goal we write and call. This
Here's the following program

```prolog
f(a).
?- f(X).
```

it get's compiled to

```
predicate f/1:
    set_structure a/0 1
    set_structure f/1 0
    set_value 1

query:
    set_variable 1
    set_structure f/1 0
    set_value 1
    call f/1
```


## Items
1) This is based on "Warrens Abstract Machine: A Tutorial Reconstruction"
2)
    This function is taken is `Figure 2.7: The unify operation`. I don't know
    what langauge it's written in, but it's hard to parse. `PDL` is assumed to
    be a stack of addresses. `PDL` is never declared or defined. At this point
    in the paper, the name `HEAP` and `STORE` are used to refer to the same
    structure, but `HEAP` denotes that the indexed cell may be undefined.
    Be warned, the next peice of code is hellish
```math
procedure unify(a₁, a₂ : address);
    push(a₁, PDL); push(a₂, PDL);
    fail <- false;
    while ¬(empty(PDL) ∨ fail) do
        d_1 <- deref(pop(PDL)); d_2 <- deref(pop(PDL));
        if d_1 != d_2 then
            begin
            ⟨t_1, v_1⟩ <- STORE[d₁]; ⟨t_2, v_2⟩ <- STORE[d₂]
            if (t_1 = REF) ∨ (t_2 == REF)
                then bind(d_1, d_2)
                else
                    begin
                        ƒ₁/n₁ <- STORE[v₁]; ƒ₂/n₂ <- STORE[v₂];
                        if (f₁ = f₂) ∧ (n₁ = n₂)
                            then
                                for i <- 1 to n₁ do
                                    begin
                                        push(v₁ + i, PDL);
                                        push(v₂ + i, PDL)
                                    end
                            else fail <- true
                        end
        end
    end
end unify;
```