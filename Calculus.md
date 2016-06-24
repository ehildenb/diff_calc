---
execute: diff_calc.maude
...

Differential Calculus over Rational Numbers
===========================================

We'd like to define differential calculus over rational numbers. This will be
done in both Haskell and Maude. Both languages have their merits.


Data Constructors
-----------------

Whether we are in equational logic (Maude) or functional programming with ADTs
(Haskell), we have to tell the system what our data-constructors are. In simple
terms, data-constructors are the building blocks of whatever mathematical
language we're creating.

For example, given some function `F`, we want to be able to build the cosine of
that function, `cos(F)`. To do this, we'll need a data-constructor which
represents `cos(F)` for some `F`.

In Haskell, we can express this using data-constructors, eg:

```haskell
data Func = Cos Func
          | Sin Func
          | ...
```

Here, we've said, "given some `F` of type `Func`, if you do `Cos F`, it will
also be of type `Func`".

In Maude, we can express this using operators along with the `ctor` attribute
(which tells Maude that it's a data-constructor):

```maude
op cos : Func -> Func [ctor] .
```

This says "given some `F` of sort (sort == type) `Func`, if you do `cos(F)` it
will also be of sort `Func`".

### Haskell

### Maude

An `fmod` defines a chunk of importable code in Maude. Here I'm declaring the
`fmod` which creates all the data-constructors for our rational calculus, I call
it `RAT-FUNCTIONS`.

```maude{exec:diff_calc.maude}
fmod RAT-FUNCTIONS is
    protecting RAT .
    protecting QID * (sort Qid to Var) .
```

It imports (`protects`) the `RAT` module, which gives us access to the sort
`Rat` of rational numbers in Maude.

We have to declare some new sorts:

```maude{exec:diff_calc.maude}
    sorts Const Func .
    subsorts Rat < Const < Func .
    subsort Var < Func .
```

Here I am saying that there are two new sorts that exist, which are `Const` (for
constants), and `Func` (for functions).  I also say that any `Rat` (rational
number, protected from `RAT`) is also a `Const`, and that any `Const` is also a
`Func`.

Here, I make my data-constructors:

```maude{exec:diff_calc.maude}
    --- a few constants
    ops pi e inf : -> Const [ctor] .

    --- ways of building up functions
    op -_  : Func -> Func [ctor ditto] .
    op _-_ : Func Func -> Func [ditto] .
    op _+_ : Func Func -> Func [ctor ditto] .
    op _*_ : Func Func -> Func [ctor ditto] .
    op _/_ : Func Func -> Func [ctor ditto] .
    op _^_ : Func Func -> Func [ctor ditto] .
    ops cos sin ln : Func -> Func [ctor] .

    ---(
    Note: Perhaps, in seeking proof that we have some normal form, it would be
    best to have each operator work at the kind level and use memberships to
    push well-formed terms to the `Func` sort.
    )---
```

I declare a few data-constructors of sort `Const` (just `pi`, `e`, and `inf`).
Remember that all `Const` are automatically also `Func`, so these can be placed
anywhere a `Func` can be placed. Thus the expression `pi + (e ^ e)` is valid.
Also remember that any `Rat` is a `Func`, so the expression\
`pi + (e ^ (3 - (4/3 * ln(1))))` is also valid.

I also am declare some other data-constructors. By saying\
`_+_ : Func Func -> Func`, I am telling Maude that for some `F` and `G` of sort
`Func`, if I do `F + G`, it will also have sort `Func`. The underbars represent
where the arguments are supposed to be placed (so we can have arbitrary
user-defined syntax).

Below, I state some simplification rules. Ideally these would take the formulae
to a normal form. I'm not so sure that they do.

```maude{exec:diff_calc.maude}
    --- these are the variables I'm allowed to use in the `eq`s below
    vars N M P : Rat .
    vars N' M' : Rat .
    vars C D   : Const .
    var X      : Var .
    vars F G H : Func .
    vars F' G' : Func .

    --- various identities over 0 and 1
    eq 0 + F     = F .
    eq F + (- F) = 0 .
    eq - (- F)   = F .

    eq 0 * F  = 0 .
    eq 1 * F  = F .

    eq F / 1  = F .
    ceq 0 / F = 0 if not F == 0 .
    ceq F / F = 1 if not F == 0 .
    ceq (N * F) / (M * G) = (N' * F) / (M' * G)
        if P := gcd(N, M)
        /\ not P == 1
        /\ N' := N / P
        /\ M' := M / P .
    ceq (N * F) / M       = N' * F
        if P := gcd(N, M)
        /\ not P == 1
        /\ N' := N / P
        /\ M' := M / P .
    ceq N / (M * F)       = N' / F
        if P := gcd(N, M)
        /\ not P == 1
        /\ N' := N / P
        /\ M' := M / P .

    eq F ^ 0  = 1 .
    eq F ^ 1  = F .
    eq 1 ^ F  = 1 .
    ceq 0 ^ F = 0 if not F == 0 .

    --- we want a canonical form. It will have division on the outside,
    --- addition inside that, then negation, then multiplications
    eq F / (G / H) = (F * H) / G .
    eq (F / G) / H = F / (G * H) .
    eq F * (G / H) = (F * G) / H .
    eq F + (G / H) = ((F * H) + G) / H .
    eq F * (G + H) = (F * G) + (F * H) .
    eq F * - G     = - (F * G) .
    eq - (F + G)   = (- F) + (- G) .
    eq F / (- G)   = (- F) / G .
    eq F - G       = F + (- G) .

    eq (F ^ G) * (F ^ H) = F ^ (G + H) .
    eq (F ^ G) / (F ^ H) = F ^ (G - H) .
    eq F ^ (- G)         = 1 / (F ^ G) .
    eq (F ^ G) ^ H       = F ^ (G * H) .

    --- definitions of special functions
    eq sin(0)             = 0 .
    eq sin(pi)            = 0 .
    eq sin(pi / 2)        = 1 .
    eq sin(- F)           = - sin(F) .
    eq sin((- F) / G)     = - sin(F / G) .
    ceq sin(N * pi)       = sin((N rem 2) * pi)
        if N >= 2 .
    ceq sin((N * pi) / M) = sin(((N / M) rem 2) * pi)
        if N / M >= 2 .
    ceq sin(N * pi)       = - sin((N - 1) * pi)
        if N > 1 /\ N < 2 .
    ceq sin((N * pi) / M) = - sin(((N / M) - 1) * pi)
        if N / M > 1 /\ N / M < 2 .

    eq cos(0)             = 1 .
    eq cos(pi)            = -1 .
    eq cos(pi / 2)        = 0 .
    eq cos(- F)           = cos(F) .
    eq cos((- F) / G)     = cos(F / G) .
    ceq cos(N * pi)       = cos((N rem 2) * pi)
        if N >= 2 .
    ceq cos((N * pi) / M) = cos(((N / M) rem 2) * pi)
        if N / M >= 2 .
    ceq cos(N * pi)       = cos(- (N - 1) * pi)
        if N > 1 /\ N < 2 .
    ceq cos((N * pi) / M) = cos(((N / M) - 1/2) * pi)
        if N / M > 1 /\ N / M < 2 .

    eq ln(e)     = 1 .
    eq ln(0)     = - inf .
    eq ln(1)     = 0 .
    eq ln(e ^ F) = F .

    op gauss : Var Rat Rat -> Func .
    --------------------------------
    eq gauss(X,N,M) = e ^ (- ((X - N) ^ 2) / (2 * (M ^ 2))) .

endfm
```

Perhaps there are some functions we would like to be defined for us. The
Gaussian would be one example. We can supply just the mean and std-dev and it
should create the Gaussian for us (we also must supply the variable the Gaussian
is over).

Here I declare some simple identities and simplifications over the sort `Func`.
The first block mostly deals with arithmetic identities (mulitplying by `0` is
`0`, for example). The second block has simplifications which will
"canonicalize" our formulas. This makes it easier to work with the resulting
formulas. Maude is an equational logic engine, which means that for every
formula you give it, it will try to apply the equations above anywhere within
that equation that it can. This is nice because it means your formulas will be
automatically fully simplified between every step of computation you do.

Additionally we declare some of the identities associated with our special
functions `sin`, `cos`, and `ln`.

So far, we can build up terms using these data-constructors and do simple
simplifications with them.

```maude{exec:diff_calc.maude}
reduce 3 + 4 .
reduce ln (e ^ 3) .
reduce cos (3 * pi) .
reduce cos (- (3 * (pi / 2))) .
reduce sin ((10 * pi) / 5) .
```


Evaluation
----------

-   `BOOL`: This gives us access to the `if_then_else_fi` used in the definition
    of derivatives of variables
-   `QID`: This gives us access to "quoted identifiers", but instead of calling
    them a `Qid`, I want to call them a `Var`. So I want to have variables in my
    formulas (as you often want when doing calculus), but want to use the
    existing machinary of `Qid` instead of hand-rolling my own.

Our functions wouldn't be much if we couldn't evaluate them.

```maude{exec:diff_calc.maude}
fmod RAT-FUNCTIONS-EVAL is
    protecting BOOL .
    extending RAT-FUNCTIONS .

    sort Subst .

    vars X Y : Var .
    var C    : Const .
    vars F G : Func .
    var S    : Subst .

    op _:=_ : Var Func -> Subst [ctor] .
    op _[_] : Func Subst -> Func [prec 80] .
    ----------------------------------------
    eq X [Y := F]    = if X == Y then F else X fi .
    eq C [S]         = C .
    eq (- F) [S]     = - (F [S]) .
    eq (F + G) [S]   = (F [S]) + (G [S]) .
    eq (F * G) [S]   = (F [S]) * (G [S]) .
    eq (F / G) [S]   = (F [S]) / (G [S]) .
    eq (F ^ G) [S]   = (F [S]) ^ (G [S]) .
    eq sin(F) [S]    = sin(F [S]) .
    eq cos(F) [S]    = cos(F [S]) .
    eq ln(F) [S]     = ln(F [S]) .
endfm

reduce ('x + ('y ^ 3)) ['x := 5] .
reduce ('x + ('y ^ 3)) ['y := 7] .
reduce ('x + ('y ^ 3)) ['y := 7] ['x := 5] .
reduce ln(e ^ 0) .
reduce gauss('x, 3, 5) ['x := 3] .
reduce gauss('x, 3, 5) ['x := 8] .
```

Derivatives
-----------

Now we want to be able to take (symbolic) derivatives of functions. That
would be super cool! How do we do it? By defining the math! Suppose our
function is once again `'x + ('y ^ 3)`, and we want to take the derivative
with respect to `'x`. We would say
`d/d 'x ('x + ('y ^ 3))`

Are all these derivative rules correct?

```maude{exec:diff_calc.maude}
fmod RAT-FUNCTIONS-DERIVATIVES is
    protecting BOOL .
    protecting RAT-FUNCTIONS .

    var N M  : Rat .
    var C    : Const .
    vars X Y : Var .
    vars F G : Func .

    op d/d__ : Var Func -> Func .
    -----------------------------
    eq d/d X C        = 0 .
    eq d/d X Y        = if X == Y then 1 else 0 fi .

    eq d/d X (- F)    = - (d/d X F) .
    eq d/d X (F + G)  = (d/d X F) + (d/d X G) .
    eq d/d X (F * G)  = ((d/d X F) * G) + (F * (d/d X G)) .
    eq d/d X (F / G)  = (((d/d X F) * G) - (F * (d/d X G))) / (G ^ 2) .

    eq d/d X (F ^ N)  = N * (F ^ (N - 1)) * (d/d X F) .
    eq d/d X (e ^ F)  = (e ^ F) * (d/d X F) .
    ceq d/d X (F ^ G) = d/d X (e ^ (G * ln(F)))
        if not (F == e) /\ not (G :: Rat) .

    eq d/d X sin(F)   = cos(F) * (d/d X F) .
    eq d/d X cos(F)   = (- sin(F)) * (d/d X F) .

    eq d/d X ln(F)    = (1 / F) * (d/d X F) .

endfm

reduce d/d 'x ('x + 'y) .
reduce d/d 'x ('x + ('x ^ 3)) .
reduce d/d 'x (d/d 'y (cos ('x + 'y))) .
reduce d/d 'x (e ^ (('x - 'y) ^ 2)) .
reduce d/d 'x (ln ('x ^ 3)) .
reduce d/d 'x (cos('x) ^ sin('x + ('y ^ 3))) .
```

```maude{exec:diff_calc.maude}
fmod CALCULUS is
    protecting RAT-FUNCTIONS-EVAL .
    protecting RAT-FUNCTIONS-DERIVATIVES .
endfm

reduce (d/d 'x (gauss('x, 3, 5))) .
reduce (d/d 'x (gauss('x, 3, 5))) ['x := 3] .
reduce (d/d 'x (gauss('x, 3, 5))) ['x := (3 + 5)] .
```

