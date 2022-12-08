# A dependently typed lambda calculus

Based on the paper
_A tutorial implementation of a dependently typed lambda calculus_, by
Andres Löh, Conor McBride and Wouter Swierstra.

### Example REPL session

You can start a REPL session with `cabal run` and then input expression in the
language. The REPL supports `let`, to define new terms, and `assume` to define
the type of free variables.

```
$> let plus = natElim (λ _ → Nat → Nat) (λn → n) (λk rec n → Succ (rec n))
plus :: (∀ (x :: Nat). (∀ (y :: Nat). Nat))

$> let append = (λα → vecElim α (λm _ → ∀(n :: Nat).Vec α n → Vec α (plus m n)) (λ _ v → v) (λm v vs rec n w → Cons α (plus m n) v (rec n w))) :: ∀(α :: ∗) (m :: Nat) (v :: Vec α m) (n :: Nat) (w :: Vec α n). Vec α (plus m n)
append :: (∀ (x :: *). (∀ (y :: Nat). (∀ (z :: (Vec (y) (z))). (∀ (u :: Nat). (∀ (v :: (Vec (y) (v))). (Vec (x) (((natElim (λw → (∀ (r :: Nat). Nat)) (λw → w) (λw → λr → λs → Succ ((w r))) (x)) z))))))))

$> assume (α :: ∗) (x :: α) (y :: α)
Assumed: α, x, y

$> append α 2 (Cons α 1 x (Cons α 0 x (Nil α))) 1 (Cons α 0 y (Nil α))
(Cons (α) (Succ (Succ (Zero))) (x) ((Cons (α) (Succ (Zero)) (x) ((Cons (α) (Zero) (y) ((Nil α))))))) :: (Vec (α) (Succ (Succ (Succ (Zero)))))

