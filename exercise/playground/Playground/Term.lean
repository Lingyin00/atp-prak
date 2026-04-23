/-Representation of a Term-/
inductive Term where
  | var : String → Term
  | func : String → List Term → Term
deriving Repr,BEq

#eval Term.var "x"
#eval Term.func "f" [Term.var "x", Term.var "y"]

/-An operation which returns the free variables in a term-/
def FV : Term → List String
  | Term.var x => [x]
  | Term.func _ args => FVList args
  where
    FVList : List Term → List String
      | [] => []
      | x :: xs => FV x ++ FVList xs
#eval FV (Term.func "f" [Term.var "x", Term.var "y"])

/-A data structure for substitutions. A substitution is a finite map from the free vari-
ables of a term to terms-/
def Substitution := String → Option Term

-- the identity substitution
def empty : Substitution := fun _ => none

-- the substitution [x ↦ t]
def singleton (x : String) (t : Term) : Substitution :=
  fun y => if y == x then some t else none

/-The example of a substitution in the exercise sheet-/
def exampleSub : Substitution
  | "x" => some (Term.func "f" [Term.func "a" [] , Term.func "b" []])
  | "y" => some (Term.func "c" [])
  | "z" => some (Term.var "y")
  | _ => none

/-An operation subst, that takes a term and a substitution and applies the substitution
to the term-/
def subst : Term → Substitution → Term
  | Term.var a, sub =>
    match (sub a) with
      | none => Term.var a
      | some arg => arg
  | Term.func f xs, sub => Term.func f (substList xs sub)
    where
      substList : List Term → Substitution → List Term
        | [], _ => []
        | x :: xs, sub => subst x sub :: (substList xs sub)

#eval subst (Term.func "f" [Term.var "x", Term.var "y"]) exampleSub

/- Apply the substitution to the list of a term pairs, returns a list of term pairs-/
def applyToPairs (σ : Substitution) (args : List (Term × Term)) : List (Term × Term) :=
  args.map (fun (a, b) => (subst a σ, subst b σ))

/- The operation compose, which composites two substitution-/
def compose (σ θ : Substitution) : Substitution :=
  fun x =>
    match θ x with
      | none => σ x
      | some args => some (subst args σ )

#eval subst (Term.func "f" [Term.var "x", Term.var "y"]) (compose exampleSub exampleSub)

-- check if x appears in y
def occurs (x : String) : Term → Bool
  | Term.var y => x == y
  | Term.func _ args => args.attach.any (fun ⟨a, ha⟩ => occurs x a)
  termination_by x => sizeOf x
  decreasing_by
    simp_wf
    have := List.sizeOf_lt_of_mem ha
    omega

namespace MartelliMontanari
/- An operation mgu, that takes two terms t, u and returns their most general unifier:
  a substitution σ, s.t. tσ = uσ and for any other θ with tθ = uθ,
  there is a substitution ρ, s.t. θ = σρ-/

partial def mgu : List (Term × Term) → Option Substitution
  | [] => some (fun _ => none)
  | (s,t) :: rest =>
      match s, t with
        | Term.var x, Term.var y =>
          if x == y then
            mgu rest
          else
            let σ_1 := singleton x (Term.var y) -- a local replacement
            (mgu (applyToPairs σ_1 rest)).map (fun σ => compose σ σ_1)
        | Term.var x, Term.func f args =>
          if occurs x (Term.func f args) then none
          else
            let σ_1 := singleton x (Term.func f args)
            (mgu (applyToPairs σ_1 rest)).map (fun σ => compose σ σ_1)
        | Term.func f args, Term.var y =>
          mgu ((Term.var y, Term.func f args) :: rest)
        | Term.func f xs, Term.func g ys =>
            if f == g && xs.length == ys.length then -- TODO: termination_by??
              mgu (List.zip xs ys ++ rest)
            else
              none
def unify (s t : Term) : Option Substitution :=
  mgu [(s, t)]
end MartelliMontanari


-- test
def v (s : String) : Term := Term.var s
def f (name : String) (args : List Term) : Term := Term.func name args
def a : Term := Term.func "a" []
def b : Term := Term.func "b" []

section
open MartelliMontanari

def verify (s t : Term) : Bool :=
  match unify s t with
  | none   => false
  | some σ => subst s σ == subst t σ

#eval verify (v "x") (v "y")                       -- true
#eval verify (f "p" [v "x", v "y"]) (f "p" [v "y", a])  -- true
#eval (unify (f "p" [v "x", v "y"]) (f "p" [v "y", a])).isSome
#eval (unify (f "p" [v "x", v "y"]) (f "p" [v "y", a])).map
        (fun σ => (σ "x", σ "y"))
#eval verify (f "p" [v "x"]) (f "q" [v "x"])       -- false (unify should fail)
end


namespace Robinson
mutual
partial def mguR : Term → Term → Option Substitution
    | Term.var x, Term.var y =>
        if x == y then some empty
        else some (singleton x (Term.var y))
    | Term.var x, t =>
        if occurs x t then none
        else some (singleton x t)
    | t, Term.var x =>
        if occurs x t then none
        else some (singleton x t)
    | Term.func f xs, Term.func g ys =>
        if f == g && xs.length == ys.length then
          mguList xs ys
        else none

partial def mguList : List Term → List Term → Option Substitution
    | [], [] => some empty
    | x :: xs, y :: ys => do
        let σ₁ ← mguR x y
        let xs' := xs.map (fun t => subst t σ₁)
        let ys' := ys.map (fun t => subst t σ₁)
        let σ₂ ← mguList xs' ys'
        return compose σ₂ σ₁
    | _, _ => none
end
end Robinson

section
open Robinson
def verifyR (s t : Term) : Bool :=
  match Robinson.mguR s t with
  | none   => false
  | some σ => subst s σ == subst t σ

#eval Robinson.mguR (v "x") (v "x") |>.isSome -- true
#eval (Robinson.mguR (v "x") (v "y")).map (fun σ => σ "x")
#eval (Robinson.mguR (v "x") a).map (fun σ => σ "x")
#eval Robinson.mguR (f "p" [v "x"]) (f "p" [v "x", v "y"]) |>.isSome
#eval Robinson.mguR (f "p" [v "x"]) (f "q" [v "x"]) |>.isSome
end
