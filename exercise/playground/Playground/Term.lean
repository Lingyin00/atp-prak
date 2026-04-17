/-Representation of a Term-/
inductive Term where
  | var : String → Term
  | func : String → List Term → Term
deriving Repr

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

/- The operation compose, which composites two substitution-/
def compose (σ θ : Substitution) : Substitution :=
  fun x =>
    match σ x with
      | none => θ x
      | some args => some (subst args θ)

#eval subst (Term.func "f" [Term.var "x", Term.var "y"]) (compose exampleSub exampleSub)

/- An operation mgu, that takes two terms t, u and returns their most general unifier:
  a substitution σ, s.t. tσ = uσ and for any other θ with tθ = uθ,
  there is a substitution ρ, s.t. θ = σρ-/

-- using pattern matching to implement the Rule-Based Naive Standard Unification
partial def mgu : List (Term × Term) → Option Substitution
  | [] => some (fun _ => none)
  | (s,t) :: rest =>
      match s, t with
        | Term.var x, Term.var y =>
          if x == y then
            none
          else
            sorry
        | Term.var x, Term.func f args => sorry
        | Term.func f args, Term.var y => sorry
        | Term.func f xs, Term.func g ys =>
            if f == g then -- TODO: termination_by??
              mgu (List.zip xs ys ++ rest)
            else
              none
