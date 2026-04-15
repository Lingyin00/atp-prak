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
