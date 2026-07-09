import Lean

namespace SmtReconstruction

-- Define AST for SMT terms
inductive SmtTerm where
  | const (val : Int)
  | bitvec (val : Nat) (width : Nat)
  | var (name : String)
  | app (fn : String) (args : List SmtTerm)
  deriving Repr, Inhabited, BEq

-- Define proof steps
inductive ProofStep where
  | assume_step (id : Nat) (term : SmtTerm)
  | resolution (id : Nat) (clauses : List Nat)
  | theory_lemma (id : Nat) (theory : String) (term : SmtTerm)
  | rns512_lemma (id : Nat) (term : SmtTerm)
  | bitvec_lemma (id : Nat) (term : SmtTerm)
  deriving Repr, Inhabited

structure ProofLog where
  steps : List ProofStep
  deriving Repr, Inhabited

end SmtReconstruction
