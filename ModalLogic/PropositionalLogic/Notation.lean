import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import ModalLogic.Notations

open Finset

namespace ModalLogic.PropositionalLogic

abbrev Context (α) [DecidableEq α] := Finset α

namespace Context

open HasConj HasDisj

variable {α : Type u} [DecidableEq α]

variable [HasTop α] [HasBot α] [HasConj α] [HasDisj α]
variable [IsCommutative α conj] [IsAssociative α conj] 
variable [IsCommutative α disj] [IsAssociative α disj] 

def Context.ConjAll (Γ : Context α) := fold (· ⋏ ·) (⊤ : α) id Γ
def Context.DisjAll (Γ : Context α) := fold (· ⋎ ·) (⊥ : α) id Γ

end Context

end ModalLogic.PropositionalLogic