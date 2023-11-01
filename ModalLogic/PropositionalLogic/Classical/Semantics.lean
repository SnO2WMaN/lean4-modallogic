import ModalLogic.PropositionalLogic.Notation
import ModalLogic.PropositionalLogic.Axioms

open ModalLogic.PropositionalLogic

namespace ModalLogic.PropositionalLogic.Classical

variable {α : Type u}

abbrev Valuation (α) := α → Bool

namespace Valuation

variable (V : Valuation α) (φ ψ : α)

variable [HasBot α] 
@[simp] def bot := (V (⊥ : α)) = false

variable [HasImply α]
@[simp] def imply := (V (φ ⇒ ψ)) = (!(V φ) || (V ψ))

variable [HasNeg α] [DefinedNeg α]

variable [HasTop α] [HasTopDef α]

variable [HasDisj α] [HasDisjDef α]

variable [HasConj α][HasConjDef α] 

variable [HasEquiv α] [DefinedEquiv α]

end Valuation

variable {V : Valuation α} {φ ψ : α}
variable [DecidableEq α]
variable [HasTop α] [HasBot α] [HasNeg α] [HasConj α] [HasDisj α] [HasImply α] [HasEquiv α]

@[simp] def Satisfy (V: Valuation α) (φ : α) := (V φ = true)
scoped [ModalLogic.PropositionalLogic.Classical] notation "⊨[" V "] " φ => Satisfy V φ
scoped [ModalLogic.PropositionalLogic.Classical] notation "⊭[" V "] " φ => ¬(⊨[V] φ)

def Consequence (V) (Γ : Context α) (φ : α) := (∀ γ ∈ Γ, (⊨[V] γ)) → (⊨[V] φ)
scoped [ModalLogic.PropositionalLogic.Classical] notation Γ " ⊨[" V "] " φ => Consequence V Γ φ

end ModalLogic.PropositionalLogic.Classical