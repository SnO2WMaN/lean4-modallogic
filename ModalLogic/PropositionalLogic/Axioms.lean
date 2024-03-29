import ModalLogic.Notations

namespace ModalLogic.PropositionalLogic.Axioms

variable {α : Type u} (φ φ₁ φ₂ ψ ξ : α)
variable [HasBot α] [HasImply α] [HasNeg α] [HasDisj α] [HasConj α]

@[simp] def ID := φ ⇒ φ

@[simp] def K := (φ ⇒ (ψ ⇒ φ))
@[simp] def S := (φ ⇒ (ψ ⇒ ξ)) ⇒ ((φ ⇒ ψ) ⇒ (φ ⇒ ξ))

@[simp] def Con₁ := ((φ ⇒ ψ) ⇒ (~ψ ⇒ ~φ))
@[simp] def Con₂ := ((φ ⇒ ~ψ) ⇒ (ψ ⇒ ~φ))
@[simp] def Con₃ := ((~φ ⇒ ψ) ⇒ (~ψ ⇒ φ))
@[simp] def Con₄ := ((~φ ⇒ ~ψ) ⇒ (ψ ⇒ φ))

@[simp] def EFQ : α := ⊥ ⇒ φ 
@[simp] def DNI : α := φ ⇒ ~~φ
@[simp] def DNE : α := ~~φ ⇒ φ

/-- Consequentia mirabilis -/
@[simp] def CM : α := (φ ⇒ ~φ) ⇒ ~φ

/-- Strong Consequentia mirabilis -/
@[simp] def CMn : α := (~φ ⇒ φ) ⇒ φ

/-- Reductio Ad Absurdum -/
@[simp] def RAA : α := (φ ⇒ ⊥) ⇒ ~φ

/-- Strong Reductio Ad Absurdum -/
@[simp] def RAAn : α := (~φ ⇒ ⊥) ⇒ φ 

@[simp] def ConjIntro := (φ ⇒ ψ ⇒ (φ ⋏ ψ))

@[simp] def ConjElim₁ := ((φ₁ ⋏ φ₂) ⇒ φ₁)
@[simp] def ConjElim₂ := ((φ₁ ⋏ φ₂) ⇒ φ₂)

@[simp] def DisjIntro₁ := (φ₁ ⇒ (φ₁ ⋎ φ₂))
@[simp] def DisjIntro₂ := (φ₂ ⇒ (φ₁ ⋎ φ₂))

@[simp] def LEM (φ : α) := φ ⋎ ~φ
@[simp] def WeakLEM (φ : α) := ~φ ⋎ ~~φ
@[simp] def NonContradiction := ~(φ ⋏ ~φ)

end ModalLogic.PropositionalLogic.Axioms 