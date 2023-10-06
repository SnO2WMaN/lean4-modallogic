import Aesop
import Mathlib.Data.Finset.Basic
import ModalLogic.PropositionalLogic.Notation
import ModalLogic.PropositionalLogic.Axioms

open Finset
open ModalLogic.PropositionalLogic

namespace ModalLogic.PropositionalLogic

variable [DecidableEq α]

abbrev Context (α) := Finset α

structure DeductionSystem (α) extends ProveSystem α where
  Deducts: Context α → α → Prop
  NoContext : (Deducts ∅ φ) ↔ (Proves φ)
  inContext : ∀ {Γ φ}, (φ ∈ Γ) → (Deducts Γ φ)

attribute [simp] DeductionSystem.NoContext
attribute [simp] DeductionSystem.inContext

namespace DeductionSystem

notation Γ " ⊢ᵈ[" D "] " φ => DeductionSystem.Deducts D Γ φ 
notation Γ " ⊬ᵈ[" D "] " φ => ¬(Γ ⊢ᵈ[D] φ)
notation "⊢ᵈ[" D "] " φ => ⊢[toProveSystem D] φ
notation "⊬ᵈ[" D "] " φ => ¬(⊢ᵈ[D] φ)


section Lemmas

variable {D : DeductionSystem α}

instance : Coe (∅ ⊢ᵈ[D] φ) (⊢ᵈ[D] φ) := ⟨D.NoContext.mp⟩
instance : Coe (⊢ᵈ[D] φ) (∅ ⊢ᵈ[D] φ) := ⟨D.NoContext.mpr⟩

lemma weakenContext {Γ Δ φ} : (Γ ⊢ᵈ[D] φ) → ((Γ ∪ Δ) ⊢ᵈ[D] φ) := by sorry

instance : Coe (Γ ⊢ᵈ[D] φ) ((Γ ∪ Δ) ⊢ᵈ[D] φ) := ⟨weakenContext⟩ 
instance : Coe (⊢ᵈ[D] φ) (Γ ⊢ᵈ[D] φ) := ⟨by intro h; have : (∅ ∪ Γ) ⊢ᵈ[D] φ := h; aesop;⟩

@[simp]
lemma trivial_context (φ : α) : {φ} ⊢ᵈ[D] φ := by aesop;

end Lemmas


section Rules

variable (D : DeductionSystem α)
variable [HasImply α] [HasBot α] [HasDisj α] [HasConj α] [HasNeg α]

variable [HasImply α] in
class HasDT extends (DeductionSystem α) where
  DT {φ ψ : α} : (Γ ⊢ᵈ[D] (φ ⇒ ψ)) ↔ ((Γ ∪ {φ}) ⊢ᵈ[D] ψ)
attribute [simp] HasDT.DT

variable [HasDT D] in
@[simp] 
theorem equality : Γ ⊢ᵈ[D] φ ⇒ φ := by simp;

class HasMP extends (DeductionSystem α) where
  MP {φ ψ : α} : (Γ ⊢ᵈ[D] (φ ⇒ ψ)) → (Γ ⊢ᵈ[D] φ) → (Γ ⊢ᵈ[D] ψ)
attribute [simp] HasMP.MP

variable [HasBot α] [HasNeg α] [HasNegDef α] {D} [HasMP D] in
@[simp]
theorem bot : (Γ ⊢ᵈ[D] ~φ) → (Γ ⊢ᵈ[D] φ) → (Γ ⊢ᵈ[D] ⊥) := by
  intro H₁ H₂;
  simp_all;
  exact HasMP.MP H₁ H₂
  

class HasIntroDisj extends (DeductionSystem α) where
  IntroDisjL {φ ψ : α} : (Γ ⊢ᵈ[D] φ) → (Γ ⊢ᵈ[D] (φ ⋎ ψ))
  IntroDisjR {φ ψ : α} : (Γ ⊢ᵈ[D] ψ) → (Γ ⊢ᵈ[D] (φ ⋎ ψ)) 
attribute [simp] HasIntroDisj.IntroDisjL HasIntroDisj.IntroDisjR


class HasIntroConj extends (DeductionSystem α) where
  IntroConj {φ ψ : α} : ((Γ ⊢ᵈ[D] φ) ∧ (Γ ⊢ᵈ[D] ψ)) → (Γ ⊢ᵈ[D] (φ ⋏ ψ))
attribute [simp] HasIntroConj.IntroConj


class HasElimConj extends (DeductionSystem α) where
  ElimConjL {φ ψ : α} : (Γ ⊢ᵈ[D] (φ ⋏ ψ)) → (Γ ⊢ᵈ[D] φ)
  ElimConjR {φ ψ : α} : (Γ ⊢ᵈ[D] (φ ⋏ ψ)) → (Γ ⊢ᵈ[D] ψ)
attribute [simp] HasElimConj.ElimConjL HasElimConj.ElimConjR 


class HasExplode extends (DeductionSystem α) where
  Explode (φ : α) : (Γ ⊢ᵈ[D] ⊥) → (Γ ⊢ᵈ[D] φ)
attribute [simp] HasExplode.Explode

class HasDoubleNegElim extends (DeductionSystem α) where
  DoubleNegElim {φ : α} : (Γ ⊢ᵈ[D] ~~φ) → (Γ ⊢ᵈ[D] φ)
attribute [simp] HasDoubleNegElim.DoubleNegElim

end Rules


section BasicSystem

variable (D : DeductionSystem α)
variable [HasImply α] [HasBot α] [HasDisj α] [HasConj α] [HasNeg α]

class IsMinimal₀ extends (HasDT D), (HasMP D)

class IsMinimal extends (IsMinimal₀ D), (HasIntroDisj D), (HasIntroConj D), (HasElimConj D)
instance [IsMinimal D] : IsMinimal₀ D := inferInstance

class IsIntuitional extends (IsMinimal D), (HasExplode D)
instance [IsIntuitional D] : IsMinimal D := inferInstance

class IsClassical extends (IsMinimal D), (HasDoubleNegElim D)
instance [IsClassical D] : IsMinimal D := inferInstance

end BasicSystem


end DeductionSystem

end ModalLogic.PropositionalLogic