import ModalLogic.SupplymentSimp
import ModalLogic.PropositionalLogic.Notation
import ModalLogic.PropositionalLogic.Axioms

open ModalLogic.PropositionalLogic

namespace ModalLogic.PropositionalLogic

structure DeductionSystem (α : Type u) [DecidableEq α] where
  Deducts: Context α → α → Prop

namespace DeductionSystem

variable {α : Type u} [DecidableEq α]

notation Γ " ⊢ᵈ[" D "] " φ => DeductionSystem.Deducts D Γ φ 
notation Γ " ⊬ᵈ[" D "] " φ => ¬(Γ ⊢ᵈ[D] φ)
notation "⊢ᵈ[" D "] " φ => ∅ ⊢ᵈ[D] φ
notation "⊬ᵈ[" D "] " φ => ¬(⊢ᵈ[D] φ)

section Rules

variable (D : DeductionSystem α)
variable [HasImply α] [HasBot α] [HasDisj α] [HasConj α] [HasNeg α]

class HasInit extends (DeductionSystem α) where
  Init {Γ φ} : (φ ∈ Γ) → (Γ ⊢ᵈ[D] φ)
attribute [simp] HasInit.Init

class HasWeakenContext extends (DeductionSystem α) where
  WeakenContext {Γ Δ φ} : (Γ ⊢ᵈ[D] φ) → ((Γ ∪ Δ) ⊢ᵈ[D] φ)
attribute [simp] HasWeakenContext.WeakenContext

class HasIntroImply extends (DeductionSystem α) where
  IntroImply {φ ψ : α} : ((Γ ∪ {φ}) ⊢ᵈ[D] ψ) → (Γ ⊢ᵈ[D] φ ⇒ ψ)
attribute [simp] HasIntroImply.IntroImply
attribute [aesop unsafe 50% apply] HasIntroImply.IntroImply

class HasElimImply extends (DeductionSystem α) where
  ElimImply {φ ψ : α} : ((Γ₁ ⊢ᵈ[D] φ ⇒ ψ) ∧ (Γ₂ ⊢ᵈ[D] φ)) → ((Γ₁ ∪ Γ₂) ⊢ᵈ[D] ψ)
attribute [simp] HasElimImply.ElimImply

class HasIntroDisj extends (DeductionSystem α) where
  IntroDisjL {φ ψ : α} : (Γ ⊢ᵈ[D] φ) → (Γ ⊢ᵈ[D] (φ ⋎ ψ))
  IntroDisjR {φ ψ : α} : (Γ ⊢ᵈ[D] ψ) → (Γ ⊢ᵈ[D] (φ ⋎ ψ)) 
attribute [simp] HasIntroDisj.IntroDisjL HasIntroDisj.IntroDisjR

class HasElimDisj extends (DeductionSystem α) where
  ElimDisj {φ ψ ξ : α} : ((Γ₁ ⊢ᵈ[D] φ ⋎ ψ) ∧ (Γ₂ ⊢ᵈ[D] φ ⇒ ξ) ∧ (Γ₃ ⊢ᵈ[D] ψ ⇒ ξ)) → ((Γ₁ ∪ Γ₂ ∪ Γ₃) ⊢ᵈ[D] ξ)
attribute [simp] HasElimDisj.ElimDisj

class HasIntroConj extends (DeductionSystem α) where
  IntroConj {φ ψ : α} : ((Γ₁ ⊢ᵈ[D] φ) ∧ (Γ₂ ⊢ᵈ[D] ψ)) → ((Γ₁ ∪ Γ₂) ⊢ᵈ[D] (φ ⋏ ψ))
attribute [simp] HasElimDisj.ElimDisj

class HasElimConj extends (DeductionSystem α) where
  ElimConjL {φ ψ : α} : (Γ ⊢ᵈ[D] (φ ⋏ ψ)) → (Γ ⊢ᵈ[D] φ)
  ElimConjR {φ ψ : α} : (Γ ⊢ᵈ[D] (φ ⋏ ψ)) → (Γ ⊢ᵈ[D] ψ)
attribute [simp] HasElimConj.ElimConjL HasElimConj.ElimConjR

class HasExplode extends (DeductionSystem α) where
  Explode (φ : α) : (Γ ⊢ᵈ[D] ⊥) → (Γ ⊢ᵈ[D] φ)
attribute [simp] HasExplode.Explode
attribute [aesop unsafe 50% apply] HasExplode.Explode

class HasElimDN extends (DeductionSystem α) where
  ElimDN {φ : α} : (Γ ⊢ᵈ[D] ~~φ) → (Γ ⊢ᵈ[D] φ)
attribute [simp] HasElimDN.ElimDN
attribute [aesop unsafe 50% apply] HasElimDN.ElimDN

end Rules

section Lemmas


variable [HasImply α] [HasBot α] [HasNeg α] [DefinedNeg α]
variable {D : DeductionSystem α} 

@[simp] lemma Trivial [HasInit D] (φ : α) : {φ} ⊢ᵈ[D] φ := by aesop;

@[simp] lemma Id [HasInit D] [HasIntroImply D] : Γ ⊢ᵈ[D] (Axioms.ID φ) := by simp;

@[simp]
lemma IntroNeg [HasIntroImply D] : ((Γ ∪ {φ}) ⊢ᵈ[D] ⊥) → (Γ ⊢ᵈ[D] ~φ) := by aesop;

@[simp]
lemma ElimNeg [HasElimImply D] : ((Γ₁ ⊢ᵈ[D] ~φ) ∧ (Γ₂ ⊢ᵈ[D] φ)) → ((Γ₁ ∪ Γ₂) ⊢ᵈ[D] ⊥) := by
  intro H₁;
  simp_all;
  exact HasElimImply.ElimImply H₁;

@[simp]
lemma ElimNeg' [HasElimImply D] : ((Γ ⊢ᵈ[D] ~φ) ∧ (Γ ⊢ᵈ[D] φ)) → (Γ ⊢ᵈ[D] ⊥) := by 
  intro H;
  have := ElimNeg H;
  aesop;

variable [HasWeakenContext D] {Δ : Context α} 

instance : Coe (Γ ⊢ᵈ[D] φ) ((Γ ∪ Δ) ⊢ᵈ[D] φ) := ⟨HasWeakenContext.WeakenContext⟩ 
instance : Coe (⊢ᵈ[D] φ) (Γ ⊢ᵈ[D] φ) := ⟨by intro h; have : (∅ ∪ Γ) ⊢ᵈ[D] φ := h; aesop;⟩

variable [HasElimImply D] in
@[simp] lemma HasElimImply.ElimImply' {φ ψ : α} : ((Γ ⊢ᵈ[D] φ ⇒ ψ) ∧ (Γ ⊢ᵈ[D] φ)) → (Γ ⊢ᵈ[D] ψ) := by
  intro H;
  have := HasElimImply.ElimImply H;
  aesop;

variable [HasConj α] [HasIntroConj D] in
@[simp] lemma HasIntroConj.IntroConj' {φ ψ : α} : ((Γ ⊢ᵈ[D] φ) ∧ (Γ ⊢ᵈ[D] ψ)) → (Γ ⊢ᵈ[D] (φ ⋏ ψ)) := by
  intro H;
  have := HasIntroConj.IntroConj H;
  aesop;

end Lemmas

section BasicSystem

variable (D : DeductionSystem α)
variable [HasImply α] [HasBot α] [HasDisj α] [HasConj α] [HasNeg α]

class IsMinimal₀ extends (HasInit D), (HasIntroImply D), (HasElimImply D), (HasWeakenContext D)

class IsMinimal extends (IsMinimal₀ D), (HasIntroDisj D), (HasIntroConj D), (HasElimConj D)
instance [IsMinimal D] : IsMinimal₀ D := inferInstance

class IsIntuitional extends (IsMinimal D), (HasExplode D)
instance [IsIntuitional D] : IsMinimal D := inferInstance

class IsClassical extends (IsMinimal D), (HasElimDN D)
instance [IsClassical D] : IsMinimal D := inferInstance
instance [DefinedNeg α] [IsClassical D] : IsIntuitional D := by constructor; aesop;

end BasicSystem


end DeductionSystem

end ModalLogic.PropositionalLogic