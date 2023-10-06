import ModalLogic.PropositionalLogic.DeductionSystem.Notations

open ModalLogic.PropositionalLogic.Axioms
open ModalLogic.PropositionalLogic.DeductionSystem
open IsMinimal₀

open Finset 
attribute [simp] union_comm insert_eq

namespace ModalLogic.PropositionalLogic.DeductionSystem

variable [DecidableEq α] [HasImply α]
variable {D : DeductionSystem α} [IsMinimal₀ D]
 
theorem K (φ ψ) : Γ ⊢ᵈ[D] (Axioms.K φ ψ) := by simp;

@[simp] 
theorem K' {φ ψ} : Γ ⊢ᵈ[D] (Axioms.K φ ψ) := K φ ψ

theorem S (φ ψ ξ) : Γ ⊢ᵈ[D] (Axioms.S φ ψ ξ) := by
  simp only [Axioms.S];
  repeat apply DT.mpr;
  have h₁ : (Γ ∪ {φ ⇒ ψ ⇒ ξ} ∪ {φ ⇒ ψ} ∪ {φ}) ⊢ᵈ[D] φ := by simp;
  have h₂ : (Γ ∪ {φ ⇒ ψ ⇒ ξ} ∪ {φ ⇒ ψ} ∪ {φ}) ⊢ᵈ[D] φ ⇒ ψ := by simp;
  have h₃ : (Γ ∪ {φ ⇒ ψ ⇒ ξ} ∪ {φ ⇒ ψ} ∪ {φ}) ⊢ᵈ[D] φ ⇒ ψ ⇒ ξ := by simp;
  have h₄ := MP h₂ h₁;
  have h₅ := MP h₃ h₁;
  have h₆ := MP h₅ h₄;
  aesop;

@[simp] 
theorem S' {φ ψ ξ} : Γ ⊢ᵈ[D] (Axioms.S φ ψ ξ) := S φ ψ ξ

lemma imply_trans : ((Γ ⊢ᵈ[D] (φ ⇒ ψ)) ∧ (Γ ⊢ᵈ[D] (ψ ⇒ ξ))) → (Γ ⊢ᵈ[D] (φ ⇒ ξ)) := by
  intro H₁;
  repeat apply DT.mpr;
  have H₁l : (Γ ∪ {φ}) ⊢ᵈ[D] φ ⇒ ψ := H₁.left;
  have H₁r : (Γ ∪ {φ}) ⊢ᵈ[D] ψ ⇒ ξ := H₁.right;
  have h₁ : (Γ ∪ {φ}) ⊢ᵈ[D] φ := by simp;
  have h₂ := MP H₁l h₁;
  have h₃ := MP H₁r h₂;
  aesop;

variable [HasBot α] [HasNeg α] [HasNegDef α]

@[simp]
theorem DNI : Γ ⊢ᵈ[D] (Axioms.DNI φ) := by
  simp only [Axioms.DNI, HasNegDef.NegDef];
  repeat apply DT.mpr;
  have h₁ : (Γ ∪ {φ ⇒ ⊥, φ}) ⊢ᵈ[D] φ := by simp;
  have h₂ : (Γ ∪ {φ ⇒ ⊥, φ}) ⊢ᵈ[D] φ ⇒ ⊥ := by simp;
  have h₃ := MP h₂ h₁;
  aesop;

@[simp]
theorem DNIntro : (Γ ⊢ᵈ[D] (φ)) → (Γ ⊢ᵈ[D] (~~φ)) := MP DNI

@[simp]
theorem contrapose₁ : (Γ ⊢ᵈ[D] (φ ⇒ ψ)) → (Γ ⊢ᵈ[D] (~ψ ⇒ ~φ)) := by
  intro H₁;
  simp [HasNegDef.NegDef];
  
  repeat apply DT.mpr;

  have H₁ : (Γ ∪ {ψ ⇒ ⊥} ∪ {φ}) ⊢ᵈ[D] φ ⇒ ψ := H₁;
  have h₁ : (Γ ∪ {ψ ⇒ ⊥} ∪ {φ}) ⊢ᵈ[D] ψ ⇒ ⊥ := by simp;
  have h₂ : (Γ ∪ {ψ ⇒ ⊥} ∪ {φ}) ⊢ᵈ[D] φ := by simp;
  have h₃ := MP H₁ h₂;
  have h₄ := MP h₁ h₃;
  aesop;

lemma CON₁ : Γ ⊢ᵈ[D] (Axioms.Con₁ φ ψ) := by
  repeat apply DT.mpr;
  have h₁ : (Γ ∪ {φ ⇒ ψ, ~ψ}) ⊢ᵈ[D] φ ⇒ ψ := by simp;
  have h₂ : (Γ ∪ {φ ⇒ ψ, ~ψ}) ⊢ᵈ[D] ~ψ := by simp;
  have h₃ := contrapose₁ h₁;
  have h₄ := MP h₃ h₂;
  aesop;

@[simp]
theorem contrapose₂ : (Γ ⊢ᵈ[D] (φ ⇒ ~ψ)) → (Γ ⊢ᵈ[D] (ψ ⇒ ~φ)) := by
  intro H₁;
  
  repeat apply DT.mpr;

  have H₁ : (Γ ∪ {ψ} ∪ {φ}) ⊢ᵈ[D] φ ⇒ ~ψ := H₁;
  have h₁ : (Γ ∪ {ψ} ∪ {φ}) ⊢ᵈ[D] φ := by simp;
  have h₂ : (Γ ∪ {ψ} ∪ {φ}) ⊢ᵈ[D] ψ := by simp;
  have h₃ := MP H₁ h₁;
  have h₄ := bot h₃ h₂;
  aesop;

lemma CON₂ : Γ ⊢ᵈ[D] (Axioms.Con₂ φ ψ) := by
  repeat apply DT.mpr;
  have h₁ : (Γ ∪ {φ ⇒ ~ψ} ∪ {ψ}) ⊢ᵈ[D] φ ⇒ ~ψ := by simp;
  have h₂ : (Γ ∪ {φ ⇒ ~ψ} ∪ {ψ}) ⊢ᵈ[D] ψ := by simp;
  have h₃ := contrapose₂ h₁;
  have _ := MP h₃ h₂;
  aesop;  


end ModalLogic.PropositionalLogic.DeductionSystem