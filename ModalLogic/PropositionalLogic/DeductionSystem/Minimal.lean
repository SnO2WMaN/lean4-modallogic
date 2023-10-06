import ModalLogic.PropositionalLogic.DeductionSystem.Notations
import ModalLogic.PropositionalLogic.DeductionSystem.Minimal0

open ModalLogic.PropositionalLogic.Axioms
open ModalLogic.PropositionalLogic.DeductionSystem
open IsMinimal HasDT HasElimImply

namespace ModalLogic.PropositionalLogic.DeductionSystem

variable [DecidableEq α] [HasImply α] [HasDisj α] [HasConj α]
variable {D : DeductionSystem α} [IsMinimal D]

theorem conj_decomp : (Γ ⊢ᵈ[D] (φ ⋏ ψ)) → ((Γ ⊢ᵈ[D] φ) ∧ (Γ ⊢ᵈ[D] ψ)):= by
  intro H;
  constructor;
  exact ElimConjL H;
  exact ElimConjR H;

@[simp]
theorem conj_comm : (Γ ⊢ᵈ[D] (φ ⋏ ψ)) → (Γ ⊢ᵈ[D] (ψ ⋏ φ)) := by
  intro H;
  have h₁ := conj_decomp H;
  exact IntroConj ⟨h₁.right, h₁.left⟩;

theorem conj_weakening : (Γ ⊢ᵈ[D] φ) → (Γ ⊢ᵈ[D] φ ⋏ φ) := λ H => IntroConj ⟨H, H⟩

@[simp]
theorem conj_contract: (Γ ⊢ᵈ[D] φ ⋏ φ) → (Γ ⊢ᵈ[D] φ) := ElimConjL

lemma conj_dilemma_elim_left : ((Γ ⊢ᵈ[D] (φ ⋏ ψ) ⇒ ρ) ∧ (Γ ⊢ᵈ[D] φ ⇒ ψ)) → (Γ ⊢ᵈ[D] φ ⇒ ρ) := by
  intro H;
  have Hl : (Γ ∪ {φ}) ⊢ᵈ[D] φ ⋏ ψ ⇒ ρ := H.left;
  have Hr : (Γ ∪ {φ}) ⊢ᵈ[D] φ ⇒ ψ:= H.right;
  have h₁ : (Γ ∪ {φ}) ⊢ᵈ[D] φ := by simp;
  have h₂ : (Γ ∪ {φ}) ⊢ᵈ[D] ψ := ElimImply ⟨Hr, h₁⟩;
  have h₃ := IntroConj ⟨h₁, h₂⟩;
  have h₄ := ElimImply ⟨Hl, h₃⟩;
  aesop;

lemma conj_dilemma_elim_right : ((Γ ⊢ᵈ[D] (φ ⋏ ψ) ⇒ ρ) ∧ (Γ ⊢ᵈ[D] ψ ⇒ φ)) → (Γ ⊢ᵈ[D] ψ ⇒ ρ) := by
  intro H;
  have Hl : (Γ ∪ {ψ}) ⊢ᵈ[D] φ ⋏ ψ ⇒ ρ := H.left;
  have Hr : (Γ ∪ {ψ}) ⊢ᵈ[D] ψ ⇒ φ := H.right;
  have h₁ : (Γ ∪ {ψ}) ⊢ᵈ[D] ψ := by simp;
  have h₂ : (Γ ∪ {ψ}) ⊢ᵈ[D] φ := ElimImply ⟨Hr, h₁⟩;
  have h₃ := IntroConj ⟨h₂, h₁⟩;
  have h₄ := ElimImply ⟨Hl, h₃⟩;
  aesop;

variable [HasBot α] [HasNeg α] [HasNegDef α]

open HasNegDef
attribute [simp] NegDef

lemma NonContradiction {φ} : (Γ ⊢ᵈ[D] (Axioms.NonContradiction φ)) := by
  simp only [Axioms.NonContradiction, NegDef];
  have h₁ : (Γ ∪ {φ ⋏ (φ ⇒ ⊥)}) ⊢ᵈ[D] φ ⋏ (φ ⇒ ⊥) := by simp;
  have h₁l := ElimConjL h₁;
  have h₁r := ElimConjR h₁;
  have h₂ := ElimImply ⟨h₁r, h₁l⟩;
  aesop;

variable [HasEquiv α] [HasEquivDef α]

open HasEquivDef
attribute [simp] EquivDef IntroConj

@[simp]
lemma equiv_intro : ((Γ ⊢ᵈ[D] (φ ⇒ ψ)) ∧ (Γ ⊢ᵈ[D] (ψ ⇒ φ))) → (Γ ⊢ᵈ[D] (φ ⇔ ψ)) := by
  intro H;
  simp [EquivDef];
  exact IntroConj H;

@[simp]
lemma equiv_comm : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] (ψ ⇔ φ)) := by aesop;

@[simp]
lemma equiv_mp : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] φ ⇒ ψ) := by
  intro H;
  simp [EquivDef] at H;
  exact ElimConjL H;

@[simp]
lemma equiv_mpr : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] ψ ⇒ φ) := λ H => equiv_mp $ equiv_comm H

@[simp]
lemma equiv_neg : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] ((~φ : α) ⇔ ~ψ)) := by 
  intro h;
  apply equiv_intro;
  exact ⟨contrapose₁ $ equiv_mpr h, contrapose₁ $ equiv_mp h⟩;

lemma equiv_pick_left : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] φ) → (Γ ⊢ᵈ[D] ψ) := by
  intro H₁ H₂;
  exact ElimImply ⟨equiv_mp H₁, H₂⟩;

lemma equiv_pick_right : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] ψ) → (Γ ⊢ᵈ[D] φ) := λ H => equiv_pick_left $ equiv_comm H

lemma equiv_pick_neg_left : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] (~φ)) → (Γ ⊢ᵈ[D] (~ψ)) := by
  intro H₁ H₂;
  exact ElimImply ⟨equiv_mp $ equiv_neg H₁, H₂⟩;
  
lemma equiv_pick_neg_right : (Γ ⊢ᵈ[D] φ ⇔ ψ) → (Γ ⊢ᵈ[D] ~ψ) → (Γ ⊢ᵈ[D] (~φ)) := λ H => equiv_pick_neg_left $ equiv_comm H

lemma equiv_trans : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] (ψ ⇔ ρ)) → (Γ ⊢ᵈ[D] (φ ⇔ ρ)) := by
  intro H₁ H₂;
  apply equiv_intro;
  apply And.intro;
  . have H₁ := equiv_mp H₁;
    have H₂ := equiv_mp H₂;
    exact imply_trans ⟨H₁, H₂⟩;    
  . have H₁ := equiv_mpr H₁;
    have H₂ := equiv_mpr H₂;
    exact imply_trans ⟨H₂, H₁⟩;

lemma equiv_decomp : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → ((Γ ⊢ᵈ[D] φ) ↔ (Γ ⊢ᵈ[D] ψ)) := by
  intro H;
  exact ⟨λ h => ElimImply ⟨equiv_mp H, h⟩, λ h => ElimImply ⟨equiv_mpr H, h⟩⟩

lemma unequiv_left : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊬ᵈ[D] φ) → (Γ ⊬ᵈ[D] ψ) := by
  intro H₁ H₂;
  exact (equiv_decomp H₁).not.mp H₂;

lemma unequiv_right : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊬ᵈ[D] ψ) → (Γ ⊬ᵈ[D] φ) := λ H => unequiv_left $ equiv_comm H

end ModalLogic.PropositionalLogic.DeductionSystem