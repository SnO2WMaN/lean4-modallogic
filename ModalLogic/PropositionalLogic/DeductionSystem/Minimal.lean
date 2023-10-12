import ModalLogic.SupplymentSimp
import ModalLogic.PropositionalLogic.DeductionSystem.Notations
import ModalLogic.PropositionalLogic.DeductionSystem.Minimal0

open ModalLogic.PropositionalLogic.Axioms
open ModalLogic.PropositionalLogic.DeductionSystem
open IsMinimal HasElimImply HasIntroConj

namespace ModalLogic.PropositionalLogic.DeductionSystem

variable [DecidableEq α] [HasImply α] [HasDisj α] [HasConj α]
variable {D : DeductionSystem α} [IsMinimal D]

theorem ConjDecomp : (Γ ⊢ᵈ[D] (φ ⋏ ψ)) → ((Γ ⊢ᵈ[D] φ) ∧ (Γ ⊢ᵈ[D] ψ)):= by
  intro H;
  constructor;
  exact ElimConjL H;
  exact ElimConjR H;
alias conj_decomp := ConjDecomp

@[simp]
theorem ConjComm : (Γ ⊢ᵈ[D] (φ ⋏ ψ)) → (Γ ⊢ᵈ[D] (ψ ⋏ φ)) := by
  intro H;
  have h₁ := conj_decomp H;
  exact IntroConj' ⟨h₁.right, h₁.left⟩;
alias conj_comm := ConjComm

theorem ConjWeaken : (Γ ⊢ᵈ[D] φ) → (Γ ⊢ᵈ[D] φ ⋏ φ) := λ H => IntroConj' ⟨H, H⟩
alias conj_weakening := ConjWeaken

@[simp]
theorem ConjContract: (Γ ⊢ᵈ[D] φ ⋏ φ) → (Γ ⊢ᵈ[D] φ) := ElimConjL
alias conj_contract := ConjContract

lemma ElimConjL_Dilemma : ((Γ ⊢ᵈ[D] (φ ⋏ ψ) ⇒ ρ) ∧ (Γ ⊢ᵈ[D] φ ⇒ ψ)) → (Γ ⊢ᵈ[D] φ ⇒ ρ) := by
  intro H;
  have Hl : (Γ ∪ {φ}) ⊢ᵈ[D] φ ⋏ ψ ⇒ ρ := H.left;
  have Hr : (Γ ∪ {φ}) ⊢ᵈ[D] φ ⇒ ψ:= H.right;
  have h₁ : (Γ ∪ {φ}) ⊢ᵈ[D] φ := by simp;
  have h₂ : (Γ ∪ {φ}) ⊢ᵈ[D] ψ := ElimImply' ⟨Hr, h₁⟩;
  have h₃ := IntroConj' ⟨h₁, h₂⟩;
  have h₄ := ElimImply ⟨Hl, h₃⟩;
  aesop
alias conj_dilemma_elim_left := ElimConjL_Dilemma

lemma ElimConjR_Dilemma : ((Γ ⊢ᵈ[D] (φ ⋏ ψ) ⇒ ρ) ∧ (Γ ⊢ᵈ[D] ψ ⇒ φ)) → (Γ ⊢ᵈ[D] ψ ⇒ ρ) := by
  intro H;
  have Hl : (Γ ∪ {ψ}) ⊢ᵈ[D] φ ⋏ ψ ⇒ ρ := H.left;
  have Hr : (Γ ∪ {ψ}) ⊢ᵈ[D] ψ ⇒ φ := H.right;
  have h₁ : (Γ ∪ {ψ}) ⊢ᵈ[D] ψ := by simp;
  have h₂ : (Γ ∪ {ψ}) ⊢ᵈ[D] φ := ElimImply' ⟨Hr, h₁⟩;
  have h₃ := IntroConj' ⟨h₂, h₁⟩;
  have h₄ := ElimImply ⟨Hl, h₃⟩;
  aesop;
alias conj_dilemma_elim_right := ElimConjR_Dilemma

variable [HasBot α] [HasNeg α] [DefinedNeg α]

open DefinedNeg

lemma NonContradiction {φ} : (Γ ⊢ᵈ[D] (Axioms.NonContradiction φ)) := by
  simp only [Axioms.NonContradiction, defNeg];
  have h₁ : (Γ ∪ {φ ⋏ (φ ⇒ ⊥)}) ⊢ᵈ[D] φ ⋏ (φ ⇒ ⊥) := by simp;
  have h₁l := ElimConjL h₁;
  have h₁r := ElimConjR h₁;
  have h₂ := ElimImply ⟨h₁r, h₁l⟩;
  aesop;

variable [HasEquiv α] [DefinedEquiv α]

open DefinedEquiv

@[simp]
lemma IntroEquiv : ((Γ ⊢ᵈ[D] (φ ⇒ ψ)) ∧ (Γ ⊢ᵈ[D] (ψ ⇒ φ))) → (Γ ⊢ᵈ[D] (φ ⇔ ψ)) := by
  intro H;
  simp [defEquiv];
  have := IntroConj' H;
  aesop;
alias equiv_intro := IntroEquiv

@[simp]
lemma CommEquiv : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] (ψ ⇔ φ)) := by aesop;
alias equiv_comm := CommEquiv

@[simp]
lemma EquivMP : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] φ ⇒ ψ) := by
  intro H;
  simp [defEquiv] at H;
  exact ElimConjL H;
alias equiv_mp := EquivMP

@[simp]
lemma EquivMPR : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] ψ ⇒ φ) := λ H => equiv_mp $ equiv_comm H
alias equiv_mpr := EquivMPR

@[simp]
lemma IntroNegEquiv : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] ((~φ : α) ⇔ ~ψ)) := by 
  intro h;
  apply equiv_intro;
  exact ⟨contrapose₁ $ equiv_mpr h, contrapose₁ $ equiv_mp h⟩;
alias equiv_neg := IntroNegEquiv

lemma ElimEquivL : ((Γ ⊢ᵈ[D] (φ ⇔ ψ)) ∧ (Γ ⊢ᵈ[D] φ)) → (Γ ⊢ᵈ[D] ψ) := by
  intro H;
  exact ElimImply' ⟨equiv_mp H.left, H.right⟩;

lemma ElimEquivL' : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] φ) → (Γ ⊢ᵈ[D] ψ) := by
  intro H₁ H₂;
  exact ElimImply' ⟨equiv_mp H₁, H₂⟩;
alias equiv_pick_left := ElimEquivL'

lemma ElimEquivR' : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] ψ) → (Γ ⊢ᵈ[D] φ) := λ H => equiv_pick_left $ CommEquiv H
alias equiv_pick_right := ElimEquivR'

lemma NegElimEquivL' : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] (~φ)) → (Γ ⊢ᵈ[D] (~ψ)) := by
  intro H₁ H₂;
  exact ElimImply' ⟨equiv_mp $ equiv_neg H₁, H₂⟩;
alias equiv_pick_neg_left := NegElimEquivL'
  
lemma NegElimEquivR' : (Γ ⊢ᵈ[D] φ ⇔ ψ) → (Γ ⊢ᵈ[D] ~ψ) → (Γ ⊢ᵈ[D] (~φ)) := λ H => equiv_pick_neg_left $ equiv_comm H
alias equiv_pick_neg_right := NegElimEquivR'

lemma EquivTrans : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] (ψ ⇔ ρ)) → (Γ ⊢ᵈ[D] (φ ⇔ ρ)) := by
  intro H₁ H₂;
  apply equiv_intro;
  apply And.intro;
  . have H₁ := equiv_mp H₁;
    have H₂ := equiv_mp H₂;
    exact imply_trans ⟨H₁, H₂⟩;    
  . have H₁ := equiv_mpr H₁;
    have H₂ := equiv_mpr H₂;
    exact imply_trans ⟨H₂, H₁⟩;
alias equiv_trans := EquivTrans

lemma EquivDecomp : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → ((Γ ⊢ᵈ[D] φ) ↔ (Γ ⊢ᵈ[D] ψ)) := by
  intro H;
  exact ⟨λ h => ElimImply' ⟨equiv_mp H, h⟩, λ h => ElimImply' ⟨equiv_mpr H, h⟩⟩
alias equiv_decomp := EquivDecomp

lemma UnducibleElimEquivL : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊬ᵈ[D] φ) → (Γ ⊬ᵈ[D] ψ) := by
  intro H₁ H₂;
  exact (equiv_decomp H₁).not.mp H₂;
alias unequiv_left := UnducibleElimEquivL

lemma UnducibleElimEquivR : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊬ᵈ[D] ψ) → (Γ ⊬ᵈ[D] φ) := λ H => unequiv_left $ equiv_comm H
alias unequiv_right := UnducibleElimEquivR

end ModalLogic.PropositionalLogic.DeductionSystem