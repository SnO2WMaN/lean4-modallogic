import ModalLogic.PropositionalLogic.DeductionSystem
import ModalLogic.Arithmetic.Notation
import ModalLogic.Arithmetic.IT2

open ModalLogic.PropositionalLogic DeductionSystem HasIntroImply HasElimImply HasElimDN HasExplode
open ModalLogic.Arithmetic.Arithmetic HasFormalDeductionTheorem Derivability1 Derivability2 Derivability3

namespace ModalLogic.Arithmetic

variable [DecidableEq α] {T : Arithmetic α} {Γ : Context (Sentence α)}
variable [IsClassical T.toDeductionSystem]

lemma provable_of_NegExpandHBInonsistency {σ} : (IsHBInconsistent T (Γ ∪ {~σ})) → (⊢ₐ[T ∔ Γ] σ) := by
  intro H;
  simp at H;
  have ⟨π, hπ⟩ := H;
  have h₁ : ⊢ₐ[T ∔ Γ ∪ {σ ⇒ₐ ⊥}] ⊥ := ElimImply' ⟨hπ.right, hπ.left⟩;
  have h₂ : ⊢ₐ[T ∔ Γ] (σ ⇒ₐ ⊥) ⇒ₐ ⊥ := IntroImply h₁;
  have h₃ : ⊢ₐ[T ∔ Γ] ~ₐ~ₐσ := by {
    repeat rw [←Sentence.def_Neg];
    exact h₂;
  }
  have h₄ : ⊢ₐ[T ∔ Γ] σ := ElimDN h₃;
  assumption;

/-- Proof of Löb's Theorem with Gödel's 2nd incompleteness theorem. -/
theorem Loeb_with_GoedelIT2 {σ}
  [HasFormalDeductionTheorem T Γ (Γ ∪ {~ₐσ})] [HasFixedPointTheorem T (Γ ∪ {~σ})]
  [Derivability1 T (Γ ∪ {~ₐσ}) (Γ ∪ {~ₐσ})] [Derivability2 T (Γ ∪ {~ₐσ}) (Γ ∪ {~ₐσ})] [FormalizedSigma1Completeness T (Γ ∪ {~σ}) (Γ ∪ {~ₐσ})]
  : (⊢ₐ[T ∔ Γ] σ) ↔ (⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](σ) ⇒ₐ σ) := by
  apply Iff.intro;
  . intro H; exact ElimImply' ⟨K', H⟩;
  . intro H;
    have h₁ : ⊢ₐ[T ∔ Γ] ~σ ⇒ₐ ~Pr[T ∔ Γ](σ) := T.contrapose₁ H;
    have h₂ : ⊢ₐ[T ∔ Γ ∪ {~ₐσ}] ~ₐPr[T ∔ Γ](σ) := DT h₁;
    have h₃ : ⊢ₐ[T ∔ Γ ∪ {~ₐσ}] ~ₐPr[T ∔ Γ](~ₐ~ₐσ) := Provable.not_pr_negneg_intro h₂;
    have h₄ : ⊢ₐ[T ∔ Γ ∪ {~ₐσ}] ~ₐPr[T ∔ Γ](~ₐσ ⇒ₐ ⊥ₐ) ⇔ₐ ~ₐPr[T ∔ Γ ∪ {~ₐσ}](⊥ₐ) := FDT_neg;
    have h₅ : ⊢ₐ[T ∔ Γ ∪ {~ₐσ}] ~ₐPr[T ∔ Γ ∪ {~ₐσ}](⊥ₐ) := ElimImply' ⟨equiv_mp h₄, h₃⟩;
    have h₆ : (⊢ₐ[T ∔ Γ ∪ {~σ}] ConL[T ∔ Γ ∪ {~σ}]) → IsHBInconsistent T (Γ ∪ {~σ}) := HBInconsistent_of_LConsistencyOfProvability;
    have h₇ : IsHBInconsistent T (Γ ∪ {~σ}) := h₆ h₅;
    exact provable_of_NegExpandHBInonsistency h₇;

end ModalLogic.Arithmetic