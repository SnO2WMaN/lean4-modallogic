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
  have h₁ : ⊢ₐ[T ∔ Γ ∪ {σ ⇒ ⊥}] ⊥ := ElimImply' ⟨hπ.right, hπ.left⟩;
  have h₂ : ⊢ₐ[T ∔ Γ] (σ ⇒ ⊥) ⇒ ⊥ := IntroImply h₁;
  have h₃ : ⊢ₐ[T ∔ Γ] ~~σ := by {
    repeat rw [←Sentence.def_Neg];
    exact h₂;
  }
  have h₄ : ⊢ₐ[T ∔ Γ] σ := ElimDN h₃;
  assumption;

/-- Proof of Löb's Theorem with Gödel's 2nd incompleteness theorem. -/
theorem Loeb_with_GoedelIT2 {σ}
  [HasFormalDeductionTheorem T Γ (Γ ∪ {~σ})] [HasFixedPointTheorem T (Γ ∪ {~σ})]
  [Derivability1 T (Γ ∪ {~σ}) (Γ ∪ {~σ})] [Derivability2 T (Γ ∪ {~σ}) (Γ ∪ {~σ})] [FormalizedSigma1Completeness T (Γ ∪ {~σ}) (Γ ∪ {~σ})]
  : (⊢ₐ[T ∔ Γ] σ) ↔ (⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](σ) ⇒ σ) := by
  apply Iff.intro;
  . intro H; exact ElimImply' ⟨K', H⟩;
  . intro H;
    have h₁ : ⊢ₐ[T ∔ Γ] ~σ ⇒ ~Pr[T ∔ Γ](σ) := T.contrapose₁ H;
    have h₂ : ⊢ₐ[T ∔ Γ ∪ {~σ}] ~Pr[T ∔ Γ](σ) := DT h₁;
    have h₃ : ⊢ₐ[T ∔ Γ ∪ {~σ}] ~Pr[T ∔ Γ](~~σ) := Provable.not_pr_negneg_intro h₂;
    have h₄ : ⊢ₐ[T ∔ Γ ∪ {~σ}] (~Pr[T ∔ Γ](~σ ⇒ ⊥)) ⇔ (~Pr[T ∔ Γ ∪ {~σ}](⊥)) := FDT_neg;
    have h₅ : ⊢ₐ[T ∔ Γ ∪ {~σ}] ~Pr[T ∔ Γ ∪ {~σ}](⊥) := ElimImply' ⟨equiv_mp h₄, h₃⟩;
    have h₆ : (⊢ₐ[T ∔ Γ ∪ {~σ}] ConL[T ∔ Γ ∪ {~σ}]) → IsHBInconsistent T (Γ ∪ {~σ}) := HBInconsistent_of_LConsistencyOfProvability;
    have h₇ : IsHBInconsistent T (Γ ∪ {~σ}) := h₆ h₅;
    exact provable_of_NegExpandHBInonsistency h₇;

end ModalLogic.Arithmetic