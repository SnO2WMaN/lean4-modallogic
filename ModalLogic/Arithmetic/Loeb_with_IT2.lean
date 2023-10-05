import Aesop
import ModalLogic.Arithmetic.Notation
import ModalLogic.Arithmetic.IT2

open ModalLogic.PropositionalLogic 
open ModalLogic.PropositionalLogic.Axioms
open ModalLogic.PropositionalLogic.DeductionSystem HasMP HasDT
open ModalLogic.Arithmetic.Arithmetic HasFormalDeductionTheorem Derivability1 Derivability2 Derivability3

namespace ModalLogic.Arithmetic

variable [DecidableEq α] {T : Arithmetic α} {Γ : Context (Sentence α)}
variable [HasDT T.toDeductionSystem] [HasMP T.toDeductionSystem] [HasExplode T.toDeductionSystem] [HasDNElim T.toDeductionSystem]

/-- Proof of Löb's Theorem with Gödel's 2nd incompleteness theorem. -/
theorem Loeb_with_GoedelIT2 {σ}
  [HasFormalDeductionTheorem T Γ (Γ ∪ {~ₐσ})] [HasGoedelSentence T (Γ ∪ {~σ})]
  [Derivability1 T (Γ ∪ {~ₐσ})] [Derivability2 T (Γ ∪ {~ₐσ})] [FormalizedSigma1Completeness T (Γ ∪ {~σ})]
  : (⊢ₐ[T ∔ Γ] σ) ↔ (⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](σ) ⇒ₐ σ) := by
  apply Iff.intro;
  . intro H; exact (MP deducible_K H);
  . intro H;
    have h₁ : ⊢ₐ[T ∔ Γ] ~σ ⇒ ~Pr[T ∔ Γ](σ) := T.deducible_contrapose₁ H;
    have h₂ : ⊢ₐ[T ∔ Γ ∪ {~ₐσ}] ~ₐPr[T ∔ Γ](σ) := DT.mp h₁;
    have h₃ : ⊢ₐ[T ∔ Γ ∪ {~ₐσ}] ~ₐPr[T ∔ Γ](~ₐ~ₐσ) := sorry;
    have h₄ : ⊢ₐ[T ∔ Γ ∪ {~ₐσ}] ~ₐPr[T ∔ Γ](~ₐσ ⇒ₐ ⊥ₐ) ⇔ₐ ~ₐPr[T ∔ Γ ∪ {~ₐσ}](⊥ₐ) := FDT_neg;
    have h₅ : ⊢ₐ[T ∔ Γ ∪ {~ₐσ}] ~ₐPr[T ∔ Γ ∪ {~ₐσ}](⊥ₐ) := MP (deducible_equiv_mp h₄) h₃;
    have h₆ : (⊢ₐ[T ∔ Γ ∪ {~σ}] ConL[T ∔ Γ ∪ {~σ}]) → IsHBInconsistent T (Γ ∪ {~σ}) := HBInconsistent_of_LConsistencyOfProvability;
    -- TODO: `IsHBInconsistent T (Γ ∪ {~σ}) → ⊢ₐ[T ∔ Γ] σ`を補題として切り出す
    have h₇ : IsHBInconsistent T (Γ ∪ {~σ}) := h₆ h₅;
    simp at h₇;
    have ⟨ρ, hρ⟩ := h₇;
    have h₈ : ⊢ₐ[T ∔ Γ ∪ {σ ⇒ ⊥}] ⊥ := MP hρ.right hρ.left;
    have h₉ : ⊢ₐ[T ∔ Γ] ~ₐ~ₐσ := HasDT.DT.mpr h₈;
    exact HasDNElim.DNElim h₉;

#print axioms Loeb_with_GoedelIT2

end ModalLogic.Arithmetic