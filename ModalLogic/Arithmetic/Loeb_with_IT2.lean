import Aesop
import ModalLogic.Arithmetic.Notation
import ModalLogic.Arithmetic.IT2

open ModalLogic.PropositionalLogic 
open ModalLogic.PropositionalLogic.Axioms
open ModalLogic.PropositionalLogic.DeductionSystem HasMP
open ModalLogic.Arithmetic.Arithmetic Derivability1 Derivability2 Derivability3

namespace ModalLogic.Arithmetic

variable [DecidableEq α] {T : Arithmetic α} {Γ : Context (Sentence α)}
variable [HasDT T.toDeductionSystem] [HasMP T.toDeductionSystem] [HasExplode T.toDeductionSystem] [HasDNElim T.toDeductionSystem]
variable [HasGoedelSentence T Γ] [HasKreiselSentence T Γ] [Derivability1 T Γ] [Derivability2 T Γ] [Derivability3 T Γ]

axiom FormalDeduction {σ π : Sentence α} : (⊢ₐ[T ∔ Γ] σ ⇒ₐ π) ↔ (Arithmetic.Deducible_def T (Γ ∪ {σ}) π)

/--
  Proof of Löb's Theorem with Gödel's 2nd incompleteness theorem.
-/
theorem Loeb_with_GoedelIT2 {σ} : (⊢ₐ[T ∔ Γ] σ) ↔ (⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](σ) ⇒ₐ σ) := by
  apply Iff.intro;
  . intro H; exact (MP deducible_K H);
  . intro H;
    have h₁ : ⊢ₐ[T ∔ Γ] ~σ ⇒ ~Pr[T ∔ Γ](σ) := T.deducible_contrapose₁ H;
    have h₂ := FormalDeduction.mp h₁;
    -- have h₃ := D1 h₂;
    have h₅ : ⊢ₐ[T ∔ Γ ∪ {~σ}] ~Pr[T ∔ Γ ∪ {~σ}](⊥) := sorry;
    have h₆ : (⊢ₐ[T ∔ Γ ∪ {~σ}] ConL[T ∔ Γ ∪ {~σ}]) → IsHBInconsistent T (Γ ∪ {~σ}) := sorry;
    have h₇ := h₆ h₅;
    simp at h₇;
    have ⟨ρ, hρ⟩ := h₇;
    have h₈ : ⊢ₐ[T ∔ Γ ∪ {σ ⇒ ⊥}] ⊥ := MP hρ.right hρ.left;
    have h₉ : ⊢ₐ[T ∔ Γ] ~ₐ~ₐσ := FormalDeduction.mpr h₈;
    exact HasDNElim.DNElim h₉;

end ModalLogic.Arithmetic