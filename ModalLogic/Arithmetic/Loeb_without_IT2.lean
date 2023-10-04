import Aesop
import ModalLogic.Arithmetic.Notation

open ModalLogic.PropositionalLogic 
open ModalLogic.PropositionalLogic.Axioms
open ModalLogic.PropositionalLogic.DeductionSystem HasMP
open ModalLogic.Arithmetic.Arithmetic Derivability1 Derivability2 Derivability3

namespace ModalLogic.Arithmetic

variable [DecidableEq α] {T : Arithmetic α} {Γ : Context (Sentence α)}
variable [HasDT T.toDeductionSystem] [HasMP T.toDeductionSystem] [HasExplode T.toDeductionSystem] [HasDNElim T.toDeductionSystem]
variable [HasKreiselSentence T Γ] [Derivability1 T Γ] [Derivability2 T Γ] [Derivability3 T Γ]

/-- Proof of Löb's Theorem without Gödel's 2nd incompleteness theorem -/
theorem Loeb_without_GoedelIT2 {σ} : (⊢ₐ[T ∔ Γ] σ) ↔ (⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](σ) ⇒ₐ σ) := by
  apply Iff.intro;
  . sorry; -- exact λ H => impₐ_intro_con (Pr[T](σ)) H;
  . intro H;
    have ⟨K, hK⟩ := @existsKreiselSentence _ Γ T _ σ;
    simp only [KreiselSentence] at hK;
    have h₁ : ⊢ₐ[T ∔ Γ] K ⇒ₐ (Pr[T ∔ Γ](K) ⇒ₐ σ) := deducible_equiv_mp hK;
    have h₂ : ⊢ₐ[T ∔ Γ] K ⇒ₐ Pr[T ∔ Γ](K) := sorry -- (mpₐ _).mpr D1;
    have h₃ : ⊢ₐ[T ∔ Γ] (K ⇒ₐ Pr[T ∔ Γ](K)) ⇒ₐ (K ⇒ₐ σ) := sorry; -- T.deducible_MP h₁ h₂;
    
    have h₄ : ⊢ₐ[T ∔ Γ] K ⇒ₐ σ := MP h₃ h₂;
    have h₅ : ⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](K) ⇒ₐ Pr[T ∔ Γ](σ) := MP D2 (D1 h₄);
    have h₆ : ⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](K) ⇒ₐ σ := T.deducible_imply_trans ⟨h₅, H⟩;
    have h₇ : ⊢ₐ[T ∔ Γ] K := (deducible_equiv_eq.mp hK).mpr h₆;
    have h₈ : ⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](K) := D1 h₇;
    have h₉ : ⊢ₐ[T ∔ Γ] σ := MP h₆ h₈;
    assumption;

lemma LInconsistent_of_ProvabilityLconsistencyOf : (⊢ₐ[T ∔ Γ] ConL[T ∔ Γ]) → (LInconsistent T Γ) := by
  simp only [LInconsistent];
  exact λ h => Loeb_without_GoedelIT2.mpr h;

/-- Another proof of unprovability side of Gödel's 2nd incompleteness theorem via Löb's Theorem. -/
theorem LConsistencyofUnprovability_of_LConsistent : (LConsistent T Γ) → (⊬ₐ[T ∔ Γ] ConL[T ∔ Γ]) := by
  apply imp_not_comm.mp;
  intro hPC;
  have _ := LInconsistent_of_ProvabilityLconsistencyOf hPC;
  aesop;

/-- Provability of Henkin sentence. -/
theorem HenkinSentenceProvablility (hH : HenkinSentence T Γ H): (⊢ₐ[T ∔ Γ] H) := by
  exact Loeb_without_GoedelIT2.mpr (T.deducible_equiv_mpr hH);

end ModalLogic.Arithmetic