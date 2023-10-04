import Aesop
import ModalLogic.Arithmetic.Notation

open ModalLogic.PropositionalLogic 
open ModalLogic.PropositionalLogic.Axioms
open ModalLogic.PropositionalLogic.DeductionSystem HasMP
open ModalLogic.Arithmetic.Arithmetic Derivability1 Derivability2 Derivability3

namespace ModalLogic.Arithmetic

variable [DecidableEq α] {T : Arithmetic α}
variable [HasDT T.toDeductionSystem] [HasMP T.toDeductionSystem] [HasExplode T.toDeductionSystem] [HasDNElim T.toDeductionSystem]
variable [HasKreiselSentence T] [Derivability1 T] [Derivability2 T] [Derivability3 T]

/--
  Proof of Löb's Theorem without Gödel's 2nd incompleteness theorem.
-/
theorem Loeb_without_GoedelIT2 {σ} : (⊢ₐ[T] σ) ↔ (⊢ₐ[T] Pr[T](σ) ⇒ₐ σ) := by
  apply Iff.intro;
  . sorry; -- exact λ H => impₐ_intro_con (Pr[T](σ)) H;
  . intro H;
    have ⟨K, hK⟩ := @existsKreiselSentence _ T _ σ;
    simp only [KreiselSentence] at hK;
    have h₁ : ⊢ₐ[T] K ⇒ₐ (Pr[T](K) ⇒ₐ σ) := deducible_equiv_mp hK;
    have h₂ : ⊢ₐ[T] K ⇒ₐ Pr[T](K) := sorry -- (mpₐ _).mpr D1;
    have h₃ : ⊢ₐ[T] (K ⇒ₐ Pr[T](K)) ⇒ₐ (K ⇒ₐ σ) := sorry; -- T.deducible_MP h₁ h₂;
    
    have h₄ : ⊢ₐ[T] K ⇒ₐ σ := MP h₃ h₂;
    have h₅ : ⊢ₐ[T] Pr[T](K) ⇒ₐ Pr[T](σ) := MP D2 (D1 h₄);
    have h₆ : ⊢ₐ[T] Pr[T](K) ⇒ₐ σ := T.deducible_imply_trans ⟨h₅, H⟩;
    have h₇ : ⊢ₐ[T] K := (deducible_equiv_eq.mp hK).mpr h₆;
    have h₈ : ⊢ₐ[T] Pr[T](K) := D1 h₇;
    have h₉ : ⊢ₐ[T] σ := MP h₆ h₈;
    assumption;

lemma LInconsistent_of_ProvabilityLconsistencyOf : (⊢ₐ[T] ConL[T]) → (LInconsistent T) := by
  simp only [LInconsistent];
  exact λ h => Loeb_without_GoedelIT2.mpr h;

/--
  Another proof of unprovability side of Gödel's 2nd incompleteness theorem via Löb's Theorem.
-/
theorem LConsistencyofUnprovability_of_LConsistent : (LConsistent T) → (⊬ₐ[T] ConL[T]) := by
  apply imp_not_comm.mp;
  intro hPC;
  have _ := LInconsistent_of_ProvabilityLconsistencyOf hPC;
  aesop;

end ModalLogic.Arithmetic