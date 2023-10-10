import ModalLogic.PropositionalLogic.DeductionSystem
import ModalLogic.Arithmetic.Notation

open ModalLogic.PropositionalLogic DeductionSystem HasElimImply
open ModalLogic.Arithmetic.Arithmetic Derivability1 Derivability2 Derivability3

namespace ModalLogic.Arithmetic

variable [DecidableEq α] {T : Arithmetic α} {Γ : Context (Sentence α)}
variable [IsMinimal T.toDeductionSystem]
variable [HasFixedPointTheorem T Γ] [Derivability1 T Γ Γ] [Derivability2 T Γ Γ] [Derivability3 T Γ Γ]

/-- Proof of Löb's Theorem without Gödel's 2nd incompleteness theorem -/
theorem Loeb_without_GoedelIT2 {σ} : (⊢ₐ[T ∔ Γ] σ) ↔ (⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](σ) ⇒ₐ σ) := by
  apply Iff.intro;
  . intro H;
    exact ElimImply' ⟨K', H⟩;
  . intro H;
    have ⟨K, (hK : KreiselSentence T Γ σ K)⟩ := existsKreiselSentence σ 
    simp only [KreiselSentence] at hK;
    have h₁  : ⊢ₐ[T ∔ Γ] K ⇒ₐ (Pr[T ∔ Γ](K) ⇒ₐ σ) := equiv_mp hK;
    have h₂  : ⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](K ⇒ₐ (Pr[T ∔ Γ](K) ⇒ₐ σ)) := D1 h₁;
    have h₃  : ⊢ₐ[T ∔ Γ] (Pr[T ∔ Γ](K) ⇒ₐ Pr[T ∔ Γ](Pr[T ∔ Γ](K) ⇒ₐ σ)) := ElimImply' ⟨D2, h₂⟩;
    have h₄  : ⊢ₐ[T ∔ Γ] (Pr[T ∔ Γ](Pr[T ∔ Γ](K) ⇒ₐ σ) ⇒ₐ (Pr[T ∔ Γ](Pr[T ∔ Γ](K)) ⇒ₐ Pr[T ∔ Γ](σ))) := D2;
    have h₅  : ⊢ₐ[T ∔ Γ] (Pr[T ∔ Γ](K) ⇒ Pr[T ∔ Γ](Pr[T ∔ Γ](K)) ⇒ₐ Pr[T ∔ Γ](σ)) := imply_trans ⟨h₃, h₄⟩;
    have h₆  : ⊢ₐ[T ∔ Γ] (Pr[T ∔ Γ](K) ⇒ₐ Pr[T ∔ Γ](Pr[T ∔ Γ](K))) := D3;
    have h₇  : ⊢ₐ[T ∔ Γ] (Pr[T ∔ Γ](K) ⇒ Pr[T ∔ Γ](σ)) := ElimImply' ⟨ElimImply' ⟨S', h₅⟩, h₆⟩;
    have h₈  : ⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](K) ⇒ₐ σ := imply_trans ⟨h₇, H⟩;
    have h₉  : ⊢ₐ[T ∔ Γ] K := (equiv_decomp hK).mpr h₈;
    have h₁₀ : ⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](K) := D1 h₉;
    have h₁₁ : ⊢ₐ[T ∔ Γ] σ := ElimImply' ⟨h₈, h₁₀⟩;
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
  exact Loeb_without_GoedelIT2.mpr (equiv_mpr hH);

end ModalLogic.Arithmetic