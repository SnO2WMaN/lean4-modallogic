import ModalLogic.Notations
import ModalLogic.PropositionalLogic.DeductionSystem

open ModalLogic.PropositionalLogic DeductionSystem

namespace ModalLogic.Arithmetic

inductive Sentence (α : Type u)
| Contradiction : Sentence α
| Imply : Sentence α → Sentence α → Sentence α
deriving DecidableEq, Repr

namespace Sentence

instance : HasBot (Sentence α) := ⟨Contradiction⟩
instance : HasImply (Sentence α) := ⟨Imply⟩

variable (φ ψ : Sentence α)

def Neg := φ ⇒ ⊥
instance : HasNeg (Sentence α) := ⟨Neg⟩

def def_Neg : (φ ⇒ ⊥) = ~φ := rfl
instance : DefinedNeg (Sentence α) := ⟨def_Neg⟩

def Disj := (~φ) ⇒ ψ
instance : HasDisj (Sentence α) := ⟨Disj⟩

def def_Disj : (φ ⋎ ψ) = (~φ ⇒ ψ) := rfl
instance : HasDisjDef (Sentence α) := ⟨def_Disj⟩

def Conj := ~(φ ⇒ ~ψ)
instance : HasConj (Sentence α) := ⟨Conj⟩

def def_Conj : (φ ⋏ ψ) = ~(φ ⇒ ~ψ) := rfl
instance : HasConjDef (Sentence α) := ⟨def_Conj⟩

def Equiv := (φ ⇒ ψ) ⋏ (ψ ⇒ φ)
instance : PropositionalLogic.HasEquiv (Sentence α) := ⟨Equiv⟩

def def_Equiv : (φ ⇔ ψ) = ((φ ⇒ ψ) ⋏ (ψ ⇒ φ)) := rfl
instance : DefinedEquiv (Sentence α) := ⟨def_Equiv⟩

end Sentence

open Sentence

structure Arithmetic (α) [DecidableEq α] extends DeductionSystem (Sentence α) where 
  Provable : (Context (Sentence α)) → (Sentence α) → (Sentence α)

notation "Pr[" T " ∔ " Γ "](" σ ")" => Arithmetic.Provable T Γ σ
notation "Pr[" T "](" σ ")" => Pr[T ∔ ∅](σ)

variable [DecidableEq α]
private def Arithmetic.Deducible_def (T : Arithmetic α) (Γ σ) := T.Deducts Γ σ

notation:20 "⊢ₐ[" T " ∔ " Γ "] " σ => Arithmetic.Deducible_def T Γ σ
notation:20 "⊬ₐ[" T " ∔ " Γ "] " σ => ¬(⊢ₐ[T ∔ Γ] σ)

notation:20 "⊢ₐ[" T "] " σ => ⊢ₐ[T ∔ ∅] σ
notation:20 "⊬ₐ[" T "] " σ => ¬(⊢ₐ[T] σ)

namespace Arithmetic

variable (T : Arithmetic α) (Γ Δ : Context (Sentence α))

class IsSigma1Sounds extends Arithmetic α where 
  Sigma1Sounds : ∀ σ, (⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](σ)) → (⊢ₐ[T ∔ Γ] σ)

class HasFixedPointTheorem extends Arithmetic α where
  /-- Fixed point theorem (Diagonal lemma) -/
  FP (P : Sentence α → Sentence α) : ∃ σ, ⊢ₐ[T ∔ Γ] (σ ⇔ (P σ))

class HasFormalDeductionTheorem extends Arithmetic α where
  /-- Formalized deduction theorem -/
  FDT {σ π : Sentence α} : (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ ⇒ π) ⇔ Pr[T ∔ Γ ∪ {σ}](π))

lemma HasFormalDeductionTheorem.FDT_neg {T : Arithmetic α} {Γ Δ} [IsMinimal T.toDeductionSystem] [HasFormalDeductionTheorem T Γ Δ] {σ π} 
  : (⊢ₐ[T ∔ Δ] (~Pr[T ∔ Γ](σ ⇒ π)) ⇔ (~Pr[T ∔ Γ ∪ {σ}](π))) := by
  suffices (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ ⇒ π) ⇔ Pr[T ∔ Γ ∪ {σ}](π)) from by exact T.equiv_neg this;
  exact HasFormalDeductionTheorem.FDT

def Incompleteness := ∃ σ, (⊬ₐ[T ∔ Γ] σ) ∧ (⊬ₐ[T ∔ Γ] ~σ)

-- Löb style Consistent 
@[simp] def LInconsistent := (⊢ₐ[T ∔ Γ] ⊥)
@[simp] def LConsistent := ¬(LInconsistent T Γ)

@[simp] def LConsistencyOf : Sentence α := ~Pr[T ∔ Γ](⊥)
notation "ConL[" T " ∔ " Γ "]" => Arithmetic.LConsistencyOf T Γ
notation "ConL[" T "]" => ConL[T ∔ ∅]

-- Hilbert-Bernays style Consistent 
@[simp] def IsHBConsistent := ∀ σ, (⊢ₐ[T ∔ Γ] σ) → (⊬ₐ[T ∔ Γ] ~σ)
@[simp] def IsHBInconsistent := ¬(IsHBConsistent T Γ)

axiom HBConsistent_of_Sigma1Soundness {T : Arithmetic α} {Γ} : IsSigma1Sounds T Γ → IsHBConsistent T Γ

-- Gödel style Consistent 
@[simp] def GConsistent := ∃ σ, (⊬ₐ[T ∔ Γ] σ) 
@[simp] def GInconsistent := ¬(GConsistent T Γ)

class Derivability1 extends Arithmetic α where
  D1  : ∀ {σ}, (⊢ₐ[T ∔ Δ] σ) → (⊢ₐ[T ∔ Δ] (Pr[T ∔ Γ](σ)))

class Derivability2 extends Arithmetic α where
  D2 : ∀ {σ π}, ⊢ₐ[T ∔ Δ] (Pr[T ∔ Γ](σ ⇒ π) ⇒ (Pr[T ∔ Γ](σ) ⇒ Pr[T ∔ Γ](π)))

class Derivability3 extends Arithmetic α where
  D3 : ∀ {σ}, ⊢ₐ[T ∔ Δ] ((Pr[T ∔ Γ](σ)) ⇒ Pr[T ∔ Γ](Pr[T ∔ Γ](σ)))

class FormalizedSigma1Completeness extends Arithmetic α where
  FS1C : ∀ {σ}, ⊢ₐ[T ∔ Δ] (σ ⇒ Pr[T ∔ Γ](σ))

section

variable {T : Arithmetic α} [IsMinimal T.toDeductionSystem]
variable {Γ Δ} {σ π : Sentence α}
variable [Derivability1 T Γ Δ] [Derivability2 T Γ Δ] [Derivability3 T Γ Δ]

open HasElimImply HasIntroConj
open Derivability1 Derivability2

lemma Provable.conj_distribute : (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ ⋏ π)) → (⊢ₐ[T ∔ Δ] (Pr[T ∔ Γ](σ) ⋏ Pr[T ∔ Γ](π))) := by
  intro H;
  sorry

lemma Provable.PrIntroConj :  (⊢ₐ[T ∔ Δ] (Pr[T ∔ Γ](σ) ⋏ Pr[T ∔ Γ](π))) → (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ ⋏ π)) := by
  intro H;
  sorry

lemma Provable.PrIntroDN : (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ)) → (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](~~σ)) := λ H => ElimImply' ⟨ElimImply' ⟨D2, D1 DNI⟩, H⟩

lemma Provable.not_pr_negneg_intro : (⊢ₐ[T ∔ Δ] ~Pr[T ∔ Γ](σ)) → (⊢ₐ[T ∔ Δ] ~Pr[T ∔ Γ](~~σ)) := by
  intro H;
  sorry

lemma Provable.noContradiction' : (⊢ₐ[T ∔ Δ] (Pr[T ∔ Γ](σ) ⋏ Pr[T ∔ Γ](~σ))) → (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](⊥)) := by
  have h₁ : ⊢ₐ[T ∔ Δ] (σ ⋏ ~σ) ⇒ ⊥ := NonContradiction;
  have h₂ : ⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ ⋏ ~σ) ⇒ Pr[T ∔ Γ](⊥) := ElimImply' ⟨D2, (D1 h₁)⟩;
  have h₃ : (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ) ⋏ Pr[T ∔ Γ](~σ)) → (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](⊥)) := λ h => ElimImply' ⟨h₂, PrIntroConj h⟩;
  assumption;

lemma Provable.noContradiction : (⊢ₐ[T ∔ Δ] (Pr[T ∔ Γ](σ) ⋏ Pr[T ∔ Γ](~σ)) ⇒ Pr[T ∔ Γ](⊥)) := by
  have h₁ : ⊢ₐ[T ∔ Δ] (σ ⋏ ~σ) ⇒ ⊥ := NonContradiction;
  have h₂ : ⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ ⋏ ~σ) ⇒ Pr[T ∔ Γ](⊥) := ElimImply' ⟨D2, (D1 h₁)⟩;
  have h₃ : (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ) ⋏ Pr[T ∔ Γ](~σ)) → (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](⊥)) := λ h => ElimImply' ⟨h₂, PrIntroConj h⟩;
  have h₄ : ((⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ)) ∧ (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](~σ))) → (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](⊥)) := λ h => h₃ (IntroConj' h);
  sorry

end

section ProvablilityFixedPoints

@[simp] def GoedelSentence (G : Sentence α) := ⊢ₐ[T ∔ Γ] (G ⇔ ~Pr[T ∔ Γ](G))

lemma existsGoedelSentence {T : Arithmetic α} (Γ) [HasFixedPointTheorem T Γ] : ∃ G, GoedelSentence T Γ G := HasFixedPointTheorem.FP (λ σ => ~Pr[T ∔ Γ](σ))


@[simp] def HenkinSentence (H : Sentence α) := ⊢ₐ[T ∔ Γ] (H ⇔ Pr[T ∔ Γ](H))

lemma existsHenkinSentence {T : Arithmetic α} {Γ} [HasFixedPointTheorem T Γ] : ∃ H, HenkinSentence T Γ H := HasFixedPointTheorem.FP (λ σ => (Pr[T ∔ Γ](σ)))


@[simp] def JeroslowSentence (J : Sentence α) := ⊢ₐ[T ∔ Γ] (J ⇔ Pr[T ∔ Γ](~J))

@[simp] def NotJeroslowSentence (NJ : Sentence α) := ⊢ₐ[T ∔ Γ] (NJ ⇔ ~Pr[T ∔ Γ](~NJ))


@[simp] def KreiselSentence (σ : Sentence α) (K : Sentence α) := ⊢ₐ[T ∔ Γ] (K ⇔ (Pr[T ∔ Γ](K) ⇒ σ))

lemma existsKreiselSentence {T : Arithmetic α} {Γ} [HasFixedPointTheorem T Γ] (σ) : ∃ K, KreiselSentence T Γ σ K := HasFixedPointTheorem.FP (λ π => (Pr[T ∔ Γ](π) ⇒ σ))

end ProvablilityFixedPoints

end Arithmetic

end ModalLogic.Arithmetic