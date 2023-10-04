import ModalLogic.PropositionalLogic.DeductionSystem

open ModalLogic.PropositionalLogic DeductionSystem

namespace ModalLogic.Arithmetic

inductive Sentence (α : Type u)
| Contradiction : Sentence α
| Imply : Sentence α → Sentence α → Sentence α
deriving DecidableEq, Repr

notation "⊥ₐ" => Sentence.Contradiction
infixl:63 " ⇒ₐ " => Sentence.Imply

namespace Sentence

instance : HasBot (Sentence α) := ⟨Contradiction⟩
instance : HasImply (Sentence α) := ⟨Imply⟩

variable (φ ψ : Sentence α)

@[simp] def Neg := φ ⇒ₐ ⊥ₐ
prefix:70 "~ₐ" => Neg
instance : HasNeg (Sentence α) := ⟨Neg⟩

@[simp] def def_Neg : φ ⇒ₐ ⊥ₐ = ~ₐφ := rfl
instance : HasNegDef (Sentence α) := ⟨def_Neg⟩

@[simp] def Disj := (~ₐφ) ⇒ₐ ψ
infixl:64 " ⋎ₐ " => Disj
instance : HasDisj (Sentence α) := ⟨Disj⟩

@[simp] def def_Disj : (~ₐφ) ⇒ₐ ψ = φ ⋎ₐ ψ := rfl
instance : HasDisjDef (Sentence α) := ⟨def_Disj⟩

@[simp] def Conj := ~ₐ(φ ⇒ ~ψ)
infixl:65 " ⋏ₐ " => Conj
instance : HasConj (Sentence α) := ⟨Conj⟩

@[simp] def def_Conj : ~ₐ(φ ⇒ ~ψ) = φ ⋏ₐ ψ := rfl
instance : HasConjDef (Sentence α) := ⟨def_Conj⟩

@[simp] def Equiv := (φ ⇒ₐ ψ) ⋏ₐ (ψ ⇒ₐ φ)
infixl:61 " ⇔ₐ " => Equiv
instance : PropositionalLogic.HasEquiv (Sentence α) := ⟨Equiv⟩

@[simp]
def def_Equiv : (φ ⇒ₐ ψ) ⋏ₐ (ψ ⇒ₐ φ) = φ ⇔ₐ ψ := rfl
instance : HasEquivDef (Sentence α) := ⟨def_Equiv⟩

end Sentence


open Sentence

structure Arithmetic (α) extends DeductionSystem (Sentence α) where 
  Provable : (Sentence α) → (Sentence α)

notation "Pr[" T "](" σ ")" => Arithmetic.Provable T σ

def Arithmetic.Proves_def (T : Arithmetic α) (σ : Sentence α) := T.Proves σ

def Arithmetic.Deducible_def (T : Arithmetic α) (Γ σ) := T.Deducts Γ σ

notation:20 "⊢ₐ[" T " + " Γ "] " σ => Arithmetic.Deducible_def T Γ σ
notation:20 "⊬ₐ[" T " + " Γ "] " σ => ¬(⊢[T + Γ] σ)

notation:20 "⊢ₐ[" T "] " σ => Arithmetic.Deducible_def T ∅ σ
notation:20 "⊬ₐ[" T "] " σ => ¬(⊢ₐ[T] σ)

-- notation:20 "⊢ₐ[" T "] " σ => Arithmetic.Proves_def T σ 


namespace Arithmetic

variable (T : Arithmetic α)

class IsSigma₁Sounds extends Arithmetic α where 
  Sigma₁Sounds : ∀ σ, (⊢ₐ[T] Pr[T](σ)) → (⊢ₐ[T] σ)

class IsSigma1Sounds extends Arithmetic α where 
  Sigma1Sounds : ∀ σ, (⊢ₐ[T] Pr[T](σ)) → (⊢ₐ[T] σ)

class HasFixedPoint extends Arithmetic α where 
  hasFP (P : Sentence α → Sentence α) : ∃ σ, ⊢ₐ[T] (σ ⇔ₐ (P σ))

def Incompleteness (T : Arithmetic α) := ∃ σ, (⊬ₐ[T] σ) ∧ (⊬ₐ[T] ~ₐσ)

-- Löb style Consistent 
@[simp] def LInconsistent := (⊢ₐ[T] ⊥ₐ)
@[simp] def LConsistent := ¬(LInconsistent T)

@[simp] def LConsistencyOf : Sentence α := ~ₐPr[T](⊥ₐ)
notation "ConL[" T "]" => Arithmetic.LConsistencyOf T

-- Hilbert-Bernays style Consistent 
@[simp] def IsHBConsistent := ∀ σ, (⊢ₐ[T] σ) → (⊬ₐ[T] ~ₐσ)
@[simp] def IsHBInconsistent := ¬(IsHBConsistent T)

axiom HBConsistent_of_Sigma1Soundness {T : Arithmetic α} : IsSigma1Sounds T → IsHBConsistent T

-- Gödel style Consistent 
@[simp] def GConsistent := ∃ σ, (⊬ₐ[T] σ)
class IsGConsistent extends Arithmetic α where 
  GConsistent : GConsistent T


class Derivability1 extends Arithmetic α where
  D1 : ∀ {σ}, (⊢ₐ[T] σ) → (⊢ₐ[T] (Pr[T](σ)))

class Derivability2 extends Arithmetic α where
  D2 : ∀ {σ π}, ⊢ₐ[T] (Pr[T](σ ⇒ₐ π) ⇒ₐ (Pr[T](σ) ⇒ₐ Pr[T](π)))

class Derivability3 extends Arithmetic α where
  D3 : ∀ {σ}, ⊢ₐ[T] ((Pr[T](σ)) ⇒ₐ Pr[T](Pr[T](σ)))

class FormalizedSigma1Completeness extends Arithmetic α where
  FS1C : ∀ {σ}, ⊢ₐ[T] (σ ⇒ₐ Pr[T](σ))



@[simp] def GoedelSentence (G : Sentence α) := ⊢ₐ[T] (G ⇔ₐ ~ₐPr[T](G))

class HasGoedelSentence extends Arithmetic α where 
  hasGoedel : ∃ G, GoedelSentence T G

def existsGoedelSentence {T : Arithmetic α} [HasGoedelSentence T] : ∃ G, GoedelSentence T G := HasGoedelSentence.hasGoedel

/-
lemma HasGoedelSentence_of_HasFixedPoint {T : Arithmetic α} : HasFixedPoint T → HasGoedelSentence T := by 
  intro h;
  exact ⟨(HasFixedPoint.hasFP (λ σ => ~ₐPr[T](σ)))⟩
-/

@[simp] def HenkinSentence (H : Sentence α) := ⊢ₐ[T] (H ⇔ₐ Pr[T](H))

class HasHenkinSentence where 
  hasHenkin : ∃ H, HenkinSentence T H

@[simp] def JeroslowSentence (J : Sentence α) := ⊢ₐ[T] (J ⇔ₐ Pr[T](~ₐJ))

@[simp] def NotJeroslowSentence (NJ : Sentence α) := ⊢ₐ[T] (NJ ⇔ₐ ~ₐPr[T](~ₐNJ))

@[simp] def KreiselSentence (σ : Sentence α) (K : Sentence α) := ⊢ₐ[T] (K ⇔ₐ (Pr[T](K) ⇒ₐ σ))

class HasKreiselSentence extends Arithmetic α where 
  hasKriesel (σ : Sentence α) : ∃ K, KreiselSentence T σ K 
  
def existsKreiselSentence {T : Arithmetic α} [HasKreiselSentence T] : ∀ (σ : Sentence α), ∃ (K : Sentence α), KreiselSentence T σ K := HasKreiselSentence.hasKriesel

/-
lemma HasKreiselSentence_of_HasFixedPoint {T : Arithmetic α} : HasFixedPoint T → HasKreiselSentence T := by 
  intro h;
  exact ⟨λ σ => HasFixedPoint.hasFP (λ π => (Pr[T](π) ⇒ₐ σ))⟩
-/

end Arithmetic

end ModalLogic.Arithmetic