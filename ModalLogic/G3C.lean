import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import ModalLogic.Notations

open Nat Finset Multiset

namespace ModalLogic.G3C

inductive Formula (α : Type u) where
| Var : α → Formula α
| Bot : Formula α
| Imply : Formula α → Formula α → Formula α
deriving DecidableEq, Repr

namespace Formula

variable (φ ψ : Formula α)
variable [DecidableEq α]

instance : HasVar α (Formula α) := ⟨Var⟩
instance : HasBot (Formula α) := ⟨Bot⟩
instance : HasImply (Formula α) := ⟨Imply⟩

@[simp]
def Neg : Formula α := φ ⇒ ⊥
instance : HasNeg (Formula α) := ⟨Neg⟩

def Top : Formula α := ~⊥
instance : HasTop (Formula α) := ⟨Top⟩

def Disj : Formula α := (~φ) ⇒ ψ
instance : HasDisj (Formula α) := ⟨Disj⟩

def Conj : Formula α := ~((~φ) ⋎ (~ψ))
instance : HasConj (Formula α) := ⟨Conj⟩

def Equiv : Formula α := (φ ⇒ ψ) ⋏ (ψ ⇒ φ)
instance : HasEquiv (Formula α) := ⟨Equiv⟩

def size : Formula α → Nat
| Var _ => 1
| Bot => 1
| Imply φ ψ => 1 + φ.size + ψ.size

def sub : Formula α → Finset (Formula α)
| Imply φ ψ => (φ.sub) ∪ (ψ.sub) ∪ {φ ⇒ ψ}
| φ => {φ}

def vars : Formula α → Finset α
| Var p => {p}
| Bot => ∅
| Imply φ ψ => (φ.vars) ∪ (ψ.vars)

def isAtomic : Formula α → Prop
| Var _ => True
| Bot => True
| _ => False

end Formula

open Formula


abbrev Context (α : Type u) := Finset (Formula α)

namespace Context

instance : Coe (Formula α) (Context α) := ⟨singleton⟩

variable {α : Type u} [DecidableEq α]

-- def vars (Γ : Context α) : Finset α := Γ.fold (λ φ vs => vs ∪ φ.vars) ∅

private def cons (φ : Formula α) (Γ : Context α) : Context α := insert φ Γ
notation:75 φ " :: " Γ => cons φ Γ

-- instance : Commutative (Context α) := ⟨λ Γ Δ => by simp⟩

end Context

open Context

structure Sequent (α : Type u) where
  Left  : Context α
  Right : Context α
deriving DecidableEq

namespace Sequent

notation:20 Γ " ⟹ " Δ => Sequent.mk Γ Δ

variable {α : Type u} [DecidableEq α]

end Sequent


variable {α : Type u} [DecidableEq α]

structure Calculus (α : Type u) where
  derive: (Sequent α × ℕ) → Prop
  liftHeight: (h₁ ≤ h₂) → derive ⟨S, h₁⟩ → derive ⟨S, h₂⟩

namespace Calculus

notation "⊢[" 𝓢 "]^{" n "}" S => derive 𝓢 ⟨S, n⟩

def derivable (𝓢 : Calculus α) (S : Sequent α) := ∃ n, ⊢[𝓢]^{n} S
notation "⊢[" 𝓢 "]" S => derivable 𝓢 S

section Rules

structure HasIdProp extends Calculus α where
  IdProp : ∀ {Γ Δ : Context α} {p : α},
    derive ⟨((#p) :: Γ) ⟹ ((#p) :: Δ), 0⟩

structure HasBotL extends Calculus α where
  BotL : ∀ {Γ Δ : Context α},
    derive ⟨(⊥ :: Γ) ⟹ Δ, 0⟩

/-
structure HasImplyL extends Calculus α where
  ImplyL : ∀ {Γ Δ : Context α} {φ ψ : Formula α},
    (derive ⟨Γ ⟹ (φ :: Δ), h₁⟩) ∧ (derive ⟨(ψ :: Γ) ⟹ Δ, h₂⟩) →
    (derive ⟨((φ ⇒ ψ) :: Γ) ⟹ (Δ), (max h₁ h₂) + 1⟩)
-/

structure HasImplyL extends Calculus α where
  ImplyL : ∀ {Γ₁ Δ₁ Γ₂ Δ₂ : Context α} {φ ψ : Formula α},
    (derive ⟨Γ₁ ⟹ (φ :: Δ₁), h₁⟩) ∧ (derive ⟨(ψ :: Γ₂) ⟹ Δ₂, h₂⟩) →
    (derive ⟨((φ ⇒ ψ) :: (Γ₁ ∪ Γ₂)) ⟹ (Δ₁ ∪ Δ₂), (max h₁ h₂) + 1⟩)

structure HasImplyR extends Calculus α where
  ImplyR : ∀ {Γ Δ : Context α} {φ ψ : Formula α},
    (derive ⟨(φ :: Γ) ⟹ (ψ :: Δ), h⟩) →
    (derive ⟨Γ ⟹ ((φ ⇒ ψ) :: Δ), h + 1⟩)

end Rules


section

variable (α : Type u) [DecidableEq α]
structure CalculusCProp extends Calculus α, HasIdProp, HasBotL, HasImplyL, HasImplyR

end

namespace CalculusCProp

variable {α : Type u} [DecidableEq α] {𝓢 : CalculusCProp α}
variable {Γ Δ : Context α} {φ ψ : Formula α}

local notation "⊢[" 𝓢 "]^{" h "}" S => ⊢[toCalculus 𝓢]^{h} S
local notation "⊢[" 𝓢 "]" S => ⊢[toCalculus 𝓢] S

lemma ZeroHeight (h : (⊢[𝓢]^{0} Γ ⟹ Δ)) :
  (∃ (Γ' Δ' : Context α) (p : α), (Γ = (#p) :: Γ') ∧ (Δ = (#p) :: Δ') ∧ ⊢[𝓢]^{0} ((#p) :: Γ') ⟹ ((#p) :: Δ')) ∨
  (∃ (Γ' : Context α), (Γ = (⊥ : Formula α) :: Γ') ∧ ⊢[𝓢]^{0} (⊥ :: Γ') ⟹ Δ)
  := by sorry;

lemma NegL : (⊢[𝓢]^{h} (Γ ⟹ (φ :: Δ))) → (⊢[𝓢]^{h + 1} (((~φ) :: Γ) ⟹ Δ)) := by
  intro d₁;
  have d₂ : ⊢[𝓢]^{0} ((⊥ :: ∅) ⟹ ∅) := 𝓢.BotL;
  have D := ImplyL 𝓢 ⟨d₁, d₂⟩;
  aesop;

lemma Admissible_NegL : (⊢[𝓢] (Γ ⟹ (φ :: Δ))) → (⊢[𝓢] (((~φ) :: Γ) ⟹ Δ)) := by
  intro d;
  have ⟨h, d₁⟩ := d;
  existsi (h + 1);
  exact NegL d₁;

lemma Admissible_IdForm : ⊢[𝓢] ((φ :: Γ) ⟹ (φ :: Δ)) := by
  induction φ with
  | Var p => apply Exists.intro 0; apply 𝓢.IdProp;
  | Bot => apply Exists.intro 0; apply 𝓢.BotL;
  | Imply φ ψ ih₁ ih₂ =>
    have ⟨h₁, d₁⟩ := ih₁;
    have ⟨h₂, d₂⟩ := ih₂;
    have D₁ := 𝓢.ImplyL ⟨d₁, d₂⟩;
    have D₂ := @ImplyR α _ 𝓢 ((max h₁ h₂) + 1) ((φ ⇒ ψ) :: Γ) Δ φ ψ sorry;
    apply Exists.intro (max h₁ h₂ + 2);
    exact D₂;

lemma HPAdmissible_WeakeningLeft : (⊢[𝓢]^{h} (Γ ⟹ Δ)) → (⊢[𝓢]^{h} ((ξ :: Γ) ⟹ Δ)) := by
  intro H;
  induction h with
  | zero =>
    have A := ZeroHeight H;
    cases A with
    | inl ch =>
      have ⟨Γ', Δ', p, ⟨e₁, ⟨e₂, d⟩⟩⟩ := ch;
      rw [e₁, e₂];
      suffices derive 𝓢.toCalculus (((#p) :: (ξ :: Γ')) ⟹ (#p) :: Δ', zero) by sorry;
      apply 𝓢.IdProp;
    | inr ch =>
      have ⟨Γ', ⟨e, d⟩⟩ := ch;
      rw [e];
      suffices derive 𝓢.toCalculus ((⊥ :: (ξ :: Γ')) ⟹ Δ, zero) by sorry;
      apply 𝓢.BotL;
  | succ h ih => sorry;

end CalculusCProp

end Calculus


section Calc

class Calc (α : Type u) [DecidableEq α] where
  derive : (Sequent α × ℕ) → Prop

variable (α : Type u) [DecidableEq α]

inductive PropLogic.derive : (Sequent α × ℕ) → Prop
  | Trivial : derive ⟨Γ ⟹ Δ, h⟩ → derive ⟨Γ ⟹ Δ, h + 1⟩
  | IdProp (Γ Δ) (p : α) :
      derive ⟨(((#p) :: Γ) ⟹ ((#p) :: Δ)), 0⟩
  | BotL (Γ Δ) :
      derive ⟨(⊥ :: Γ) ⟹ Δ, 0⟩
  | ImplyL {Γ₁ Δ₁ Γ₂ Δ₂} {φ ψ : Formula α} :
      derive ⟨Γ₁ ⟹ (φ :: Δ₁), h₁⟩ → derive ⟨(ψ :: Γ₂) ⟹ Δ₂, h₂⟩ →
      derive ⟨((φ ⇒ ψ) :: (Γ₁ ∪ Γ₂)) ⟹ (Δ₁ ∪ Δ₂), (max h₁ h₂) + 1⟩
  | ImplyR {Γ Δ} {φ ψ : Formula α} :
      derive ⟨(φ :: Γ) ⟹ (ψ :: Δ), h⟩ →
      derive ⟨Γ ⟹ ((φ ⇒ ψ) :: Δ), h + 1⟩

namespace PropLogic

open derive

local notation "⊢^{" n "}" S => PropLogic.derive α ⟨S, n⟩

def derivable (S : Sequent α) := ∃ n, ⊢^{n} S
local notation "⊢" S => derivable α S

lemma NegL : (⊢^{h} (Γ ⟹ (φ :: Δ))) → (⊢^{h + 1} (((~φ) :: Γ) ⟹ Δ)) := by
  intro d₁;
  have D := ImplyL d₁ (BotL ∅ ∅);
  aesop;

lemma Admissible_IdForm : ⊢ ((φ :: Γ) ⟹ (φ :: Δ)) := by
  induction φ with
  | Var p => apply Exists.intro 0; apply IdProp;
  | Bot => apply Exists.intro 0; apply BotL;
  | Imply φ ψ ih₁ ih₂ =>
    have ⟨h₁, d₁⟩ := ih₁;
    have ⟨h₂, d₂⟩ := ih₂;
    have D₁ := ImplyL d₁ d₂;
    have D₂ := @ImplyR α _ ((max h₁ h₂) + 1) ((φ ⇒ ψ) :: Γ) Δ φ ψ sorry;
    apply Exists.intro (max h₁ h₂ + 2);
    exact D₂;

lemma HeightPreserving_InvImplyR : (⊢^{h} (Γ ⟹ (φ ⇒ ψ) :: Δ)) → (⊢^{h} ((φ :: Γ) ⟹ (ψ :: Δ))) := by
  intro H;
  induction h with
  | zero => sorry
  | succ h ih => sorry

lemma HeightPreserving_InvImplyL : (⊢^{h} ((φ ⇒ ψ) :: Γ) ⟹ (Δ)) → (⊢^{h} (Γ₁ ⟹ (φ :: Δ₁))) ∧ (⊢^{h} ((ψ :: Γ₂) ⟹ Δ₂)) := by
  intro H;
  induction h with
  | zero => sorry
  | succ h ih => sorry

lemma HeightPreserving_WeakeningLeft : (⊢^{h} (Γ ⟹ Δ)) → (⊢^{h} ((ξ :: Γ) ⟹ Δ)) := by
  intro H;
  induction h with
  | zero =>
    cases H with
    | IdProp Γ Δ p =>
      suffices ⊢^{0} (#p :: ξ :: Γ) ⟹ #p :: Δ by sorry;
      apply IdProp;
    | BotL Γ Δ =>
      suffices ⊢^{0} (⊥ :: ξ :: Γ) ⟹ Δ by sorry;
      apply BotL;
  | succ h ih =>
    cases H with
    | Trivial d => exact Trivial (ih d);
    | ImplyR d => sorry;
    | ImplyL d₁ d₂ => sorry;

inductive deriveWithCut : (Sequent α × ℕ × ℕ) → Prop
  | LiftCut : (derive α ⟨S, h⟩) → (deriveWithCut ⟨S, h, c⟩)
  | Cut {Γ Δ φ}
    (D₁ : deriveWithCut ⟨Γ ⟹ (φ :: Δ), h₁, c₁⟩)
    (D₂ : deriveWithCut ⟨(φ :: Γ) ⟹ Δ, h₂, c₂⟩)
    : deriveWithCut ⟨Γ ⟹ Δ, (max h₁ h₂) + 1, c₁ + c₂ + 1⟩

local notation "⊢^{" n "}_{" c "}" S => deriveWithCut α ⟨S, n, c⟩

lemma toDerive : (⊢^{h}_{0} S) → (⊢^{h} S) := by intro H; cases H; trivial;

lemma reduce : (⊢^{h}_{1} Γ ⟹ Δ) → (⊢^{h} Γ ⟹ Δ) := by
  intro H;
  sorry;

end PropLogic

end Calc

end ModalLogic.G3C
