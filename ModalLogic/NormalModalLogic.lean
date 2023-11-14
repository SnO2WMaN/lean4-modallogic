import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Fold
import ModalLogic.Notations

open Nat Finset

namespace ModalLogic.NormalModalLogic

inductive Formula (α : Type u) where
| Var : α → Formula α
| Bot : Formula α
| Imply : Formula α → Formula α → Formula α
| Box : Formula α → Formula α
deriving DecidableEq, Repr

namespace Formula

variable (φ ψ : Formula α)
variable [DecidableEq α]

instance : HasVar α (Formula α) := ⟨Var⟩
instance : HasBot (Formula α) := ⟨Bot⟩
instance : HasImply (Formula α) := ⟨Imply⟩
instance : HasBox (Formula α) := ⟨Box⟩

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

def unbox : Formula α → Formula α
| Box φ => φ
| _ => φ

def size : Formula α → Nat
| Var _ => 1
| Bot => 1
| Imply φ ψ => 1 + φ.size + ψ.size
| Box φ => 1 + φ.size

def sub : Formula α → Finset (Formula α)
| Imply φ ψ => (φ.sub) ∪ (ψ.sub) ∪ {φ ⇒ ψ}
| Box φ => (φ.sub) ∪ {□φ}
| φ => {φ}

def vars : Formula α → Finset α
| Var p => {p}
| Bot => ∅
| Imply φ ψ => (φ.vars) ∪ (ψ.vars)
| Box φ => φ.vars

def isAtomic : Formula α → Prop
| Var _ => True
| Bot => True
| _ => False

def isBoxed : Formula α → Prop
| Box _ => True
| _ => False

instance : @DecidablePred (Formula α) isBoxed := by
  intro φ;
  cases φ <;> simp [isBoxed];
  repeat (first | exact decidableFalse | exact decidableTrue);

end Formula

abbrev Context (α : Type u) := Finset (Formula α)

namespace Context

instance : Coe (Formula α) (Context α) := ⟨singleton⟩

variable {α : Type u} [DecidableEq α]

@[simp]
private def joinFormula (Γ : Context α) (φ : Formula α) : Context α := insert φ Γ
notation Γ " :: " φ => joinFormula Γ φ

@[simp]
private def joinContext (Γ₁ Γ₂ : Context α) : Context α := Γ₁ ∪ Γ₂
notation Γ₁ " ++ " Γ₂ => joinContext Γ₁ Γ₂

@[simp]
lemma simpDupl {Γ : Context α} : (Γ ++ Γ) = Γ := by simp;

def Box (Γ : Context α) : Context α := Γ.image (Formula.Box)
prefix:65 "□" => Box

-- def vars (Γ : Context α) : Finset α := Γ.fold (λ φ vs => vs ∪ φ.vars) ∅

def boxedFormulae (Γ : Context α) : Finset (Formula α) := Γ.filter Formula.isBoxed

-- def XBox (Γ : Context α) : Finset (Finset (Formula α)) := Γ.image (λ γ => [γ, □γ])

end Context


structure Sequent (α : Type u) where
  Left  : Context α
  Right : Context α
deriving DecidableEq

namespace Sequent

notation Γ " ⟹ " Δ => Sequent.mk Γ Δ

variable {α : Type u} [DecidableEq α]

@[simp]
lemma rmDuplContextInLeft {Γ Δ : Context α} : ((Γ ++ Γ) ⟹ Δ) = (Γ ⟹ Δ) := by simp

@[simp]
lemma rmDuplContextInRight {Γ Δ : Context α} : (Γ ⟹ (Δ ++ Δ)) = (Γ ⟹ Δ) := by simp

end Sequent


variable {α : Type u} [DecidableEq α]

structure Calculus (α : Type u) where
  derive: (Sequent α × ℕ) → Prop

namespace Calculus

notation "⊢[" 𝓢 "]^{" n "}" S => derive 𝓢 ⟨S, n⟩

def derivable (𝓢 : Calculus α) (S : Sequent α) := ∃ n, ⊢[𝓢]^{n} S
notation "⊢[" 𝓢 "]" S => derivable 𝓢 S

section Rules

structure HasIdProp extends Calculus α where
  IdProp : ∀ {Γ Δ : Context α} {p : α},
    derive ⟨(Γ :: #p) ⟹ (Δ :: #p), 0⟩

structure HasBotL extends Calculus α where
  BotL : ∀ {Γ Δ : Context α},
    derive ⟨(Γ :: ⊥) ⟹ Δ, 0⟩

structure HasImplyL extends Calculus α where
  ImplyL : ∀ {Γ₁ Δ₁ Γ₂ Δ₂ : Context α} {φ ψ : Formula α},
    (derive ⟨Γ₁ ⟹ (Δ₁ :: φ), h₁⟩) ∧ (derive ⟨(Γ₂ :: ψ) ⟹ Δ₂, h₂⟩) →
    (derive ⟨(Γ₁ ++ Γ₂ :: φ ⇒ ψ) ⟹ (Δ₁ ++ Δ₂), (max h₁ h₂) + 1⟩)

structure HasImplyR extends Calculus α where
  ImplyR : ∀ {Γ Δ : Context α} {φ ψ : Formula α},
    (derive ⟨(Γ :: φ) ⟹ (Δ :: ψ), h⟩) →
    (derive ⟨Γ ⟹ (Δ :: φ ⇒ ψ), h + 1⟩)

structure HasGLBoxR extends Calculus α where
  GLBoxR : ∀ {Γ : Context α} {φ : Formula α},
    (derive ⟨(Γ ++ □Γ :: □φ) ⟹ φ, h⟩) →
    (derive ⟨(□Γ) ⟹ (□φ), h + 1⟩)

end Rules


section

variable (α : Type u) [DecidableEq α]
structure CalculusGL extends Calculus α, HasIdProp, HasBotL, HasImplyL, HasImplyR, HasGLBoxR

end


namespace CalculusGL

variable {α : Type u} [DecidableEq α] {𝓢 : CalculusGL α}
variable {Γ Δ : Context α} {φ ψ : Formula α} {h h₁ h₂ : ℕ}

local notation "⊢[" 𝓢 "]^{" h "}" S => ⊢[toCalculus 𝓢]^{h} S
local notation "⊢[" 𝓢 "]" S => ⊢[toCalculus 𝓢] S

lemma ZeroHeight (h : (⊢[𝓢]^{0} Γ ⟹ Δ)) :
  (∃ (Γ' Δ' : Context α) (p : α), (Γ = Γ' :: #p) ∧ (Δ = Δ' :: #p) ∧ ⊢[𝓢]^{0} (Γ' :: #p) ⟹ (Δ' :: #p)) ∨
  (∃ (Γ' : Context α), (Γ = Γ' :: ⊥) ∧ ⊢[𝓢]^{0} (Γ' :: ⊥) ⟹ Δ)
  := by sorry;

lemma Admissible_IdForm : ⊢[𝓢] ((Γ :: φ) ⟹ (Δ :: φ)) := by
  induction φ with
  | Var p => apply Exists.intro 0; apply 𝓢.IdProp;
  | Bot => apply Exists.intro 0; apply 𝓢.BotL;
  | Imply φ ψ ih₁ ih₂ =>
    have ⟨h₁, d₁⟩ := ih₁;
    have ⟨h₂, d₂⟩ := ih₂;
    have D₁ := by exact @ImplyL α _ 𝓢 h₁ h₂ (Γ :: φ) Δ Γ (Δ :: ψ) φ ψ ⟨d₁, d₂⟩;
    simp at D₁;
    -- have A : derive 𝓢.toCalculus (((Γ :: φ) :: φ ⇒ ψ) ⟹ (Δ :: ψ), max h₁ h₂ + 1) := D₁;
    have D₂ := @ImplyR α _ 𝓢 ((max h₁ h₂) + 1);
    apply Exists.intro (max h₁ h₂ + 2);
    sorry
  | Box φ ih =>
    have ⟨h, d⟩ := ih;
    apply Exists.intro (h + 1);
    sorry;

lemma HPAdmissible_WeakeningLeft : (⊢[𝓢]^{h} (Γ ⟹ Δ)) → (⊢[𝓢]^{h} ((Γ :: ξ) ⟹ Δ)) := by
  intro H;
  induction h with
  | zero =>
    have A := ZeroHeight H;
    cases A with
    | inl ch =>
      have ⟨Γ', Δ', p, ⟨e₁, ⟨e₂, d⟩⟩⟩ := ch;
      rw [e₁, e₂];
      suffices derive 𝓢.toCalculus (((Γ' :: ξ) :: #p) ⟹ Δ' :: #p, 0) by sorry;
      apply 𝓢.IdProp;
    | inr ch =>
      have ⟨Γ', ⟨e, d⟩⟩ := ch;
      rw [e];
      suffices derive 𝓢.toCalculus (((Γ' :: ξ) :: ⊥) ⟹ Δ, 0) by sorry;
      apply 𝓢.BotL;
  | succ h ih => sorry;

end CalculusGL

end Calculus

end ModalLogic.NormalModalLogic
