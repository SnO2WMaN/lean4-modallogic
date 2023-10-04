import Mathlib.Data.Finset.Basic

open Finset

namespace ModalLogic.PropositionalLogic

section Symbols

variable (α : Type u)

class HasBot where bot : α
scoped[ModalLogic.PropositionalLogic] notation:70 "⊥" => HasBot.bot

class HasImply where imply : α → α → α
scoped[ModalLogic.PropositionalLogic] infixr:63 " ⇒ " => HasImply.imply

class HasNeg where neg : α → α
scoped[ModalLogic.PropositionalLogic] prefix:64 "~" => HasNeg.neg

class HasNegDef [HasNeg α] [HasBot α] [HasImply α] where 
  NegDef (φ : α) : (~φ) = (φ ⇒ ⊥)
attribute [simp] HasNegDef.NegDef

class HasTop where top : α
scoped[ModalLogic.PropositionalLogic] notation:70 "⊤" => HasTop.top

class HasDisj where disj : α → α → α
scoped[ModalLogic.PropositionalLogic] infixl:62 " ⋎ " => HasDisj.disj

class HasDisjDef [HasDisj α] [HasImply α] [HasNeg α] where 
  DisjDef (φ ψ : α) : (φ ⋎ ψ) = (~φ ⇒ ψ)

class HasConj where conj : α → α → α
scoped[ModalLogic.PropositionalLogic] infixl:62 " ⋏ " => HasConj.conj

class HasConjDef [HasConj α] [HasImply α] [HasNeg α] where 
  ConjDef (φ ψ : α) : (φ ⋏ ψ) = ~(φ ⇒ ~ψ)

class HasEquiv where equiv : α → α → α
scoped[ModalLogic.PropositionalLogic] infixl:61 " ⇔ " => HasEquiv.equiv

class HasEquivDef [HasEquiv α] [HasImply α] [HasConj α] where 
  EquivDef (φ ψ : α) : (φ ⇔ ψ) = ((φ ⇒ ψ) ⋏ (ψ ⇒ φ))
attribute [simp] HasEquivDef.EquivDef

end Symbols

structure ProveSystem (α : Type u) where
  Proves: α → Prop
notation "⊢[" S "] " φ => ProveSystem.Proves S φ
notation "⊬[" S "] " φ => ¬(⊢[S] φ)

/-
namespace ProveSystem

variable {α : Type u} [HasImply α] [HasNeg α] [HasDisj α] [HasConj α] (S : ProveSystem α)

class HasAxiomK where
  AxiomK {φ ψ : α} : (⊢[S] (φ ⇒ ψ ⇒ φ))
attribute [simp] HasAxiomK.AxiomK

class HasAxiomS where
  AxiomS {φ ψ ξ : α} : ⊢[S] ((φ ⇒ (ψ ⇒ ξ)) ⇒ ((φ ⇒ ψ) ⇒ (φ ⇒ ξ)))
attribute [simp] HasAxiomS.AxiomS

class HasAxiomCon₄ where
  AxiomCon₄ {φ ψ : α} : ⊢[S] ((φ ⇒ ψ) ⇒ ((~ψ) ⇒ (~φ)))
attribute [simp] HasAxiomCon₄.AxiomCon₄

class HasAxiomConjIntro where
  AxiomConjIntro {φ ψ : α} : ⊢[S] (φ ⇒ ψ ⇒ (φ ⋏ ψ))

class HasAxiomConjElim where
  AxiomConjElim₁ {φ₁ φ₂ : α} : ⊢[S] (φ₁ ⋏ φ₂) ⇒ φ₁
  AxiomConjElim₂ {φ₁ φ₂ : α} : ⊢[S] (φ₁ ⋏ φ₂) ⇒ φ₂

class HasAxiomDisjIntro where
  AxiomDisjIntro₁ {φ₁ φ₂ : α} : ⊢[S] φ₁ ⇒ (φ₁ ⋎ φ₂)
  AxiomDisjIntro₂ {φ₁ φ₂ : α} : ⊢[S] φ₂ ⇒ (φ₁ ⋎ φ₂)

class HasMP where
  MP {φ ψ : α} : (⊢[S] (φ ⇒ ψ)) → (⊢[S] φ) → (⊢[S] ψ)
attribute [simp] HasMP.MP

end ProveSystem
-/

end ModalLogic.PropositionalLogic

/-
section Syntax

end Syntax

inductive Formula (α : Type u) : Type u
  | Contradiction : (Formula α)
  | Imply : (Formula α) → (Formula α) → (Formula α)
  deriving DecidableEq, Repr

notation "⊥ₚ" => Formula.Contradiction
infixr:73 " ⇒ₚ " => Formula.Imply

abbrev Context (α) := Finset (Formula α)

structure ProveSystem (α) where
  Proves: Formula α → Prop
notation "⊢ₚ[" S "]" => ProveSystem.Proves S

namespace ProveSystem

@[simp]
def Deducts (S : ProveSystem α) (Γ : Context α) (φ : Formula α) := (⊢ₚ[S] φ) ∨ (φ ∈ Γ)
notation Γ " ⊢ₚ[" S "] " φ => ProveSystem.Deducts S Γ φ

@[simp]
lemma deduction_emptyctx : (⊢ₚ[S] φ) ↔ (∅ ⊢ₚ[S] φ) := by aesop;

@[simp]
lemma deduction_weakening : (Γ ⊆ Δ) → (Γ ⊢ₚ[S] φ) → (Δ ⊢ₚ[S] φ) := by
  intro h₁ h₂;
  cases h₂ with
  | inl h₂ => exact Or.inl h₂
  | inr h₂ => exact Or.inr (h₁ h₂)

@[simp]
lemma deducts_by_proves (Γ) : (⊢ₚ[S] φ) → (Γ ⊢ₚ[S] φ) := by
  rw [deduction_emptyctx];
  exact deduction_weakening (by simp);

instance (Γ : Context α) : Coe (⊢ₚ[S] φ) (Γ ⊢ₚ[S] φ) := ⟨deducts_by_proves Γ⟩ 

class HasAxiomK (S : ProveSystem α) where
  AxiomK {φ ψ : Formula α} : (⊢ₚ[S] (φ ⇒ₚ ψ ⇒ₚ φ))

@[simp]
def AxiomK_def {S : ProveSystem α} [HasAxiomK S] {φ ψ : Formula α} : (⊢ₚ[S] (φ ⇒ₚ ψ ⇒ₚ φ)) := HasAxiomK.AxiomK

class HasAxiomS (S : ProveSystem α) where
  AxiomS {φ ψ ξ : Formula α} : ⊢ₚ[S] ((φ ⇒ₚ (ψ ⇒ₚ ξ)) ⇒ₚ ((φ ⇒ₚ ψ) ⇒ₚ (φ ⇒ₚ ξ)))

@[simp]
def AxiomS_def {S : ProveSystem α} [HasAxiomS S] {φ ψ ξ : Formula α} : (⊢ₚ[S] ((φ ⇒ₚ (ψ ⇒ₚ ξ)) ⇒ₚ ((φ ⇒ₚ ψ) ⇒ₚ (φ ⇒ₚ ξ)))) := HasAxiomS.AxiomS

class HasModusPonens (S : ProveSystem α) where
  MP {φ ψ : Formula α} : (⊢ₚ[S] (φ ⇒ₚ ψ)) → (⊢ₚ[S] φ) → (⊢ₚ[S] ψ)

@[simp]
def MP_def {S : ProveSystem α} [HasModusPonens S] {φ ψ : Formula α} : (⊢ₚ[S] (φ ⇒ₚ ψ)) → (⊢ₚ[S] φ) → (⊢ₚ[S] ψ) := HasModusPonens.MP

class HasDeductionTheorem (S : ProveSystem α) where
  DT {Γ} {φ ψ : Formula α} : (Γ ⊢ₚ[S] φ ⇒ₚ ψ) ↔ ((Γ ∪ {φ}) ⊢ₚ[S] ψ)

variable {S : ProveSystem α} [HasModusPonens S] [HasDeductionTheorem S] [HasAxiomK S] [HasAxiomS S]

lemma DeductMP {φ ψ : Formula α} : (Γ ⊢ₚ[S] φ ⇒ₚ ψ) → (Γ ⊢ₚ[S] φ) → (Γ ⊢ₚ[S] ψ) := by
  intro h₁ h₂
  cases h₁ with
  | inl h₁ => 
    cases h₂ with
    | inl h₂ => exact Or.inl (MP_def h₁ h₂)
    | inr h₂ => sorry
  | inr h₁ =>
    cases h₂ with
    | inl h₂ => sorry
    | inr h₂ => sorry

end ProveSystem

end ModalLogic.PropositionalLogic
-/