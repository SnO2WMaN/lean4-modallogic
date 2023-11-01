import ModalLogic.SupplymentSimp
import ModalLogic.Notations
import ModalLogic.PropositionalLogic.Axioms

open Nat Finset
open ModalLogic.PropositionalLogic

namespace ModalLogic.PropositionalLogic.SequentCalculus

inductive Formula (α : Type u) where
| Var : α → Formula α
| Bot : Formula α
| Conj : Formula α → Formula α → Formula α
| Disj : Formula α → Formula α → Formula α
| Imply : Formula α → Formula α → Formula α
deriving DecidableEq, Repr

namespace Formula

instance : HasVar α (Formula α) := ⟨Var⟩
instance : HasBot (Formula α) := ⟨Bot⟩
instance : HasConj (Formula α) := ⟨Conj⟩
instance : HasDisj (Formula α) := ⟨Disj⟩
instance : HasImply (Formula α) := ⟨Imply⟩

def complexity : Formula α → ℕ
| Var _ => 0
| Bot => 0
| Conj φ ψ => max (φ.complexity) (ψ.complexity) + 1
| Disj φ ψ => max (φ.complexity) (ψ.complexity) + 1
| Imply φ ψ => max (φ.complexity) (ψ.complexity) + 1

end Formula

structure Sequent (α : Type u) [DecidableEq α] where
  antecedent : Finset (Formula α)
  consequent : Finset (Formula α)

notation Γ " ⟹ " Δ => Sequent.mk Γ Δ

structure Calculus (α : Type u) [DecidableEq α] where
  infer : (Sequent α × ℕ) → Prop
  LongerInference : (k ≤ l) → infer ⟨S, k⟩ → infer ⟨S, l⟩

namespace Calculus

attribute [simp] LongerInference

variable {α : Type u} [DecidableEq α]
variable (𝓖 : Calculus α) (S : Sequent α) (k n : ℕ)

notation "⊢[" 𝓖 "]^{" n "} " S => infer 𝓖 ⟨S, n⟩

def inferable : Prop := ∃ k, ⊢[𝓖]^{k} S
notation "⊢[" 𝓖 "] " S => inferable 𝓖 S

/-
instance : Coe (⊢[𝓖]^{k} S) (⊢[𝓖] S) where
  coe := by
    intro H;
    existsi k;
    exact H;
-/

def inferableUnder (n : ℕ) : Prop := ∃ k, k ≤ n ∧ ⊢[𝓖]^{k} S
notation "⊢[" 𝓖 "]≤{" n "}" S => inferableUnder 𝓖 S n

end Calculus


section Rules

open Calculus

variable {α : Type u} [DecidableEq α]
variable (𝓖 : Calculus α)

class HasInit extends Calculus α where
  Init {p : α} : ⊢[𝓖]^{0} (Γ ∪ {#p}) ⟹ (Δ ∪ {#p})
attribute [simp] HasInit.Init

lemma HasInit.Init' [HasInit 𝓖] {p : α} : ⊢[𝓖]^{k} (Γ ∪ {#p}) ⟹ (Δ ∪ {#p}) := 𝓖.LongerInference (by simp) Init

lemma HasInit.Init_inferable [HasInit 𝓖] {p : α} : ⊢[𝓖] (Γ ∪ {#p}) ⟹ (Δ ∪ {#p}) := by
  existsi 0;
  apply HasInit.Init;

class HasLeftBot extends Calculus α where
  LeftBot : ⊢[𝓖]^{0} (Γ ∪ {(⊥ : Formula α)}) ⟹ Δ
attribute [simp] HasLeftBot.LeftBot

lemma HasLeftBot.LeftBot' [HasLeftBot 𝓖] : ⊢[𝓖]^{k} (Γ ∪ {(⊥ : Formula α)}) ⟹ Δ := 𝓖.LongerInference (by simp) LeftBot

lemma HasLeftBot.LeftBot_inferable [HasLeftBot 𝓖] : ⊢[𝓖] (Γ ∪ {(⊥ : Formula α)}) ⟹ Δ  := by
  existsi 0;
  apply HasLeftBot.LeftBot;

class HasLeftConj extends Calculus α where
  LeftConj {k} : (⊢[𝓖]^{k} (Γ ∪ {φ, ψ}) ⟹ Δ) → (⊢[𝓖]^{k + 1} (Γ ∪ {φ ⋏ ψ}) ⟹ Δ)
attribute [simp] HasLeftConj.LeftConj

class HasRightConj extends Calculus α where 
  RightConj {k₁ k₂} : ((⊢[𝓖]^{k₁} Γ₁ ⟹ (Δ₁ ∪ {φ})) ∧ (⊢[𝓖]^{k₂} Γ₂ ⟹ (Δ₂ ∪ {ψ}))) → (⊢[𝓖]^{(max k₁ k₂) + 1} (Γ₁ ∪ Γ₂) ⟹ (Δ₁ ∪ Δ₂ ∪ {φ ⋏ ψ}))
attribute [simp] HasRightConj.RightConj

class HasLeftDisj extends Calculus α where
  LeftDisj : ((⊢[𝓖]^{k₁} (Γ₁ ∪ {φ}) ⟹ Δ₁) ∧ (⊢[𝓖]^{k₂} (Γ₂ ∪ {ψ}) ⟹ Δ₂)) → (⊢[𝓖]^{(max k₁ k₂) + 1} (Γ₁ ∪ Γ₂ ∪ {φ ⋎ ψ}) ⟹ (Δ₁ ∪ Δ₂))
attribute [simp] HasLeftDisj.LeftDisj

class HasRightDisj extends Calculus α where
  RightDisj {k} : (⊢[𝓖]^{k} Γ ⟹ (Δ ∪ {φ, ψ})) → (⊢[𝓖]^{k + 1} Γ ⟹ (Δ ∪ {φ ⋎ ψ}))
attribute [simp] HasRightDisj.RightDisj

class HasLeftImpl extends Calculus α where
  LeftImpl {k₁ k₂} : ((⊢[𝓖]^{k₁} Γ₁ ⟹ (Δ₁ ∪ {φ})) ∧ (⊢[𝓖]^{k₂} (Γ₂ ∪ {ψ}) ⟹ Δ₂)) → (⊢[𝓖]^{(max k₁ k₂) + 1} ((Γ₁ ∪ Γ₂) ∪ {φ ⇒ ψ}) ⟹ (Δ₁ ∪ Δ₂))
attribute [simp] HasLeftImpl.LeftImpl

class HasRightImpl extends Calculus α where
  RightImpl {φ ψ Γ Δ k} : (⊢[𝓖]^{k} (Γ ∪ {φ}) ⟹ (Δ ∪ {ψ})) → (⊢[𝓖]^{k + 1} Γ ⟹ (Δ ∪ {φ ⇒ ψ}))
attribute [simp] HasRightImpl.RightImpl

class ClassicalCalculus extends Calculus α,
  (HasInit 𝓖), (HasLeftBot 𝓖), 
  (HasLeftConj 𝓖), (HasRightConj 𝓖), 
  (HasLeftDisj 𝓖), (HasRightDisj 𝓖), 
  (HasLeftImpl 𝓖), (HasRightImpl 𝓖)

end Rules


section Admissible

variable {α : Type u} [DecidableEq α] 
variable {𝓖 : Calculus α} [ClassicalCalculus 𝓖]
variable {Γ Δ : Finset (Formula α)} {φ ψ : Formula α}

lemma admissible_InitFormula : ⊢[𝓖] (Γ ∪ {φ}) ⟹ (Δ ∪ {φ}) := by
  induction φ with
  | Var p => apply HasInit.Init_inferable;
  | Bot => apply HasLeftBot.LeftBot_inferable;
  | Conj φ ψ IH₁ IH₂ => 
    have ⟨k₁, h₁⟩ := IH₁;
    have ⟨k₂, h₂⟩ := IH₂;
    have ⟨k₃, h₃⟩ : ⊢[𝓖] (Γ ∪ {φ, ψ}) ⟹ (Δ ∪ {φ ⋏ ψ}) := by 
      have := HasRightConj.RightConj ⟨h₁, h₂⟩;
      existsi (max k₁ k₂) + 1;
      simp_all only [Finset.union_idempotent];
      -- rw [Finset.union_comm];
      -- repeat rw [←union_assoc] at this;
      sorry;
    have ⟨k₄, h₄⟩ : ⊢[𝓖] (Γ ∪ {φ ⋏ ψ}) ⟹ (Δ ∪ {φ ⋏ ψ}) := by 
      have := HasLeftConj.LeftConj h₃;
      existsi k₃ + 1;
      exact this;
    existsi k₄;
    exact h₄;
  | Disj φ ψ IH₁ IH₂ =>
    have ⟨k₁, h₁⟩ := IH₁; 
    have ⟨k₂, h₂⟩ := IH₂;
    have ⟨k₃, h₃⟩ : ⊢[𝓖] (Γ ∪ {φ ⋎ ψ}) ⟹ (Δ ∪ {φ, ψ}) := by  
      have := HasLeftDisj.LeftDisj ⟨h₁, h₂⟩;
      existsi (max k₁ k₂) + 1;
      sorry;
    have ⟨k₄, h₄⟩ : ⊢[𝓖] (Γ ∪ {φ ⋎ ψ}) ⟹ (Δ ∪ {φ ⋎ ψ}) := by
      have := HasRightDisj.RightDisj h₃;
      existsi k₃ + 1;
      exact this;
    existsi k₄;
    exact h₄;
  | Imply φ ψ IH₁ IH₂ =>
    have ⟨k₁, h₁⟩ := IH₁; 
    have ⟨k₂, h₂⟩ := IH₂;
    have ⟨k₃, h₃⟩ : ⊢[𝓖] (Γ ∪ {φ ⇒ ψ} ∪ {φ}) ⟹ (Δ ∪ {ψ}) := by  
      have := HasLeftImpl.LeftImpl ⟨h₁, h₂⟩;
      existsi (max k₁ k₂) + 1;
      sorry
    have ⟨k₄, h₄⟩ : ⊢[𝓖] (Γ ∪ {φ ⇒ ψ}) ⟹ (Δ ∪ {φ ⇒ ψ}) := by
      have := @HasRightImpl.RightImpl α _ 𝓖 _ φ ψ (Γ ∪ {φ ⇒ ψ}) Δ k₃ h₃;
      existsi k₃ + 1;
      exact this;
    existsi k₄;
    exact h₄;

lemma HPAdmissible_InversedLeftConj : (⊢[𝓖]^{k} (Γ ∪ {φ ⋏ ψ}) ⟹ Δ) → (⊢[𝓖]^{k} (Γ ∪ {φ, ψ}) ⟹ Δ) := by
  intro H;
  induction k with
  | zero =>
    sorry
  | succ k IH =>
    sorry

lemma HPAdmissible_LeftWeakening (Γ') : (⊢[𝓖]^{k} Γ ⟹ Δ) → (⊢[𝓖]^{k} (Γ ∪ Γ') ⟹ Δ) := by
  intro H;
  induction k with
  | zero =>
    simp at *;
    sorry
  | succ k IH =>
    sorry

lemma HPAdmissible_LeftWeakening' (φ) : (⊢[𝓖]^{k} Γ ⟹ Δ) → (⊢[𝓖]^{k} (Γ ∪ {φ}) ⟹ Δ) := HPAdmissible_LeftWeakening {φ} 

lemma HPAdmissible_RightWeakening (Δ') : (⊢[𝓖]^{k} Γ ⟹ Δ) → (⊢[𝓖]^{k} Γ ⟹ (Δ ∪ Δ')) := by
  intro H;
  induction k with
  | zero =>
    sorry
  | succ k IH =>
    sorry 
 
lemma HPAdmissible_RightWeakening' (φ) : (⊢[𝓖]^{k} Γ ⟹ Δ) → (⊢[𝓖]^{k} Γ ⟹ Δ ∪ {φ}) := HPAdmissible_RightWeakening {φ} 

end Admissible


section CalculusWithCut

variable {α : Type u} [DecidableEq α]

structure CalculusWithCut (α : Type u) [DecidableEq α] extends Calculus α where
  inferWithCut : (Sequent α × (ℕ × ℕ)) → Prop
  cutComp : infer ⟨S, k⟩ ↔ inferWithCut ⟨S, ⟨k, 0⟩⟩
  Cut φ : ((inferWithCut ⟨Γ₁ ⟹ (Δ₁ ∪ {φ}), ⟨k₁, c₁⟩⟩) ∧ (inferWithCut ⟨Γ₂ ⟹ (Δ₂ ∪ {φ}), ⟨k₂, c₂⟩⟩)) → (inferWithCut ⟨(Γ₁ ∪ Γ₂) ⟹ (Δ₁ ∪ Δ₂), ⟨(max k₁ k₂) + 1, (c₁ + c₂ + 1)⟩⟩)

notation "⊢ᶜ[" 𝓖c "]^{" n "}_{" c "} " S => CalculusWithCut.inferWithCut 𝓖c ⟨S, ⟨n, c⟩⟩

def CalculusWithCut.inferable (𝓖c : CalculusWithCut α) (h S) := ∃ c, ⊢ᶜ[𝓖c]^{h}_{c} S 

notation "⊢ᶜ[" 𝓖c "]^{" h "} " S => CalculusWithCut.inferable 𝓖c h S

class ClassicalCalculusWithCut (𝓖c : CalculusWithCut α) extends CalculusWithCut α, (ClassicalCalculus 𝓖c.toCalculus)

end CalculusWithCut


section CutElimination

open CalculusWithCut

variable {α : Type u} [DecidableEq α] {𝓖 𝓖c : Calculus α}
variable {𝓖c : CalculusWithCut α} [ClassicalCalculusWithCut 𝓖c]
variable {Γ Δ : Finset (Formula α)} {k : ℕ}

lemma CutFrom : (⊢ᶜ[𝓖c]^{k}_{1} (Γ₁ ∪ Γ₂) ⟹ (Δ₁ ∪ Δ₂)) → (∃ φ, (⊢[𝓖c.toCalculus]^{k} (Γ₁ ⟹ (Δ₁ ∪ {φ}))) ∧ (⊢[𝓖c.toCalculus]^{k} ((Γ₂ ∪ {φ}) ⟹ Δ₂))) := by 
  intro H;
  sorry;

lemma ReducingCutTimes : (inferWithCut 𝓖c ⟨((Γ₁ ∪ Γ₂) ⟹ (Δ₁ ∪ Δ₂)), k, c + 1⟩) → (inferWithCut 𝓖c ⟨((Γ₁ ∪ Γ₂) ⟹ (Δ₁ ∪ Δ₂)), l, c⟩) := by 
  intro H;
  induction c with
  | zero => 
    simp at *;
    have ⟨φ, ⟨Hl, Hr⟩⟩ := CutFrom H;
    have hl₁ := HPAdmissible_RightWeakening Δ₂ $ HPAdmissible_LeftWeakening (Γ₂ ∪ {φ}) Hl;
    have hr₁ := HPAdmissible_LeftWeakening Γ₁ $ HPAdmissible_RightWeakening (Δ₁ ∪ {φ}) Hr;
    apply (cutComp 𝓖c).mp;
    sorry;
  | succ c IH =>
    simp at *;
    sorry;
  
lemma ReducingCutFormulaComplexity {φ : Formula α} (h : True) : ∃ (ψ : Formula α), (ψ.complexity < φ.complexity) := by sorry

theorem EliminateCut : (⊢ᶜ[𝓖c]^{k} (Γ₁ ∪ Γ₂) ⟹ (Δ₁ ∪ Δ₂)) → (⊢[𝓖c.toCalculus]^{k} (Γ₁ ∪ Γ₂) ⟹ (Δ₁ ∪ Δ₂)) := by
  intro H;
  have ⟨c, H⟩ := H;
  induction c with
  | zero => exact (cutComp 𝓖c).mpr H;
  | succ c IH => exact IH (ReducingCutTimes H);

end CutElimination

end ModalLogic.PropositionalLogic.SequentCalculus