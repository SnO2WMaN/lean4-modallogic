import Modallogic.Normal.Formula
import Mathlib.Logic.Basic

namespace Modallogic.Normal

structure KripkeFrame (α : Type) where
  World : α → Prop
  Relation : α → α → Prop

namespace KripkeFrame

def IsWorld (F : KripkeFrame α) (w : α) := F.World w
def IsRelation (F : KripkeFrame α) (w v : α) := (F.IsWorld w) ∧ (F.IsWorld v) ∧ (F.Relation w v)

end KripkeFrame

def Valuation (α : Type) := α → Prop

structure KripkeModel (α β : Type) where
  Frame : KripkeFrame α
  Valuation : Valuation β

namespace KripkeModel

def IsWorld (M : KripkeModel α β) := M.Frame.IsWorld
def IsRelation (M : KripkeModel α β) := M.Frame.IsRelation

end KripkeModel

def Satisfy (M : KripkeModel α β) (w : α) : Formula β → Prop
| #p => (M.IsWorld w) ∧ (M.Valuation p)
| ⊥ₘ => false
| φ →ₘ ψ => (Satisfy M w φ) → (Satisfy M w ψ)
| □φ => ∀ v, (M.IsRelation w v) → (Satisfy M v φ)

notation M "," w "⊨ₘ" φ => (Satisfy M w φ)
notation M "," w "⊭ₘ" φ => ¬(Satisfy M w φ)

namespace Satisfy

variable (M : KripkeModel α β) (w v : α) (p : β) (φ ψ : Formula β)

@[simp] theorem var_iff : (M,w ⊨ₘ #p) ↔ (M.IsWorld w ∧ M.Valuation p) := by simp [Satisfy]
@[simp] theorem bot_iff : (M,w ⊨ₘ ⊥ₘ) ↔ false := by simp [Satisfy];
@[simp] theorem imp_iff : (M,w ⊨ₘ φ →ₘ ψ) ↔ (Satisfy M w φ → Satisfy M w ψ) := by simp [Satisfy];
@[simp] theorem box_iff : (M,w ⊨ₘ □φ) ↔ (∀ v, M.IsRelation w v → Satisfy M v φ) := by simp [Satisfy];

@[simp] theorem not_iff : (M,w ⊨ₘ ¬ₘφ) ↔ (M,w ⊭ₘ φ) := by simp [Satisfy];
@[simp] theorem not_not_iff : (M,w ⊨ₘ ¬ₘ¬ₘφ) ↔ (M,w ⊨ₘ φ) := by simp [Satisfy.not_iff];

@[simp] theorem top_iff : (M,w ⊨ₘ ⊤ₘ) ↔ true := by simp [Satisfy];

@[simp]
theorem or_iff  : (M,w ⊨ₘ φ ∨ₘ ψ) ↔ ((M,w ⊨ₘ φ) ∨ (M,w ⊨ₘ ψ)) := by
  apply Iff.intro
  . simp [Formula.or]; simp [Formula.not];
    exact or_iff_not_imp_left.mpr
  . simp [Formula.or]; simp [Formula.not];
    exact or_iff_not_imp_left.mp
@[simp] theorem or_comm  : (M,w ⊨ₘ φ ∨ₘ ψ) ↔ (M,w ⊨ₘ ψ ∨ₘ φ) := by simp [Satisfy.or_iff]; exact Or.comm;
@[simp] theorem or_assoc : (M,w ⊨ₘ (φ ∨ₘ ψ) ∨ₘ χ) ↔ (M,w ⊨ₘ φ ∨ₘ (ψ ∨ₘ χ)) := by simp [Satisfy.or_iff]; exact _root_.or_assoc;

@[simp]
theorem and_iff : (M,w ⊨ₘ φ ∧ₘ ψ) ↔ ((M,w ⊨ₘ φ) ∧ (M,w ⊨ₘ ψ)) := by
  apply Iff.intro
  . simp [Formula.and]
    exact and_iff_not_or_not.mpr
  . intro h
    simp [Formula.and]
    exact and_iff_not_or_not.mp h
@[simp] theorem and_comm : (M,w ⊨ₘ φ ∧ₘ ψ) ↔ (M,w ⊨ₘ ψ ∧ₘ φ) := by simp [Satisfy.and_iff]; exact And.comm;
@[simp] theorem and_assoc : (M,w ⊨ₘ (φ ∧ₘ ψ) ∧ₘ χ) ↔ (M,w ⊨ₘ φ ∧ₘ (ψ ∧ₘ χ)) := by simp [Satisfy.and_iff]; exact _root_.and_assoc;

theorem iff_iff : (M,w ⊨ₘ φ ↔ₘ ψ) ↔ ((M,w ⊨ₘ φ) ↔ (M,w ⊨ₘ ψ)) := by
  apply Iff.intro
  . intro h
    simp [Formula.iff] at h
    exact iff_def.mpr h
  . intro h
    simp [Formula.iff]
    exact iff_def.mp h

theorem dia_iff : (M,w ⊨ₘ ◇φ) ↔ (∃ v, (M.IsRelation w v) ∧ (M,w ⊨ₘ φ)) := by
  apply Iff.intro
  . intro h
    simp [Formula.dia] at h
    sorry
  . intro h
    simp [Formula.dia]
    sorry

end Satisfy

def Valid (M : KripkeModel α β) (φ : Formula β) := ∀ w, (M, w ⊨ₘ φ)
notation M "⊨" φ => Valid M φ
notation M "⊭" φ => ¬(Valid M φ)
