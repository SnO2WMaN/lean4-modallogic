import Modallogic.Normal.Formula
import Modallogic.Normal.Semantics

namespace Modallogic.Normal.Axioms

variable (φ ψ χ : Formula α)

def Pl1 := (φ →ₘ (ψ →ₘ φ))
theorem Pl1.valid (M : KripkeModel α β) (φ ψ : Formula β) : Valid M (Pl1 φ ψ) := by
  intro w;
  exact fun a _ => a

def Pl2 := ((φ →ₘ (ψ →ₘ χ)) →ₘ ((φ →ₘ ψ) →ₘ (φ →ₘ χ)))
theorem Pl2.valid (M : KripkeModel α β) (φ ψ χ: Formula β) : Valid M (Pl2 φ ψ χ) := by
  intro w;
  exact fun a b c => a c (b c)

def Pl3 := ((¬ₘφ →ₘ ¬ₘψ) →ₘ (ψ →ₘ φ))
theorem Pl3.valid (M : KripkeModel α β) (φ ψ: Formula β) : Valid M (Pl3 φ ψ) := by
  intro w;
  simp [Pl3];
  exact not_imp_not.mp

def K := □(φ →ₘ ψ) →ₘ (□φ →ₘ □ψ)
def T := □φ →ₘ φ
def B := φ →ₘ □◇φ
def Four := □φ →ₘ □□φ
def Five := ◇φ →ₘ □◇φ

def D := □φ →ₘ ◇φ

def DotTwo := ◇□φ →ₘ □◇φ

def L := □(□φ →ₘ φ) →ₘ □φ
