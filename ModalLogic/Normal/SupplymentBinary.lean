variable {α : Type u} (r : α → α → Prop)

local infix:50 " ≺ " => r

def _root_.Serial := ∀ w, ∃ v, w ≺ v

def _root_.Euclidean := ∀ w v u, (w ≺ v ∧ w ≺ u) → v ≺ u 
