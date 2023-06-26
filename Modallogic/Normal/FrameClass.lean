import Modallogic.Normal.Semantics

namespace Modallogic.Normal.FrameClass

variable (F : KripkeFrame α)

class T := (reflexive : ∀ w, F.IsRelation w w)
class B := (symmetric : ∀ x y, F.IsRelation x y → F.IsRelation y x)
class Four := (transitive : ∀ x y z, (F.IsRelation x y ∧ F.IsRelation y z) → F.IsRelation x z)
class Five := (euclidean : ∀ x y z, (F.IsRelation x y ∧ F.IsRelation x z) → F.IsRelation y z)
class D := (successive : ∃ v, ∀ w, F.IsRelation v w)
class DotTwo := (directive : ∀ x y z, (F.IsRelation x y ∧ F.IsRelation x z) → (∃ s, F.IsRelation y s ∨ F.IsRelation z s))
