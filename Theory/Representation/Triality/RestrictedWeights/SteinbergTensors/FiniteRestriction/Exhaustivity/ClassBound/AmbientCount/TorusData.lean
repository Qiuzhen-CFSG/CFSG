module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Passage

/-!
# Torus data for the ambient D4 class count

The Weyl group is that of the standard D4 root pairing, and it acts on the
points of `S.torus`. The simple-reflection character equations refer to the
actual characters `S.weight`; the graph-field character equation uses the
same arm cycle as `S.diagram_root`. The point equation links the torus map
to `ClassBound.graphFieldEnd`, in the ambient algebraic point group.

This is an intermediate contract, not an asserted consequence of `Geometry`.
Its construction and the finite twisted-kernel calculation are independent
inputs to the ambient counting assembly. In particular no conjugacy-class
count or representation classification is assumed here.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, §§11 and 14.8--14.9.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight

abbrev Weyl := (typeDRootPairing 2).weylGroup
/-- A finite root system has a finite Weyl group. -/
instance : Fintype Weyl := @Fintype.ofFinite _ (weylGroup_finite _)

universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The actual torus and its D4 Weyl action, with character formulas fixing
both the simple reflections and the graph-field map. No count is assumed. -/
structure TorusData (S : Geometry K) (n : ℕ) where
  action : MulAction Weyl (Variety.Point S.torus.carrierVariety)
  map : Variety.Point S.torus.carrierVariety → Variety.Point S.torus.carrierVariety
  map_ambient : ∀ t, S.torus.includePoint (map t) =
    graphFieldEnd S n (S.torus.includePoint t)
  conjugate_iff : letI := action
    ∀ t u : Variety.Point S.torus.carrierVariety,
      IsConj (S.torus.includePoint t) (S.torus.includePoint u) ↔ ∃ w : Weyl, w • t = u
  semisimple_conjugate : ∀ x : Variety.Point K, IsSemisimpleElement K x →
    ∃ t : Variety.Point S.torus.carrierVariety, IsConj x (S.torus.includePoint t)
  reflection_weight : letI := action
    ∀ (i : Fin 4) (a : Weight) (t : Variety.Point S.torus.carrierVariety),
      (S.weight (Multiplicative.ofAdd a)).pointCharacter
        ((RootPairing.weylGroup.ofIdx (typeDRootPairing 2) (typeDSimpleRootIndex 2 i)) • t) =
      (S.weight (Multiplicative.ofAdd (reflection i a))).pointCharacter t
  map_weight : ∀ (a : Weight) (t : Variety.Point S.torus.carrierVariety),
    (S.weight (Multiplicative.ofAdd a)).pointCharacter (map t) =
      (S.weight (Multiplicative.ofAdd (a ∘ typeD4DiagramPermutation))).pointCharacter t ^ (2 ^ n)

variable {S : Geometry K} {n : ℕ}

/-- The literal torus equation, before passing to Weyl or ambient classes. -/
def TwistedKernel (D : TorusData S n) (w : Weyl) :=
  letI := D.action
  {t : Variety.Point S.torus.carrierVariety // D.map t = w • t}

/-- Sum of the sizes of the actual twisted torus kernels. -/
def kernelTotal (D : TorusData S n) : ℕ := ∑ w : Weyl, Nat.card (TwistedKernel D w)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount
