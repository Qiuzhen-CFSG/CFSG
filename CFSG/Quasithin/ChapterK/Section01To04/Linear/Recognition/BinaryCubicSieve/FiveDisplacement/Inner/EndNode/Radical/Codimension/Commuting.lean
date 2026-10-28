module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension.Certificate

/-!
# Commuting differences for the two end-adjacent radical certificates

Differences of commuting group elements commute as linear operators. This
allows an extractor to start with a radical root, as required to annihilate
the common fixed space, while evaluating it in a different order on a chosen
vector. The exceptional certificates also use root differences of permutation
translates; no action for an unknown root difference is assumed.

Source application: Guralnick–Malle, Classification of 2F-modules II,
Proposition 4.7 step 1, pp.25–26; Aschbacher–Smith K.3.2, pp.454–455.
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Codimension
open Representation
open Representation.SL5TenDimensional.Classification.Separated
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Commutation reorders an extractor without changing its value. -/
theorem difference_commute
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V)
    {g k : SL5TenDimensional.Group} (h : g * k = k * g) (x : V) :
    difference σ g (difference σ k x) = difference σ k (difference σ g x) := by
  simp only [difference, LinearMap.sub_apply, LinearMap.id_apply, map_sub, ← apply_mul, h]
  abel

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Codimension
