module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights.Characters

/-!
# Direct root conjugation with the unchanged positive root groups

The inverted root character and inverted cocharacter preserve all Cartan
integers. The raw equation at an inverse torus point proves the direct equation;
its simple-root exponent is +2. Source: GLS3 1.9.2 and 1.12.1(g), translated
to Steinberg (6.1).
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.LeftWeights
universe u
variable {k : Type u} [Field k]
variable {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}

/-- The root character for direct conjugation on the same root subgroup. -/
def leftRootCharacter (D : RootGroupData K T) (r : D.Root) : TorusWeight T :=
  (D.rootWeight r)⁻¹

theorem leftRootCharacter_morphism (D : RootGroupData K T) (r : D.Root) :
    leftRootCharacter D r = parameterInversion.comp (D.rootWeight r) := rfl

/-- Both ways of inverting a cocharacter agree as regular morphisms. -/
theorem leftCocharacter_eq_torusInversion (h : ClosedSubgroupTorusCocharacter T)
    (hc : ∀ x y : Variety.Point T.carrierVariety, x * y = y * x) :
    leftCocharacter h = (inversion _ hc).comp h := by
  apply Theory.AlgebraicGroup.Morphism.ext
  funext t
  exact map_inv h.onPoints t

theorem direct_root_conjugation (D : RootGroupData K T) (hD : D.IsRealization)
    (r : D.Root) (x : OneParameterParametrization (D.rootSubgroup r).carrierVariety)
    (u : k) (t : Variety.Point T.carrierVariety) :
    T.includePoint t * (D.rootSubgroup r).includePoint (x.value u) * (T.includePoint t)⁻¹ =
      (D.rootSubgroup r).includePoint (x.value ((leftRootCharacter D r).pointCharacter t * u)) :=
  direct_conjugation (hD.2.2.1 r).2 x u t

/-- The Cartan exponent is unchanged for each pair of actual roots. -/
theorem direct_left_coroot_conjugation (D : RootGroupData K T) (hD : D.IsRealization)
    (r s : D.Root) (x : OneParameterParametrization (D.rootSubgroup r).carrierVariety)
    (u : k) (t : Variety.Point (KMult k)) :
    T.includePoint ((leftCocharacter (D.rootCocharacter s)).onPoints t) *
      (D.rootSubgroup r).includePoint (x.value u) *
      (T.includePoint ((leftCocharacter (D.rootCocharacter s)).onPoints t))⁻¹ =
      (D.rootSubgroup r).includePoint
        (x.value ((dPointEquiv 1 t 0 : k) ^ (D.pairing r s) * u)) := by
  rw [direct_root_conjugation D hD]
  rw [show (leftRootCharacter D r).pointCharacter
    ((leftCocharacter (D.rootCocharacter s)).onPoints t) =
      (dPointEquiv 1 t 0 : k) ^ (D.pairing r s) from left_cartan hD r s t]

/-- In particular, the direct simple-root exponent is +2, in every characteristic. -/
theorem direct_left_coroot_self (D : RootGroupData K T) (hD : D.IsRealization)
    (r : D.Root) (x : OneParameterParametrization (D.rootSubgroup r).carrierVariety)
    (u : k) (t : Variety.Point (KMult k)) :
    T.includePoint ((leftCocharacter (D.rootCocharacter r)).onPoints t) *
      (D.rootSubgroup r).includePoint (x.value u) *
      (T.includePoint ((leftCocharacter (D.rootCocharacter r)).onPoints t))⁻¹ =
      (D.rootSubgroup r).includePoint (x.value ((dPointEquiv 1 t 0 : k) ^ (2 : ℤ) * u)) := by
  simpa only [hD.2.2.2.2.2.2.1 r] using direct_left_coroot_conjugation D hD r r x u t

end Triality.RestrictedWeights.SteinbergTensors.LeftWeights
