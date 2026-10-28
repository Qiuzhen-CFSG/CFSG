module

public import Theory.GroupTheory.GeneralizedFitting.ComponentLayerProjection
public import CFSG.Quasithin.ChapterI.Section03.GeneralTwoOrbit.Source
public import CFSG.Quasithin.ChapterI.Section03.RankTwoSource

/-!
# The source orbit projection used in rank-two balance

The unconditional GLS II 5.22 theorem selects an ambient two-component J
and proves that its P-orbit is the seed's normal closure in the two-layer.
Under the actual map H → H/O(H), the two-layer becomes the ordinary layer
and J becomes an ordinary component. The layer projection onto J̄/Z(J̄)
cannot kill the seed: its normal kernel would then contain that normal
closure, including J̄, contrary to its surjective restriction to J̄.

Thus `earlierOrbitProjection` proves the exact universal contract consumed
by the existing rank-two theorem, without any extra source premise. The
last theorem applies it to I.3.1(3), leaving precisely A.3.6 and A.3.8 to
their structural source producer. The imported `GeneralTwoOrbit.Source`
also retains all four GLS 5.22 clauses, including the literal fixed-subgroup
quotient maps for every invariant normal subgroup of O_{2',2} of the orbit.
No map to the covering factor J̄ itself is asserted.

Source: GLS II, Chapter B, Proposition 5.22(i)-(iv); Aschbacher--Smith,
combined manuscript of 1 March 2004, I.3.1, printed pp.414--415.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterI.RankTwoSource
open Theory.GroupTheory
universe u

/-- GLS 5.22 supplies the orbit and a nonzero projection onto the central
quotient of its selected component's literal image modulo the ambient odd core.
S₂ and two-layer balance are fully discharged; no K-group assumption is needed. -/
theorem orbit_projection {H : Type u} [Group H] [Finite H]
    (P : Subgroup H) (hP : IsPGroup 2 P)
    (L : Subgroup (centralizer (P : Set H))) (hL : L.IsTwoComponent) :
    ∃ J : Subgroup H, J.IsTwoComponent ∧
      componentOrbit (L.map (centralizer (P : Set H)).subtype) (oddELayer H) =
        componentOrbit J P ∧
      ∃ π : L →* (J.map (QuotientGroup.mk' (pPrimeCore 2 H)) ⧸
        center (J.map (QuotientGroup.mk' (pPrimeCore 2 H)))), π.range ≠ ⊥ := by
  obtain ⟨J, hJ, hLJ, _, hgen, hodd, _⟩ :=
    GeneralTwoOrbit.Source.internal_orbit_and_closures P hP L hL
  refine ⟨J, hJ, hodd, ?_⟩
  let C := centralizer (P : Set H)
  let D := L.map C.subtype
  let q := QuotientGroup.mk' (pPrimeCore 2 H)
  let f : L →* H ⧸ pPrimeCore 2 H := q.comp (C.subtype.comp L.subtype)
  have hfrange : f.range = D.map q := by
    simp only [f, D, MonoidHom.range_comp, range_subtype]
  have hf : f.range ≤ componentLayer (H ⧸ pPrimeCore 2 H) := by
    rw [hfrange]
    exact (map_mono (hLJ.trans (GeneralTwoOrbit.orbit_le_twoLayer hJ P))).trans_eq
      Balance.map_twoComponentLayer_oddCore
  have hqgen := congrArg (map q) hgen
  rw [map_componentOrbit, Balance.map_twoComponentLayer_oddCore] at hqgen
  have hJgen : J.map q ≤ componentOrbit f.range (componentLayer (H ⧸ pPrimeCore 2 H)) := by
    rw [hfrange, hqgen]
    exact map_mono (le_componentOrbit J P)
  exact (Balance.twoComponent_oddCore_image hJ).exists_nontrivial_centralQuotient_projection
    f hf hJgen

/-- Discharge the exact earlier-source contract used by the rank-two
I.3 theorem and its Chapter 15 and E.6 consumers. -/
theorem earlierOrbitProjection (κ : GroupClass.{u}) : EarlierOrbitProjection κ := by
  intro H _ _ _ P hP L hL
  exact orbit_projection P hP L hL

/-- The literal rank-two I.3.1(3) application, with the orbit/projection
premise discharged. Only the genuine earlier A.3.6 and A.3.8 inputs remain. -/
theorem lemma_I_3_1_three_of_earlier_structure
    {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}
    (hA36 : EarlierA36 κ) (hA38 : EarlierA38 κ) (hH : IsSQTK κ H)
    (P : Subgroup H) (hP : IsPGroup 2 P)
    (L : Subgroup (centralizer (P : Set H))) (hL : L.IsTwoComponent)
    (hr : primeRank 3 L = 2) :
    IsQuasisimple L ∧ ∃ J : Subgroup H, IsComponent H J ∧ J.Normal ∧
      L.map (centralizer (P : Set H)).subtype ≤ J :=
  lemma_I_3_1_three hA36 hA38 (earlierOrbitProjection κ) hH P hP L hL hr

end CFSG.Quasithin.ChapterI.RankTwoSource
