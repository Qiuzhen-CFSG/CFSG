module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Transport
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.PointCores
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.PointCores.IncidentRank

/-!
# Component point-core bounds for the middle-node eight-point case

The canonical PSL₄(2)–GL₄(2) equivalence intertwines the actual natural action
and its contragredient. It carries each point stabilizer and its intrinsic
two-core to the simultaneous vector–covector stabilizer and its two-core.

The zero and pairing-one cores are trivial, and the nonzero pure-point cores
have order eight. In the nonzero incident case, the image lies in the concrete
flag-(1,3) radical of order 32. Restriction to the hyperplane and evaluation
on a transverse vector bound its abelian subgroups by order eight. Together
these cases prove that every elementary subgroup of every point two-core
has rank at most three.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49, printed p.1145; B.4.9(2iii), p.92; B.5.1(6), p.103.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight
open Subgroup Representation.BinaryOffender
open Chapter2.ComponentRefinement.LieType.Binary
open BinaryNaturalDual.VectorStabilizers
namespace PointCore

/-- The projective representation is precisely the natural-plus-contragredient linear action. -/
theorem naturalDual_apply (n : ℕ) [NeZero n] (g : PSL n)
    (z : Vector n × Module.Dual (ZMod 2) (Vector n)) :
    BinaryGeometry.naturalDual n g z =
      BinaryNaturalDual.naturalDualRepresentation (pslEquivLinear n g) z := by
  rw [BinaryNaturalDual.naturalDualRepresentation_apply]
  apply Prod.ext
  · rfl
  · apply LinearMap.ext
    intro v
    change z.2 (pslEquivLinear n g⁻¹ v) = z.2 ((pslEquivLinear n g).symm v)
    rw [map_inv]
    rfl

/-- The canonical actor comparison identifies the actual stabilizers. -/
theorem pointStabilizer_map_linear (n : ℕ) [NeZero n]
    (x : Vector n) (f : Module.Dual (ZMod 2) (Vector n)) :
    (pointStabilizer (BinaryGeometry.naturalDual n) (x, f)).map
      (pslEquivLinear n).toMonoidHom = pairStabilizer x f := by
  ext g
  obtain ⟨g, rfl⟩ := (pslEquivLinear n).surjective g
  rw [mem_map_equiv, MulEquiv.symm_apply_apply]
  change BinaryGeometry.naturalDual n g (x, f) = (x, f) ↔ _
  rw [naturalDual_apply]
  exact (mem_pairStabilizer_iff_action x f _).symm

/-- The comparison transports intrinsic two-cores, with no outer-group core identification. -/
theorem pointCore_map_linear (n : ℕ) [NeZero n]
    (x : Vector n) (f : Module.Dual (ZMod 2) (Vector n)) :
    (localTwoCore (pointStabilizer (BinaryGeometry.naturalDual n) (x, f))).map
      (pslEquivLinear n).toMonoidHom = (pairStabilizer x f).pCoreIn 2 := by
  rw [localTwoCore_map_equiv, pointStabilizer_map_linear]
  rfl

/-- An actor in the projective point core remains in the intrinsic linear point core. -/
theorem map_le_pair_core {x : Vector 4} {f : Module.Dual (ZMod 2) (Vector 4)}
    {A : Subgroup (PSL 4)}
    (hA : A ≤ localTwoCore (pointStabilizer (BinaryGeometry.naturalDual 4) (x, f))) :
    A.map (pslEquivLinear 4).toMonoidHom ≤ (pairStabilizer x f).pCoreIn 2 := by
  have h := map_mono (f := (pslEquivLinear 4).toMonoidHom) hA
  rwa [pointCore_map_linear] at h

private theorem rank_le_three_of_card {G : Type*} [Group G]
    {A : Subgroup G} (h : Nat.card A ≤ 8) : rank A ≤ 3 := by
  exact (Nat.log_mono_right h).trans (by decide : Nat.log 2 8 ≤ 3)

private theorem card_le_core {x : Vector 4} {f : Module.Dual (ZMod 2) (Vector 4)}
    {A : Subgroup (PSL 4)}
    (hA : A ≤ localTwoCore (pointStabilizer (BinaryGeometry.naturalDual 4) (x, f))) :
    Nat.card A ≤ Nat.card ((pairStabilizer x f).pCoreIn 2) := by
  let : Finite (BinaryLinear.GL (Vector 4)) := Finite.of_injective
    (fun g : BinaryLinear.GL (Vector 4) => (g : Vector 4 → Vector 4)) DFunLike.coe_injective
  rw [← card_map_of_injective (f := (pslEquivLinear 4).toMonoidHom)
    (pslEquivLinear 4).injective]
  exact card_le_of_le (map_le_pair_core hA)

/-- At the zero point the two-core is trivial. -/
theorem zero_rank_le_three {A : Subgroup (PSL 4)}
    (hA : A ≤ localTwoCore (pointStabilizer (BinaryGeometry.naturalDual 4) (0, 0))) :
    rank A ≤ 3 := by
  have h := card_le_core hA
  rw [PointCores.zero_core, card_bot] at h
  exact rank_le_three_of_card (h.trans (by decide))

/-- The nonzero pure-vector core has order eight. -/
theorem pure_vector_rank_le_three {x : Vector 4} (hx : x ≠ 0)
    {A : Subgroup (PSL 4)}
    (hA : A ≤ localTwoCore (pointStabilizer (BinaryGeometry.naturalDual 4) (x, 0))) :
    rank A ≤ 3 := by
  have h := card_le_core hA
  rw [PointCores.pure_vector_core_card hx] at h
  norm_num [Chapter2.ComponentRefinement.LieType.Binary.Vector, Module.finrank_pi, Fintype.card_fin] at h
  exact rank_le_three_of_card h

/-- The nonzero pure-covector core has order eight by contragredient transport. -/
theorem pure_covector_rank_le_three {f : Module.Dual (ZMod 2) (Vector 4)} (hf : f ≠ 0)
    {A : Subgroup (PSL 4)}
    (hA : A ≤ localTwoCore (pointStabilizer (BinaryGeometry.naturalDual 4) (0, f))) :
    rank A ≤ 3 := by
  have h := card_le_core hA
  rw [PointCores.pure_covector_core_card hf] at h
  norm_num [Chapter2.ComponentRefinement.LieType.Binary.Vector, Module.finrank_pi, Fintype.card_fin] at h
  exact rank_le_three_of_card h

/-- A pairing-one point has trivial intrinsic two-core. -/
theorem pairing_one_rank_le_three {x : Vector 4}
    {f : Module.Dual (ZMod 2) (Vector 4)} (hfx : f x = 1)
    {A : Subgroup (PSL 4)}
    (hA : A ≤ localTwoCore (pointStabilizer (BinaryGeometry.naturalDual 4) (x, f))) :
    rank A ≤ 3 := by
  have h := card_le_core hA
  rw [PointCores.pairing_one_core hfx, card_bot] at h
  exact rank_le_three_of_card (h.trans (by decide))

/-- An incident point core lies in the actual flag radical. -/
theorem incident_map_le_radical {x : Vector 4}
    {f : Module.Dual (ZMod 2) (Vector 4)} (hf : f ≠ 0) (hfx : f x = 0)
    {A : Subgroup (PSL 4)}
    (hA : A ≤ localTwoCore (pointStabilizer (BinaryGeometry.naturalDual 4) (x, f))) :
    A.map (pslEquivLinear 4).toMonoidHom ≤ PointCores.incidentRadical x f :=
  (map_le_pair_core hA).trans (PointCores.incident_core_le hf hfx)

end PointCore

/-- The universal bound reduced to elementary subgroups of the concrete incident radical. -/
theorem naturalDualPointCoreBound_of_incidentRadical
    (hincident : ∀ (x : Vector 4) (f : Module.Dual (ZMod 2) (Vector 4)),
      x ≠ 0 → f ≠ 0 → f x = 0 → ∀ A : Subgroup (BinaryLinear.GL (Vector 4)),
      A ≤ PointCores.incidentRadical x f → IsElementaryAbelian 2 A → Nat.card A ≤ 8) :
    NaturalDualPointCoreBound := by
  rintro ⟨x, f⟩ A hA hE
  by_cases hx : x = 0
  · subst x
    by_cases hf : f = 0
    · subst f
      exact PointCore.zero_rank_le_three hA
    · exact PointCore.pure_covector_rank_le_three hf hA
  by_cases hf : f = 0
  · subst f
    exact PointCore.pure_vector_rank_le_three hx hA
  by_cases hfx : f x = 0
  · have hle := PointCore.incident_map_le_radical hf hfx hA
    let : IsElementaryAbelian 2 A := hE.2
    have hB : IsElementaryAbelian 2 (A.map (pslEquivLinear 4).toMonoidHom) :=
      IsElementaryAbelian.map _
    have hc := hincident x f hx hf hfx _ hle hB
    rw [card_map_of_injective (pslEquivLinear 4).injective] at hc
    exact PointCore.rank_le_three_of_card hc
  · have hfx1 : f x = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hfx
    exact PointCore.pairing_one_rank_le_three hfx1 hA

/-- Every elementary subgroup of an intrinsic natural-plus-dual point two-core
has rank at most three, for the actual projective matrix action. -/
theorem naturalDualPointCoreBound : NaturalDualPointCoreBound := by
  apply naturalDualPointCoreBound_of_incidentRadical
  intro x f hx hf _ A hA hE
  let : IsElementaryAbelian 2 A := hE
  exact PointCores.incidentRadical_elementary_card_le_eight hx hf A hA

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight
