module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Point
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedCentralizers

/-!
# Adapted nonsingular points in the original ambient group

The corrected H.9 theorem moves the point by an element of L. Its relative
Sylow is the literal C_T(w); fixed-space transport gives the original
T-fixed line, and residual transport lifts an element moving that line to
O²(C_L(w)). Normalizer conjugation then reduces 12.1.1 to these adapted
points. No ambient point-centralizer containment is assumed here.

Source: Aschbacher--Smith, 12.1.1, pp.788--789, with the corrected H.9.1(4)
marking described in docs/quasithin-proof-basis.md.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

/-- Geometric and relative Sylow conclusions of the corrected H.9 marking.
All fields are proved from the compatible source model below. -/
structure AdaptedPoint (S : B.SourceModel)
    (w : componentOrbit V (T : Subgroup G)) : Prop where
  nonsingular : B.quadratic (Additive.ofMul w) = 1
  local_sylow : Chapter1.IsSylowIn 2 (B.pointSylow w) (B.localPointCentralizer w)
  fixed_moving : S.setup.moving (Additive.ofMul w) ⊓ B.fixedSpace (B.pointSylow w) =
    B.fixedSpace (T : Subgroup G)
  fixed_rank : Module.finrank (ZMod 2) (B.fixedSpace (T : Subgroup G)) = 1
  residual_moves : ¬ B.pointResidual w ≤ centralizer (B.fixedLine : Set G)

namespace SourceModel
variable {B} (S : B.SourceModel)

omit [Finite G] in
/-- Fixed spaces computed in the action quotient are literal ambient centralizers. -/
theorem fixed_image_eq (A : Subgroup (normalizer (L : Set G))) :
    S.setup.fixed (A.map B.actionProjection) =
      B.fixedSpace (A.map (normalizer (L : Set G)).subtype) := by
  ext z
  change z ∈ S.setup.fixed (A.map B.actionProjection) ↔
    z ∈ subgroupSpace (componentOrbit V (T : Subgroup G))
      (centralizer (A.map (normalizer (L : Set G)).subtype : Set G))
  rw [mem_subgroupSpace]
  exact S.mem_fixed_image_iff A z.toMul

/-- The Sylow point-intersection has the expected image even when the kernel
of the normalizer action is not a two-group. -/
theorem pointSylow_image (P : Sylow 2 (normalizer (L : Set G)))
    (w : componentOrbit V (T : Subgroup G)) :
    ((P : Subgroup _) ⊓ (B.pointCentralizer w).subgroupOf (normalizer (L : Set G))).map
      B.actionProjection =
        ((P.mapSurjective B.actionProjection_surjective : Sylow 2 B.ActionQuotient) :
          Subgroup B.ActionQuotient) ⊓ S.setup.stabilizer (Additive.ofMul w) := by
  ext a
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨mem_map_of_mem _ hm.1, ?_⟩
    have hh : m ∈ (S.setup.stabilizer (Additive.ofMul w)).comap B.actionProjection := by
      rw [S.stabilizer_comap]
      exact hm.2
    exact hh
  · rintro ⟨⟨m, hm, rfl⟩, hw⟩
    refine ⟨m, ⟨hm, ?_⟩, rfl⟩
    have hh : m ∈ (S.setup.stabilizer (Additive.ofMul w)).comap B.actionProjection := hw
    rw [S.stabilizer_comap] at hh
    exact hh

end SourceModel
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Every nonsingular point has an L-conjugate with the full corrected marking,
including actual movement by the point residual on the original fixed line. -/
theorem doubleNatural_adaptedPoint
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G),
      B.quadratic (Additive.ofMul w) = 1 →
      ∃ l : L, ∃ w' : componentOrbit V (T : Subgroup G),
        (w' : G) = (l : G) * (w : G) * (l : G)⁻¹ ∧ B.AdaptedPoint S w' := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  let M := normalizer (L : Set G)
  let P : Sylow 2 M := T.subtype D.sylow_normalizes_component
  let Pbar := P.mapSurjective B.actionProjection_surjective
  have hPM : (P : Subgroup M).map M.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le D.sylow_normalizes_component
  have hfixed : S.setup.fixed Pbar = B.fixedSpace (T : Subgroup G) := by
    change S.setup.fixed ((P : Subgroup M).map B.actionProjection) = _
    rw [S.fixed_image_eq, hPM]
  obtain ⟨l, w', he, hq, hP, _, hmove, hrank, a, ha, z, hz, haz⟩ :=
    S.adapted_pair P w hw ⊥ (IsPGroup.of_subsingleton 2 _) bot_le
  have hinter :
      ((P : Subgroup M) ⊓ (B.pointCentralizer w').subgroupOf M).map M.subtype =
        B.pointSylow w' := by
    rw [map_inf _ _ _ M.subtype_injective, hPM, subgroupOf_map_subtype]
    change (T : Subgroup G) ⊓ (B.pointCentralizer w' ⊓ M) =
      (T : Subgroup G) ⊓ B.pointCentralizer w'
    exact le_antisymm (inf_le_inf_left _ inf_le_left)
      (le_inf inf_le_left (le_inf inf_le_right
        (inf_le_left.trans D.sylow_normalizes_component)))
  have hpointfixed : S.setup.fixed
      ((Pbar : Subgroup B.ActionQuotient) ⊓ S.setup.stabilizer (Additive.ofMul w')) =
        B.fixedSpace (B.pointSylow w') := by
    rw [← S.pointSylow_image P w', S.fixed_image_eq, hinter]
  refine ⟨l, w', he, hq, ?_, ?_, ?_, ?_⟩
  · have hs := (Chapter1.IsSylowIn.map_iff M.subtype M.subtype_injective).mpr hP
    rw [subgroupOf_map_subtype] at hs
    change Chapter1.IsSylowIn 2
      (((P : Subgroup M) ⊓ (B.pointCentralizer w').subgroupOf M).map M.subtype)
      (B.pointCentralizer w' ⊓ M) at hs
    rw [hinter, inf_comm (B.pointCentralizer w') M] at hs
    exact hs
  · rwa [hpointfixed, hfixed] at hmove
  · rwa [hfixed] at hrank
  · obtain ⟨b, hb, hbz⟩ := S.exists_pointResidual_mover w' z.toMul ⟨a, ha, haz⟩
    have hzC : (z.toMul : G) ∈ centralizer (T : Set G) := by
      rw [hfixed] at hz
      exact (mem_subgroupSpace _ _ z).mp hz
    intro hc
    have hh := hc hb _ ⟨z.toMul.property, hzC⟩
    exact hbz (mul_inv_eq_iff_eq_mul.mpr hh.symm)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Containment for the constructed adapted representatives suffices for every
nonsingular point. The conclusion is transported back by the same element of L. -/
theorem doubleNatural_nonsingularCentralizers_of_adapted
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel,
      (∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
        B.pointCentralizer w ≤ normalizer (L : Set G)) → B.NonsingularCentralizers := by
  let := D.doubledOrbit_elementary h
  intro S hcontrol w hw
  have hq : B.quadratic (Additive.ofMul w) = 1 := by
    exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hw
  obtain ⟨l, w', he, hw'⟩ := D.doubleNatural_adaptedPoint h B S w hq
  intro x hx
  have hx' : (l : G) * x * (l : G)⁻¹ ∈ B.pointCentralizer w' := by
    apply mem_centralizer_singleton_iff.mpr
    rw [he]
    have hc := mem_centralizer_singleton_iff.mp hx
    calc
      (l : G) * x * (l : G)⁻¹ * ((l : G) * (w : G) * (l : G)⁻¹) =
          (l : G) * (x * (w : G)) * (l : G)⁻¹ := by group
      _ = (l : G) * ((w : G) * x) * (l : G)⁻¹ := by rw [hc]
      _ = (l : G) * (w : G) * (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) := by group
  have hm := hcontrol w' hw' hx'
  have hl : (l : G) ∈ normalizer (L : Set G) := L.le_normalizer l.property
  have hh := (normalizer (L : Set G)).mul_mem
    ((normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).inv_mem hl) hm) hl
  have heq : (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * (l : G) = x := by group
  rwa [heq] at hh

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
