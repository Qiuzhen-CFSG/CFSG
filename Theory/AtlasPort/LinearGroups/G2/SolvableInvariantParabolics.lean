module
public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement
public import Theory.AtlasPort.LinearGroups.G2.SylowNormalizer

/-!
# Invariant parabolics of a solvable G₂ Sylow overgroup

A solvable subgroup containing the positive-root Sylow lies in the Borel,
so that Sylow is characteristic in it. Its central involutions and second
central involutions determine the two root parabolics. Every automorphism
preserving the overgroup therefore fixes both parabolics.

Source: Aschbacher–Smith 2.3.9(7), printed p.526, applied in 15.3.20,
printed p.1127. Root and octonion facts retain the licensed ATLAS port's
attribution; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup
namespace Atlas.G2.SolvableSylowPlacement
open LieParabolicSetup SylowParabolicInvariance
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem parabolic_pair_map_of_solvable_overgroup
    (hq : 2 < Nat.card F) (B : Subgroup (Model F))
    (hsol : Group.IsSolvable B) (hUB : unipotent ≤ B)
    (a : MulAut (Model F)) (hB : B.map a.toMonoidHom = B) :
    parabolic₁.map a.toMonoidHom = parabolic₁ ∧
      parabolic₂.map a.toMonoidHom = parabolic₂ := by
  have hN : B ≤ normalizer (unipotent (K := F) : Set (Model F)) := by
    rw [SylowNormalizer.normalizer_unipotent]
    exact le_borel hq B hUB hsol
  let T := (sylow (F := F)).subtype hUB
  have hT : (T : Subgroup B).Normal :=
    (normal_subgroupOf_iff_le_normalizer hUB).mpr hN
  let : (T : Subgroup B).Characteristic := T.characteristic_of_normal hT
  let b : MulAut B := (a.subgroupMap B).trans (MulEquiv.subgroupCongr hB)
  have hb : (T : Subgroup B).map b.toMonoidHom = T := characteristic_iff_map_eq.mp inferInstance b
  have hmapT : (T : Subgroup B).map B.subtype = unipotent := by
    change (unipotent.subgroupOf B).map B.subtype = unipotent
    exact map_subgroupOf_eq_of_le hUB
  have hU : unipotent.map a.toMonoidHom = unipotent := by
    calc
      _ = ((T : Subgroup B).map B.subtype).map a.toMonoidHom := by rw [hmapT]
      _ = ((T : Subgroup B).map b.toMonoidHom).map B.subtype := by
        rw [map_map,map_map]
        rfl
      _ = unipotent := by rw [hb,hmapT]
  have hA := map_eq_of_centralInvolutions unipotent highestRoot
    highestRoot_iff_centralInvolution a hU
  have hD := map_eq_of_secondCentralInvolutions unipotent longRootLocal
    longRootLocal_iff_secondCentralInvolution a hU
  constructor
  · rw [←normalizer_highestRoot, map_equiv_normalizer_eq,hA]
  · rw [←normalizer_longRootLocal, map_equiv_normalizer_eq,hD]
end Atlas.G2.SolvableSylowPlacement
