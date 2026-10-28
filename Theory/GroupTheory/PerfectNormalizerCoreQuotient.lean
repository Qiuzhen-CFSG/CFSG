module
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
public import Theory.GroupTheory.CharacteristicNormalizerClosure
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Normalizers of perfect subgroups modulo a normal two-group

If a normal two-group Q normalizes a perfect subgroup A, then A is the
solvable residual of AQ. Consequently the normalizer of the image of A
modulo Q pulls back to the exact normalizer of A. This does not assume A
subnormal in the ambient group.

Source application: the nontrivial quotient action in Aschbacher--Smith,
quasithin C.4.3, printed p.152.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A normal two-group that normalizes a perfect subgroup creates no new
normalizer elements on passing to the quotient. -/
theorem normalizer_perfect_image_comap (A Q : Subgroup G)
    [Group.IsPerfect A] [Q.Normal] (hQ : IsPGroup 2 Q)
    (hQA : Q ≤ normalizer (A : Set G)) :
    (normalizer (A.map (QuotientGroup.mk' Q) : Set (G ⧸ Q))).comap
      (QuotientGroup.mk' Q) = normalizer (A : Set G) := by
  let D := A ⊔ Q
  have hAD : A ≤ D := le_sup_left
  have hQD : Q ≤ D := le_sup_right
  let : (A.subgroupOf D).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hQA)
  let : Group.IsPerfect (A.subgroupOf D) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hAD).symm.toMonoidHom)
    (subgroupOfEquivOfLe hAD).symm.surjective
  have hgen : A.subgroupOf D ⊔ Q.subgroupOf D = ⊤ := by
    apply map_injective D.subtype_injective
    rw [map_sup, map_subgroupOf_eq_of_le hAD, map_subgroupOf_eq_of_le hQD,
      ← MonoidHom.range_eq_map, range_subtype]
  have hs : (solvableResidual D).map D.subtype = A := by
    rw [(residuals_of_perfect_normal_sup_twoGroup (A.subgroupOf D)
      (Q.subgroupOf D) hQ.comap_subtype hgen).2,
      map_subgroupOf_eq_of_le hAD]
  apply le_antisymm
  · rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective Q),
      comap_map_eq, QuotientGroup.ker_mk']
    change normalizer (D : Set G) ≤ normalizer (A : Set G)
    rw [← hs]
    exact normalizer_le_normalizer_characteristic_image D (solvableResidual D)
  · exact map_le_iff_le_comap.mp (A.le_normalizer_map (QuotientGroup.mk' Q))

/-- Centralization modulo the normal two-group already gives normalization
of the original perfect subgroup. -/
theorem normalizes_perfect_of_commutator_le (A Q B : Subgroup G)
    [Group.IsPerfect A] [Q.Normal] (hQ : IsPGroup 2 Q)
    (hQA : Q ≤ normalizer (A : Set G)) (hAB : ⁅A,B⁆ ≤ Q) :
    B ≤ normalizer (A : Set G) := by
  let q := QuotientGroup.mk' Q
  have hc : ⁅A.map q,B.map q⁆ = ⊥ := by
    rw [← map_commutator, map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hAB
  have hn : B.map q ≤ normalizer (A.map q : Set (G ⧸ Q)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
      (centralizer_le_normalizer _)
  have hh := map_le_iff_le_comap.mp hn
  rwa [normalizer_perfect_image_comap A Q hQ hQA] at hh

end Subgroup
