module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue.DesignContract
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue.LocalLifts
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue.PartitionAction.Certificates

/-!
# Partition lifts fix no nonzero binary vector

Four even involutions project into the literal three-pair stabilizer and have
zero common fixed space in the original twelve-dimensional column module.
Every lift of one of these involutions cubes to that involution: its error is
in the central cubic kernel inside the component. Thus every subgroup covering
the partition stabilizer contains all four involutions. Conjugating them by an
actual lift of the specified design automorphism proves the same assertion for
every `partitionAt g`.

The resulting nonfixation is stronger than the rank-one application: neither
Sylow containment nor disjointness from the cubic kernel is needed. The final
wrapper retains exactly the inputs of `Catalogue.catalogue_of_design`.

Source: Aschbacher--Smith, Lemma 14.4.12, printed pp.1011--1012, case
14.4.2(6), p.1006, and H.12.1, pp.393--394. The finite certificates use the
published native matrices and design projection, without point-centralizer
classification or a comparison with a separate representation.
-/

public section
open Subgroup Sporadic.Mathieu
open scoped Pointwise
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue
namespace PartitionAction

/-- An even involution lies in every subgroup whose design image contains
its image, since cubing any lift removes the central cubic error. -/
lemma involution_mem_of_image (P : Subgroup Model) (x : Model) (hx : x ∈ component)
    (hx2 : x ^ 2 = 1) (himage : designProjection x ∈ P.map designProjection) : x ∈ P := by
  obtain ⟨y, hy, he⟩ := himage
  let c := y * x⁻¹
  have hc : c ∈ cubic := by
    rw [← designProjection_ker]
    change designProjection (y * x⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hc3 : c ^ 3 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨c, hc⟩ : cubic))
    rw [cubic_card] at hh
    have hh' := congrArg cubic.subtype hh
    rw [map_pow, map_one] at hh'
    exact hh'
  have hcx : Commute c x := (cubic_le_centralizer_component hc x hx).symm
  have hy3 : y ^ 3 = x := by
    calc
      y ^ 3 = (c * x) ^ 3 := by simp [c]
      _ = c ^ 3 * x ^ 3 := hcx.mul_pow 3
      _ = x := by rw [hc3, one_mul, show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hx2, one_mul]
  exact hy3 ▸ P.pow_mem hy 3

private lemma native_involution_partition (i : Fin 4) :
    designProjection (componentInclusion (Certificates.involution i)) ∈
      M22ValueBound.Concrete.outerSecond := by
  rw [designProjection_component]
  change (componentProjection (Certificates.involution i) : Equiv.Perm (Fin 22)) •
    M22ValueBound.Concrete.hexadPartition = M22ValueBound.Concrete.hexadPartition
  rw [componentProjection_apply_perm]
  exact Certificates.involution_partition i

/-- The zero fixed-space calculation transported through the actual design
projection and the original column representation. -/
lemma eq_zero_of_partitionAt_le_image (g : m22DesignAut) (P : Subgroup Model)
    (himage : partitionAt g ≤ P.map designProjection) (v : Space)
    (hfix : P ≤ pointCentralizer v) : v = 0 := by
  obtain ⟨t, ht⟩ := designProjection_surjective g
  have hw : action t⁻¹ v = 0 := by
    apply Certificates.eq_zero_of_fixed
    intro i
    let x : Model := componentInclusion (Certificates.involution i)
    have hx : x ∈ component := (Certificates.involution i).property
    have hx2 : x ^ 2 = 1 := by
      change componentInclusion (Certificates.involution i) ^ 2 = 1
      rw [← map_pow, Certificates.involution_square, map_one]
    have hyC : t * x * t⁻¹ ∈ component := component_normal.conj_mem x hx t
    have hy2 : (t * x * t⁻¹) ^ 2 = 1 := by
      change ((MulAut.conj t) x) ^ 2 = 1
      rw [← map_pow, hx2, map_one]
    have hyim : designProjection (t * x * t⁻¹) ∈ P.map designProjection := by
      apply himage
      refine mem_map.mpr ⟨designProjection x, native_involution_partition i, ?_⟩
      change g * designProjection x * g⁻¹ = designProjection (t * x * t⁻¹)
      rw [map_mul, map_mul, map_inv, ht]
    have hyfix : action (t * x * t⁻¹) v = v :=
      hfix (involution_mem_of_image P _ hyC hy2 hyim)
    have h := congrArg (fun w => action t⁻¹ w) hyfix
    rw [← Module.End.mul_apply, ← map_mul,
      show t⁻¹ * (t * x * t⁻¹) = x * t⁻¹ by group,
      map_mul, Module.End.mul_apply] at h
    change action (componentInclusion (Certificates.involution i)) (action t⁻¹ v) =
      action t⁻¹ v at h
    rwa [action_component, M22TripleCover.binaryRepresentation_apply,
      Certificates.involution_matrix] at h
  have h := congrArg (fun w => action t w) hw
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply, map_zero] using h

end PartitionAction

/-- The exact binary nonfixation input used to order the two native rank-one
lifts in `catalogue_of_design`. -/
lemma partition_not_le_pointCentralizer (S : Sylow 2 Model) (v : Space) (hv : v ≠ 0)
    (g : m22DesignAut) (P : Subgroup Model) (_hP : P ∈ rankOneOvergroups S)
    (_hd : Disjoint cubic P) (himage : P.map designProjection = partitionAt g) :
    ¬ P ≤ pointCentralizer v := by
  intro hfix
  exact hv (PartitionAction.eq_zero_of_partitionAt_le_image g P himage.ge v hfix)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue
