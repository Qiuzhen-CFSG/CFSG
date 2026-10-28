module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.CentralizerSylow
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits.Coordinates
public import Theory.GroupTheory.SubgroupCenterImageBound

/-!
# Noncommuting returning conjugates of the central J₄ involution

The existing center calculation for a Sylow subgroup of `C(a)` identifies
every original Sylow-central involution with the class of the certified
generator `a`. In the literal max1 subgroup, the first local generator and
kernel mask 5 belong to that class and fail to commute: right conjugation
sends masks 3 to 5 under `y`, and 5 to 10 under `x`. The normal elementary
kernel together with `x` is a two-group, so both elements lie in an actual
ambient Sylow. Sylow conjugacy supplies the pair in the given Sylow.

Source: Aschbacher--Smith 1.1.5(3)(f), pp.501--503, and Proposition 2.2.2,
pp.519--520 (combined 1 March 2004 manuscript). The local words and binary
coordinates are the certified ATLAS `J4G1-max1W1` data. All conjugators lie
in the original model; no global fusion or group-order assertion is used.
-/

public section
open Subgroup
open scoped Pointwise
namespace Janko4
open Cardinality Cardinality.KernelCount Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] basis modelGroup matrixA matrixB localKernel
  max1Subgroup localX localY localKernelSeed

private abbrev M := max1Subgroup matrixA_mul_self matrixB_pow_four
private abbrev K : Subgroup M := localKernel matrixA_mul_self matrixB_pow_four
private abbrev x : M := localX matrixA_mul_self matrixB_pow_four
private abbrev y : M := localY matrixA_mul_self matrixB_pow_four
private abbrev k : K := maskValue matrixA_mul_self matrixB_pow_four 5

private theorem mask_checks : maskImage yMasks 3 = 5 ∧ maskImage xMasks 5 = 10 := by
  decide +kernel

private theorem distinct_masks :
    (maskValue matrixA_mul_self matrixB_pow_four 5 : M) ≠
      maskValue matrixA_mul_self matrixB_pow_four 10 := by
  intro h
  have he : maskValue matrixA_mul_self matrixB_pow_four 5 =
      maskValue matrixA_mul_self matrixB_pow_four 10 := Subtype.ext h
  have hb := coordinates_injective matrixA_mul_self matrixB_pow_four he
  have hbit : (5 : ℕ).testBit 0 = (10 : ℕ).testBit 0 := congrFun hb (0 : Fin 11)
  norm_num at hbit

private theorem local_pair_noncommuting : ¬Commute x (k : M) := by
  intro hc
  have hfix : x⁻¹ * (k : M) * x = k := by
    rw [mul_assoc, ← hc.eq, inv_mul_cancel_left]
  have hmove : x⁻¹ * (k : M) * x =
      maskValue matrixA_mul_self matrixB_pow_four 10 := by
    simpa only [mask_checks.2] using
      right_conj_mask_x matrixA_mul_self matrixB_pow_four 5
  exact distinct_masks (hfix.symm.trans hmove)

private theorem local_generator_class : IsConj Janko4.a (x : Model) := by
  obtain ⟨g, hg⟩ := localX_fuses_first matrixA_mul_self matrixB_pow_four
  exact (isConj_iff.mpr ⟨g, hg.symm⟩).symm

private theorem local_mask_class : IsConj Janko4.a ((k : M) : Model) := by
  have hp : IsConj Janko4.a
      (kernelPair matrixA_mul_self matrixB_pow_four : Model) := by
    obtain ⟨g, hg⟩ := pair_fuses_first matrixA_mul_self matrixB_pow_four
    exact (isConj_iff.mpr ⟨g, hg.symm⟩).symm
  have hy : y⁻¹ * kernelPair matrixA_mul_self matrixB_pow_four * y = (k : M) := by
    rw [← maskValue_three]
    simpa only [mask_checks.1] using
      right_conj_mask_y matrixA_mul_self matrixB_pow_four 3
  refine hp.trans (isConj_iff.mpr ⟨(y : Model)⁻¹, ?_⟩)
  simpa only [inv_inv, map_mul, map_inv, Subgroup.subtype_apply] using
    congrArg (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype hy

private theorem base_pair :
    ∃ S : Sylow 2 Model, ∃ a b : S, IsConj Janko4.a (a : Model) ∧
      IsConj Janko4.a (b : Model) ∧ ¬Commute a b := by
  have hx1 : x ≠ 1 := by
    intro h
    apply local_pair_noncommuting
    rw [h]
    exact Commute.one_left _
  have hx2 : x ^ 2 = 1 := by
    simpa only [pow_two] using localX_mul_self matrixA_mul_self matrixB_pow_four
  have hxo : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hxp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hxo, pow_one])
  let : IsElementaryAbelian 2 K :=
    LocalStructure.localKernel_elementary matrixA_mul_self matrixB_pow_four
  have hkp : IsPGroup 2 K := IsElementaryAbelian.isPGroup 2 K
  have hsup : IsPGroup 2 (K ⊔ zpowers x : Subgroup M) :=
    hkp.to_sup_of_normal_left hxp
  obtain ⟨S, hS⟩ := (hsup.map (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype).exists_le_sylow
  have hxS : (x : Model) ∈ S := hS
    (mem_map_of_mem _ ((show zpowers x ≤ K ⊔ zpowers x from le_sup_right) (mem_zpowers x)))
  have hkS : ((k : M) : Model) ∈ S := hS
    (mem_map_of_mem _ ((show K ≤ K ⊔ zpowers x from le_sup_left) k.property))
  refine ⟨S, ⟨x, hxS⟩, ⟨k, hkS⟩, local_generator_class, local_mask_class, ?_⟩
  intro hc
  apply local_pair_noncommuting
  exact Subtype.ext (hc.map (S : Subgroup Model).subtype).eq

private theorem central_marker_class (R : Sylow 2 Model)
    (v : Model) (hv : v ∈ R) (ho : orderOf v = 2)
    (hc : ∀ x ∈ R, Commute v x) : IsConj Janko4.a v := by
  classical
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := centralizer ({Janko4.a} : Set Model))
  obtain ⟨S, hS⟩ := OuterReduction.OddIndex.centralizer_sylow_is_ambient P
  have hcenter : (center (S : Subgroup Model)).map (S : Subgroup Model).subtype =
      zpowers Janko4.a := by
    rw [hS]
    exact OuterReduction.OddIndex.centralizer_sylow_center P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model R S
  let e := MulAut.conj g
  have hmap : (R : Subgroup Model).map e.toMonoidHom = (S : Subgroup Model) :=
    congrArg Sylow.toSubgroup hg
  have hvZ : v ∈ (center R).map (R : Subgroup Model).subtype := by
    refine ⟨⟨v, hv⟩, mem_center_iff.mpr ?_, rfl⟩
    intro t
    exact Subtype.ext (hc t t.property).symm.eq
  have himage := map_subgroup_center_le e.toMonoidHom (R : Subgroup Model)
    (mem_map_of_mem e.toMonoidHom hvZ)
  rw [hmap, hcenter, mem_zpowers_iff_mem_range_orderOf, orderOf_a] at himage
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp himage
  have hi01 : i = 0 ∨ i = 1 := by
    have hi2 := Finset.mem_range.mp hi
    omega
  rcases hi01 with rfl | rfl
  · have hv1 : v = 1 := e.injective (by
      simpa only [pow_zero, map_one, MulEquiv.coe_toMonoidHom] using he.symm)
    simp [hv1] at ho
  · exact (isConj_iff.mpr ⟨g, by
      simpa only [pow_one, MulEquiv.coe_toMonoidHom, e, MulAut.conj_apply]
        using he.symm⟩).symm

/-- Every original two-central J₄ marker has noncommuting conjugates in its
supplied Sylow, with the marked class and conjugating elements proved internally. -/
theorem sylow_noncommuting_conjugates (R : Sylow 2 Model)
    (v : Model) (hv : v ∈ R) (ho : orderOf v = 2)
    (hc : ∀ x ∈ R, Commute v x) :
    ∃ a b : R, IsConj v (a : Model) ∧ IsConj v (b : Model) ∧ ¬Commute a b := by
  have hmarker := central_marker_class R v hv ho hc
  obtain ⟨S, a, b, ha, hb, hab⟩ := base_pair
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model S R
  let e := MulAut.conj g
  have hmap : (S : Subgroup Model).map e.toMonoidHom = (R : Subgroup Model) :=
    congrArg Sylow.toSubgroup hg
  have hmem (t : S) : e (t : Model) ∈ R := by
    change e (t : Model) ∈ (R : Subgroup Model)
    rw [← hmap]
    exact mem_map_of_mem e.toMonoidHom t.property
  refine ⟨⟨e a, hmem a⟩, ⟨e b, hmem b⟩,
    hmarker.symm.trans (ha.trans (isConj_iff.mpr ⟨g, rfl⟩)),
    hmarker.symm.trans (hb.trans (isConj_iff.mpr ⟨g, rfl⟩)), ?_⟩
  intro hcomm
  apply hab
  have hh := hcomm.map (R : Subgroup Model).subtype
  change Commute (e (a : Model)) (e (b : Model)) at hh
  exact Subtype.ext (Commute.of_map e.injective hh).eq

end Janko4
