module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers
public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.RootArithmetic
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl
public import Theory.SpecificGroups.Triality.ParabolicGeometry

/-!
# Noncommuting returning conjugates of a two-central triality involution

The center of the genuine positive Sylow is the highest-root subgroup.
The central reflection and the product of the arm and central reflections
send its nonzero parameter t to the other two positive long roots, with the
same parameter. Their already proved exchange has highest-root correction
t², which is nonzero. Sylow conjugacy transports this pair to the original
Sylow of the marked involution. The argument includes field order two.

Source: Aschbacher--Smith 1.1.5(3)(a), pp.501--503, and the inspection in
Proposition 2.2.2, pp.519--520, combined 1 March 2004 manuscript. The root
conventions and exchange are GLS3 §§2.4--2.6. Every element belongs to the
genuine D4 graph-field elementary group and its actual central quotient.
-/

public section
noncomputable section
open Subgroup
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates.SumExchangeData
namespace Triality.Standard.MarkedStrongClosure
open Parabolics ConcreteBruhat PositiveCoordinates
open RadicalCoordinates.Centers RadicalCoordinates.LeviCommutators

private theorem central_highest_root :
    (rootRepresentative (.sr 1)).val (rootIndex 11) = rootIndex 10 := by
  rw [rootRepresentative_sr_one]
  change rootReflection 1 (rootIndex 11) = rootIndex 10
  rw [← rootEnumeration_positiveIndex 11, rootReflection,
    ← rootEnumeration_reflectionTable]
  rfl

private theorem rotation_highest_root :
    (rootRepresentative (.r 1)).val (rootIndex 11) = rootIndex 3 := by
  change ((foldedRootReflection .arms * foldedRootReflection .central) ^ (1 : ℕ)).val
    (rootIndex 11) = rootIndex 3
  rw [pow_one]
  change rootReflection 0 (rootReflection 2 (rootReflection 3
    (rootReflection 1 (rootIndex 11)))) = rootIndex 3
  simp only [← rootEnumeration_positiveIndex 11, rootReflection,
    ← rootEnumeration_reflectionTable]
  rfl

private theorem weyl_conjugate_long (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) (i j : Fin 3)
    (hw : (rootRepresentative w).val (rootIndex (longPosition i)) =
      rootIndex (longPosition j)) (t : fixedField P) :
    weylRepresentative P hp w * long P hp i t * (weylRepresentative P hp w)⁻¹ =
      long P hp j t := by
  have hs : splitRepresentative P hp w * longSplit P i t *
      (splitRepresentative P hp w)⁻¹ = longSplit P j t := by
    apply Subtype.ext
    change (splitRepresentative P hp w).val *
        (curve P (longPosition i) t.val).val *
        (splitRepresentative P hp w).val⁻¹ = (curve P (longPosition j) t.val).val
    simp only [curve_unit]
    rw [splitRepresentative_rootCurveUnit_conjugation, hw]
  have he : weylElementary P hp w * longElementary P hp i t *
      (weylElementary P hp w)⁻¹ = longElementary P hp j t := by
    apply elementaryInclusion_injective P
    simpa only [map_mul, map_inv, longElementary_val, splitRepresentative] using hs
  simpa only [map_mul, map_inv, weylRepresentative, long] using congrArg (toCarrier P) he

private theorem long_two_eq_highestHom (P : Parameters) (hp : P.prime = 2)
    (t : fixedField P) :
    long P hp 2 t = highestHom P hp (Multiplicative.ofAdd t) := by
  have he : elementaryInclusion P (longElementary P hp 2 t) =
      elementaryInclusion P (elementaryHighestHom P hp (Multiplicative.ofAdd t)) :=
    (longElementary_val P hp 2 t).trans
      (elementaryHighestHom_val P hp (Multiplicative.ofAdd t)).symm
  exact congrArg (toCarrier P) (elementaryInclusion_injective P he)

private theorem long_two_ne_one (P : Parameters) (hp : P.prime = 2)
    {t : fixedField P} (ht : t ≠ 0) : long P hp 2 t ≠ 1 := by
  rw [long_two_eq_highestHom]
  intro he
  have hz := highestHom_injective P hp (he.trans (map_one (highestHom P hp)).symm)
  exact ht (congrArg Multiplicative.toAdd hz)

private theorem long_zero_one_not_commute (P : Parameters) (hp : P.prime = 2)
    (t : fixedField P) (ht : t ≠ 0) :
    ¬Commute (long P hp 0 t) (long P hp 1 t) := by
  intro hc
  have he := long_zero_one_exchange P hp t t
  rw [hc.eq] at he
  have hz : long P hp 2 (t * t) = 1 :=
    (mul_left_cancel ((mul_one (long P hp 1 t * long P hp 0 t)).trans he)).symm
  exact long_two_ne_one P hp (mul_ne_zero ht ht) hz

private theorem long_mem_unipotent (P : Parameters) (hp : P.prime = 2)
    (i : Fin 3) (t : fixedField P) : long P hp i t ∈ unipotent P :=
  descendSubgroup_mono P (RadicalCoordinates.rootSubgroup_le_positiveSubgroup P hp .arms)
    (long_mem P hp .arms i (by trivial) t)

/-- Every Sylow contains noncommuting conjugates of its actual nonidentity
central involution. No exhaustive involution classification or field-size
exception is needed. -/
theorem sylow_noncommuting_conjugates (P : Parameters) (hp : P.prime = 2)
    (R : Sylow 2 (Carrier P)) (v : Carrier P)
    (hvR : v ∈ R) (hv : orderOf v = 2)
    (hc : ∀ x ∈ R, Commute v x) :
    ∃ a b : R, IsConj v (a : Carrier P) ∧ IsConj v (b : Carrier P) ∧
      ¬Commute a b := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Carrier P) R (unipotentSylow P hp)
  let f := MulAut.conj g
  have hm : (R : Subgroup (Carrier P)).map f.toMonoidHom = unipotent P := by
    have hh := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, coe_unipotentSylow] at hh
    exact hh
  have hfv : f v ∈ unipotent P := hm ▸ mem_map_of_mem f.toMonoidHom hvR
  have hfc : ∀ x ∈ unipotent P, Commute (f v) x := by
    intro x hx
    rw [← hm] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (hc y hy).map f.toMonoidHom
  have hZ : f v ∈ (center (unipotent P)).map (unipotent P).subtype := by
    refine ⟨⟨f v, hfv⟩, mem_center_iff.mpr ?_, rfl⟩
    intro x
    exact Subtype.ext (hfc x x.property).symm.eq
  rw [embedded_center_unipotent P hp, ← highestHom_range P hp] at hZ
  obtain ⟨t, ht⟩ := hZ
  have he : long P hp 2 t.toAdd = f v :=
    (long_two_eq_highestHom P hp t.toAdd).trans ht
  have hvn : v ≠ 1 := by
    intro heq
    rw [heq, orderOf_one] at hv
    norm_num at hv
  have htn : t.toAdd ≠ 0 := by
    intro hzero
    have hone : f v = 1 := by rw [← he, hzero, long_zero]
    exact hvn (f.injective (hone.trans (map_one f).symm))
  have h0 : IsConj (f v) (long P hp 0 t.toAdd) := by
    rw [← he]
    exact isConj_iff.mpr ⟨weylRepresentative P hp (.r 1),
      weyl_conjugate_long P hp (.r 1) 2 0 rotation_highest_root t.toAdd⟩
  have h1 : IsConj (f v) (long P hp 1 t.toAdd) := by
    rw [← he]
    exact isConj_iff.mpr ⟨weylRepresentative P hp (.sr 1),
      weyl_conjugate_long P hp (.sr 1) 2 1 central_highest_root t.toAdd⟩
  have hback : ∀ x ∈ unipotent P, f.symm x ∈ R := by
    intro x hx
    rw [← hm] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change f.symm (f y) ∈ (R : Subgroup (Carrier P))
    rw [f.symm_apply_apply]
    exact hy
  let a : R := ⟨f.symm (long P hp 0 t.toAdd),
    hback _ (long_mem_unipotent P hp 0 t.toAdd)⟩
  let b : R := ⟨f.symm (long P hp 1 t.toAdd),
    hback _ (long_mem_unipotent P hp 1 t.toAdd)⟩
  refine ⟨a, b, ?_, ?_, ?_⟩
  · simpa only [a, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
      f.symm.toMonoidHom.map_isConj h0
  · simpa only [b, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
      f.symm.toMonoidHom.map_isConj h1
  · intro hab
    apply long_zero_one_not_commute P hp t.toAdd htn
    change long P hp 0 t.toAdd * long P hp 1 t.toAdd =
      long P hp 1 t.toAdd * long P hp 0 t.toAdd
    have hh : (a : Carrier P) * (b : Carrier P) =
        (b : Carrier P) * (a : Carrier P) := congrArg Subtype.val hab.eq
    have hf := congrArg f hh
    change f (f.symm (long P hp 0 t.toAdd) * f.symm (long P hp 1 t.toAdd)) =
      f (f.symm (long P hp 1 t.toAdd) * f.symm (long P hp 0 t.toAdd)) at hf
    simpa only [map_mul, MulEquiv.apply_symm_apply] using hf

end Triality.Standard.MarkedStrongClosure
