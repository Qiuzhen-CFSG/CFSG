module
public import Theory.SpecificGroups.Triality.ArmsParabolicAtTwo
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl

/-!
# Perfectness of the arms parabolic at the binary base field

An order-seven torus element moves both short radical root groups at q = 2.
The highest long root is already a commutator inside the radical. The folded
short-root exchange at parameters (1,1) then recovers the next long root,
and the arms Weyl element recovers the remaining long root. Thus the radical
and the perfect PSL₂(8) Levi lie in the derived subgroup of the first parabolic.

This supplies the q = 2 case needed to identify the original O² residual with
the whole first endpoint in Aschbacher--Smith 14.2.16--18, pp.986--987.
The root formulas and enumeration are those of GLS3 §§2.4,2.6 and the existing
triality model; the Weyl transport follows `StandardTwoRank/Perfectness.lean`.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace Triality.Standard.Parabolics
open ConcreteBruhat PositiveCoordinates PositiveCoordinates.SumExchangeData
open RankOneMatrices RadicalCoordinates RadicalCoordinates.Centers RadicalCoordinates.LeviCommutators
open scoped commutatorElement

private theorem short_motion_at_two (P : Parameters) (hp : P.prime = 2)
    (hq : P.q = 2) (i : Fin 3) (hi : i ≠ 0) : ShortTorusMotion P hp .arms i := by
  obtain ⟨t, ht⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ExtensionField P)ˣ)
  have ht7 : orderOf t = 7 := by
    simpa [Nat.card_units, card_extensionField, hq] using ht
  have hpow5 : t.val ^ 5 ≠ 1 := by
    intro he
    have hh : t ^ 5 = 1 := Units.ext (by simpa using he)
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [ht7] at hd
    norm_num at hd
  have ht1 : t.val ≠ 1 := by
    intro he
    have hh : t = 1 := Units.ext he
    rw [hh, orderOf_one] at ht7
    norm_num at ht7
  have hF (x : ExtensionField P) : fieldFrobenius P x = x ^ 2 := by
    rw [fieldFrobenius_apply, hq]
  fin_cases i
  · exact (hi rfl).elim
  · refine ⟨t, t.val / (fieldFrobenius P t.val *
        fieldFrobenius P (fieldFrobenius P t.val)), ?_,
      torus_arms_short_one_conjugate P hp t⟩
    intro he
    have hh := (div_eq_one_iff_eq (mul_ne_zero (by simp)
      (by simp))).mp he
    simp only [hF] at hh
    apply hpow5
    apply mul_left_cancel₀ t.ne_zero
    calc
      t.val * t.val ^ 5 = t.val ^ 2 * (t.val ^ 2) ^ 2 := by ring
      _ = t.val := hh.symm
      _ = t.val * 1 := (mul_one _).symm
  · refine ⟨t, t.val * fieldFrobenius P t.val /
        fieldFrobenius P (fieldFrobenius P t.val), ?_,
      torus_arms_short_two_conjugate P hp t⟩
    intro he
    have hh := (div_eq_one_iff_eq (by simp)).mp he
    simp only [hF] at hh
    apply ht1
    apply (mul_right_cancel₀ (pow_ne_zero 3 t.ne_zero))
    calc
      t.val * t.val ^ 3 = (t.val ^ 2) ^ 2 := by ring
      _ = t.val * t.val ^ 2 := hh.symm
      _ = 1 * t.val ^ 3 := by ring

private def numbering : rootWeylGroup →* Equiv.Perm (Fin 24) :=
  rootEnumeration.symm.permCongrHom.toMonoidHom.comp rootWeylGroup.subtype

private lemma numbering_generator (i : Fin 4) :
    numbering (rootWeylGenerator i) = DiagramFixed.reflection i := by
  apply Equiv.ext
  intro r
  change rootEnumeration.symm ((typeDRootPairing 2).reflectionPerm
    (typeDSimpleRootIndex 2 i) (rootEnumeration r)) = reflectionTable i r
  rw [← rootEnumeration_reflectionTable, Equiv.symm_apply_apply]

private lemma representative_numbered (w : DihedralGroup 6) (r : Fin 24) :
    (rootRepresentative w).val (rootEnumeration r) =
      rootEnumeration (DiagramFixed.representativeTable w r) := by
  have h : numbering (rootRepresentative w) = DiagramFixed.representative w := by
    cases w <;> simp [rootRepresentative, DiagramFixed.representative, foldedRootReflection,
      map_mul, map_pow, numbering_generator, DiagramFixed.arm]
  have hh := congrFun (congrArg (fun e : Equiv.Perm (Fin 24) => (e : Fin 24 → Fin 24)) h) r
  change rootEnumeration.symm ((rootRepresentative w).val (rootEnumeration r)) = _ at hh
  exact (rootEnumeration.apply_symm_apply _).symm.trans
    (congrArg rootEnumeration (hh.trans (DiagramFixed.representative_apply w r)))

private theorem conjugate_curve (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) (i j : Fin 12)
    (h : DiagramFixed.representativeTable w (positiveIndex i) = positiveIndex j)
    (t : ExtensionField P) :
    splitRepresentative P hp w * curve P i t * (splitRepresentative P hp w)⁻¹ =
      curve P j t := by
  apply Subtype.ext
  change (splitRepresentative P hp w).val * _ * (splitRepresentative P hp w).val⁻¹ = _
  rw [curve_unit, splitRepresentative_rootCurveUnit_conjugation,
    ← rootEnumeration_positiveIndex, representative_numbered, h, rootEnumeration_positiveIndex]
  rfl


private theorem arms_long_conjugate (P : Parameters) (hp : P.prime = 2)
    (t : fixedField P) :
    simpleRepresentative P hp .arms * long P hp 1 t *
      (simpleRepresentative P hp .arms)⁻¹ = long P hp 0 t := by
  rw [← weylRepresentative_simple P hp .arms]
  change toCarrier P (weylElementary P hp (.sr 0)) *
    toCarrier P (longElementary P hp 1 t) *
    (toCarrier P (weylElementary P hp (.sr 0)))⁻¹ = _
  simp only [← map_inv, ← map_mul]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, map_inv, longElementary_val]
  exact conjugate_curve P hp (.sr 0) 10 3 (by decide) t.val

private theorem short_zero_mem_levi (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) : short P hp 0 t ∈ levi P .arms := by
  refine ⟨shortElementary P hp 0 t, ?_, rfl⟩
  change elementaryInclusion P _ ∈ splitLevi P .arms
  rw [shortElementary_val]
  change curve P (simplePosition 0) t * curve P (simplePosition 2) (fieldFrobenius P t) *
    curve P (simplePosition 3) (fieldFrobenius P (fieldFrobenius P t)) ∈ _
  rw [curve_simple, curve_simple, curve_simple]
  have hpos (i : Fin 4) (hi : i ≠ 1) (u : ExtensionField P) :
      positiveRoot P i u ∈ splitLevi P .arms :=
    Subgroup.subset_closure ⟨i, hi, u, Or.inl rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hpos 0 (by decide) _)
    (hpos 2 (by decide) _)) (hpos 3 (by decide) _)

private theorem exchange_middle_mem {X : Type*} [Group X] (D : Subgroup X)
    {a b c d : X} (ha : a ∈ D) (hb : b ∈ D) (hd : d ∈ D)
    (he : a * b = b * a * c * d) : c ∈ D := by
  have hm := D.mul_mem ha hb
  rw [he] at hm
  exact (D.mul_mem_cancel_left (D.mul_mem hb ha)).mp
    ((D.mul_mem_cancel_right hd).mp hm)

/-- The first triality parabolic at q = 2 is perfect. -/
theorem parabolic_arms_isPerfect_at_two (P : Parameters) (hp : P.prime = 2)
    (hq : P.q = 2) : Group.IsPerfect (parabolic P .arms) := by
  let L := parabolic P .arms
  let D := ⁅L,L⁆
  have hR : descendSubgroup P (rootSubgroup P .arms) ≤ L :=
    (descendedRootSubgroup_le_radical P hp .arms).trans (radical_le_parabolic P .arms)
  have hlevi : levi P .arms ≤ L := (levi_le_localFactor P hp .arms).trans
    (localFactor_le_parabolic P .arms)
  have hleviD : levi P .arms ≤ D := by
    let := levi_arms_isPerfect P hp
    exact (commutator_eq_self (H := levi P .arms)).symm.le.trans
      (commutator_mono hlevi hlevi)
  have hshort (i : Fin 3) (t : ExtensionField P) : short P hp i t ∈ D := by
    by_cases hi : i = 0
    · subst i
      exact hleviD (short_zero_mem_levi P hp t)
    · exact commutator_mono hR hlevi
        (short_mem_commutator_of_motion P hp .arms i hi (short_motion_at_two P hp hq i hi) t)
  have hlong2 (t : fixedField P) : long P hp 2 t ∈ D := by
    have he := long_zero_one_exchange P hp t 1
    rw [mul_one] at he
    have hz : long P hp 2 t = ⁅(long P hp 0 t)⁻¹, (long P hp 1 1)⁻¹⁆ := by
      apply mul_left_cancel (a := long P hp 1 1 * long P hp 0 t)
      rw [← he]
      simp only [commutatorElement_def]
      group
    rw [hz]
    exact commutator_mem_commutator (L.inv_mem (hR (long_mem P hp .arms 0 trivial t)))
      (L.inv_mem (hR (long_mem P hp .arms 1 trivial 1)))
  have hlong1 : long P hp 1 1 ∈ D := by
    have he := short_zero_one_exchange P hp 1 1
    have hcoeff : higherCoefficient P 1 1 = 0 := by
      let : CharP (ExtensionField P) 2 := by rw [← hp]; infer_instance
      simp [higherCoefficient, CharTwo.add_self_eq_zero]
    have htrace : cubicTrace P 1 = 1 := by
      let : CharP (ExtensionField P) 2 := by rw [← hp]; infer_instance
      apply Subtype.ext
      simp [cubicTrace_coe, CharTwo.add_self_eq_zero]
    simp only [map_one, mul_one, hcoeff, htrace, short_zero] at he
    exact exchange_middle_mem D (hshort 0 1) (hshort 1 1) (hlong2 1) he
  have hlong (i : Fin 3) (t : fixedField P) : long P hp i t ∈ D := by
    have ht : t = 0 ∨ t = 1 := by
      have hs : t.val ^ 2 = t.val := by
        have hf : fieldFrobenius P t.val = t.val := t.property
        simpa only [fieldFrobenius_apply, hq] using hf
      rcases eq_zero_or_one_of_sq_eq_self hs with hs | hs
      · exact Or.inl (Subtype.ext hs)
      · exact Or.inr (Subtype.ext hs)
    rcases ht with rfl | rfl
    · rw [long_zero]; exact D.one_mem
    fin_cases i
    · change long P hp 0 1 ∈ D
      rw [← arms_long_conjugate P hp 1]
      exact le_normalizer_iff.mp (normalizer_commutator_ge_left L L)
        _ (simpleRepresentative_mem_parabolic P hp .arms) _ hlong1
    · exact hlong1
    · exact hlong2 1
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (commutator_le_self L)
  change parabolic P .arms ≤ D
  rw [parabolic_arms_eq_localFactor_at_two P hp hq,
    localFactor_eq_radical_sup_levi P hp .arms,
    radical_eq_descendedRootSubgroup P hp .arms]
  exact sup_le (descendedRoot_le_of_folded P hp .arms D
    (fun i _ => hshort i) (fun i _ => hlong i)) hleviD
end Triality.Standard.Parabolics
