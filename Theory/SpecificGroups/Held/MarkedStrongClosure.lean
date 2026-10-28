module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage.FiniteFusion.Roots
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.Representative

/-!
# Noncommuting returning conjugates of the central Held involution

Roots 3 and 4 of the checked Held fusion forest conjugate the literal
`max5First ^ 4` to binary words 6 and 12 in the actual representative Sylow.
The existing internal conjugator identifies that representative with
`centralWord`. The two binary words do not commute: their products have
different images at permutation point 0. The whole Sylow-center identity
identifies every original two-central marker with this class, and Sylow
conjugacy puts the pair in the supplied Sylow subgroup.

Source: Aschbacher--Smith 1.1.5(3)(f), pp.501--503, and the Bender inspection
in Proposition 2.2.2, pp.519--520 (combined 1 March 2004 manuscript).
All words use the unchanged ATLAS HeG1-p2058B0 carrier and left action.
-/

public section
open Subgroup
open scoped Pointwise
namespace Held
open LocalPairs.SylowGeometry.Calculations
open TwoLocalCandidates TwoLocalCandidates.MaximalNormalizerCatalogue
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration
open InvolutionFixedData.Coverage AutomorphismLocalPair

private theorem noncommuting_check :
    normalPerm 6 (normalPerm 12 (0 : Fin 2058)) ≠ normalPerm 12 (normalPerm 6 0) := by
  decide +kernel

private theorem base_pair :
    ∃ a b : representative, IsConj centralWord (a : He) ∧
      IsConj centralWord (b : He) ∧ ¬Commute a b := by
  have hi3 : rootIndex 3 = 6 := by decide +kernel
  have hi4 : rootIndex 4 = 12 := by decide +kernel
  have hr3 : rootRepresentative 3 = max5First ^ 4 := by
    unfold rootRepresentative
    rw [if_neg (by decide +kernel : rootClass 3 ≠ 0)]
  have hr4 : rootRepresentative 4 = max5First ^ 4 := by
    unfold rootRepresentative
    rw [if_neg (by decide +kernel : rootClass 4 ≠ 0)]
  have hz : IsConj (max5First ^ 4) centralWord :=
    isConj_iff.mpr ⟨conjugator 0, conjugator_zero_max5First_four⟩
  have hx : IsConj (max5First ^ 4) (normalForm 6).val := by
    apply isConj_iff.mpr
    refine ⟨rootConjugator 3, ?_⟩
    change MulAut.conj (rootConjugator 3) (max5First ^ 4) = (normalForm 6).val
    simpa only [hi3, hr3] using root_conjugation_identity 3
  have hy : IsConj (max5First ^ 4) (normalForm 12).val := by
    apply isConj_iff.mpr
    refine ⟨rootConjugator 4, ?_⟩
    change MulAut.conj (rootConjugator 4) (max5First ^ 4) = (normalForm 12).val
    simpa only [hi4, hr4] using root_conjugation_identity 4
  refine ⟨normalForm 6, normalForm 12, hz.symm.trans hx, hz.symm.trans hy, ?_⟩
  intro h
  have he := congrArg (fun x : representative => representation (x : He) (0 : Fin 2058)) h.eq
  change representation ((normalForm 6).val * (normalForm 12).val) 0 =
    representation ((normalForm 12).val * (normalForm 6).val) 0 at he
  simp only [map_mul, Equiv.Perm.mul_apply, normalForm_representation] at he
  exact noncommuting_check he

private theorem central_marker_class (R : Sylow 2 He)
    (v : He) (hv : v ∈ R) (ho : orderOf v = 2)
    (hc : ∀ x ∈ R, Commute v x) : IsConj centralWord v := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq He R representativeSylow
  let e := MulAut.conj g
  have hmap : (R : Subgroup He).map e.toMonoidHom = representative := by
    change ((g • R : Sylow 2 He) : Subgroup He) = representative
    rw [hg, representativeSylow_coe]
  have hvZ : v ∈ centerSeed (R : Subgroup He) :=
    (mem_centerSeed _ _).mpr ⟨hv, fun x hx => (hc x hx).symm.eq⟩
  have himage : e v ∈ centerSeed representative := by
    rw [← hmap, centerSeed_map]
    exact mem_map_of_mem e.toMonoidHom hvZ
  rw [representative_centerSeed, mem_zpowers_iff_mem_range_orderOf,
    centralWord_order] at himage
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp himage
  have hi01 : i = 0 ∨ i = 1 := by
    have hi2 := Finset.mem_range.mp hi
    omega
  rcases hi01 with rfl | rfl
  · have hv1 : v = 1 := e.injective (by
      simpa only [pow_zero, map_one, MulEquiv.coe_toMonoidHom] using he.symm)
    simp [hv1] at ho
  · exact (isConj_iff.mpr ⟨g, by
      simpa only [pow_one, MulEquiv.coe_toMonoidHom, e, MulAut.conj_apply] using he.symm⟩).symm

/-- Every original two-central Held marker has noncommuting conjugates in
its supplied Sylow subgroup, with the marked class proved internally. -/
theorem sylow_noncommuting_conjugates (R : Sylow 2 He)
    (v : He) (hv : v ∈ R) (ho : orderOf v = 2)
    (hc : ∀ x ∈ R, Commute v x) :
    ∃ a b : R, IsConj v (a : He) ∧ IsConj v (b : He) ∧ ¬Commute a b := by
  have hmarker := central_marker_class R v hv ho hc
  obtain ⟨a, b, ha, hb, hab⟩ := base_pair
  obtain ⟨g, hg⟩ := exists_conjugate_representative R
  let e := MulAut.conj g
  have hmem (x : representative) : e (x : He) ∈ R := by
    change e (x : He) ∈ (R : Subgroup He)
    rw [← hg]
    exact mem_map_of_mem e.toMonoidHom x.property
  refine ⟨⟨e a, hmem a⟩, ⟨e b, hmem b⟩,
    hmarker.symm.trans (ha.trans (isConj_iff.mpr ⟨g, rfl⟩)),
    hmarker.symm.trans (hb.trans (isConj_iff.mpr ⟨g, rfl⟩)), ?_⟩
  intro hcomm
  apply hab
  have hh := hcomm.map (R : Subgroup He).subtype
  change Commute (e (a : He)) (e (b : He)) at hh
  exact Subtype.ext (Commute.of_map e.injective hh).eq

end Held
