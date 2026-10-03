module
public import Theory.GroupTheory.SpecificGroups.QuaternionEightAut
public import Mathlib.GroupTheory.PGroup

/-!
# Cubic normalizers of quaternion automorphism two-subgroups

A two-subgroup of the automorphism group of `QuaternionGroup 2` normalized by
a nonidentity automorphism whose cube is one consists of inner automorphisms.
The result is transported through an actual quaternion isomorphism for use
with subgroup factors and their supplied normalizer actions.

The quaternion automorphism group has order twenty-four. Thus a two-subgroup
has order dividing eight, and every one of its elements has eighth power one.
If the cubic automorphism normalizes this subgroup, an element and its product
with its cubic conjugate both belong to the subgroup. The kernel-checked
quaternion calculation `exists_conj_of_eighth_powers_of_cubic` then makes
that element inner. Transport uses the automorphism-group isomorphism induced
by the supplied quaternion model and pulls back the conjugating element.

This intrinsic normalizer calculation controls the terminal-core action on
quaternion factors in Stellmacher (9.1), Journal of Algebra 190 (1997), p.48.
It requires the actual two-subgroup and normalization; it makes no claim that
an arbitrary quaternion automorphism is inner.
-/

namespace QuaternionGroup
/-- A two-subgroup normalized by a nonidentity cubic quaternion automorphism
consists of inner automorphisms. -/
public theorem le_inner_of_isPGroup_two_of_normalized_by_cubic
    (P : Subgroup (MulAut (QuaternionGroup 2))) (hP : IsPGroup 2 P)
    (e : MulAut (QuaternionGroup 2)) (he : e^3 = 1) (hne : e ≠ 1)
    (hnorm : e ∈ Subgroup.normalizer (P : Set (MulAut (QuaternionGroup 2)))) :
    P ≤ (MulAut.conj : QuaternionGroup 2 →* MulAut (QuaternionGroup 2)).range := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hd24 : Nat.card P ∣ 24 := by
    simpa only [card_mulAut_two] using P.card_subgroup_dvd_card
  have hcop : (Nat.card P).Coprime 3 := by
    rw [hn]
    exact Nat.Coprime.pow_left n (by decide)
  have hd8 : Nat.card P ∣ 8 := hcop.dvd_mul_right.mp (show Nat.card P ∣ 8*3 from hd24)
  have hpow (f : MulAut (QuaternionGroup 2)) (hf : f ∈ P) : f^8 = 1 := by
    have hh : (⟨f,hf⟩ : P)^8 = 1 := by
      obtain ⟨k, hk⟩ := hd8
      rw [hk, pow_mul, pow_card_eq_one', one_pow]
    exact congrArg Subtype.val hh
  intro f hf
  have hfconj : e * f * e⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hnorm f).mp hf
  obtain ⟨z, hz⟩ := exists_conj_of_eighth_powers_of_cubic e f he hne
    (hpow f hf) (hpow _ (P.mul_mem hf hfconj))
  exact ⟨z, hz.symm⟩
/-- Cubic-normalized two-subgroups act by inner automorphisms on any supplied
quaternion model. -/
public theorem le_inner_of_isPGroup_two_of_normalized_by_cubic_of_equiv
    {G : Type*} [Group G] (model : G ≃* QuaternionGroup 2)
    (P : Subgroup (MulAut G)) (hP : IsPGroup 2 P)
    (e : MulAut G) (he : e^3 = 1) (hne : e ≠ 1)
    (hnorm : e ∈ Subgroup.normalizer (P : Set (MulAut G))) :
    P ≤ (MulAut.conj : G →* MulAut G).range := by
  let φ := MulAut.congr model
  have he' : (φ e)^3 = 1 := by rw [← map_pow, he, map_one]
  have hne' : φ e ≠ 1 := by
    intro hh
    apply hne
    apply φ.injective
    simpa only [map_one] using hh
  have hnorm' : φ e ∈ Subgroup.normalizer (P.map φ.toMonoidHom : Set (MulAut (QuaternionGroup 2))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro f
    obtain ⟨g, rfl⟩ := φ.surjective f
    rw [← map_inv, ← map_mul, ← map_mul]
    change φ.toMonoidHom g ∈ P.map φ.toMonoidHom ↔
      φ.toMonoidHom (e * g * e⁻¹) ∈ P.map φ.toMonoidHom
    simp only [Subgroup.mem_map_iff_mem (f := φ.toMonoidHom) φ.injective]
    exact Subgroup.mem_normalizer_iff.mp hnorm g
  have hle := le_inner_of_isPGroup_two_of_normalized_by_cubic
    (P.map φ.toMonoidHom) (hP.map φ.toMonoidHom) (φ e) he' hne' hnorm'
  intro f hf
  obtain ⟨q, hq⟩ := hle (Subgroup.mem_map.mpr ⟨f, hf, rfl⟩)
  refine ⟨model.symm q, ?_⟩
  ext x
  apply model.injective
  have hh := DFunLike.congr_fun hq (model x)
  simpa [φ, MulAut.congr_apply, MulAut.conj_apply] using hh
end QuaternionGroup
