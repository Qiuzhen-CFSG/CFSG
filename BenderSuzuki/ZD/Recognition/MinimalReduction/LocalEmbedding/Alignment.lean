module
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.Conjugation
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms
public import Theory.GroupAction.NormalizerFixedCentralizer

/-!
# Aligning a commuting conjugate with the distinguished subgroup

An involutory automorphism of an even-order group fixes an involution by
parity. Strong embedding conjugates that fixed involution into the specified
subgroup. When the original central involution centralizes D, this
conjugation leaves it fixed. Transport of Lemma 4.7(c) then expresses the
product of the adjusted conjugate with any commuting distinguished
involution as a commuting product of distinguished involutions.

Source: GLS, Volume 4, Chapter 2, (4F)--(4G) and the final paragraph of
Proposition 4.4. The parity argument avoids needing the more precise
dihedral Sylow order in that paragraph.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1

private theorem involution_of_isConj {G : Type*} [Group G] {u v : G}
    (hu : PFAppendixIII.IsInvolution u) (hconj : IsConj u v) :
    PFAppendixIII.IsInvolution v := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hh := BenderSuzuki.IsInvolution.map_of_injective hu
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  change PFAppendixIII.IsInvolution (MulAut.conj g u) at hh
  simpa only [MulAut.conj_apply, hg] using hh

/-- Conjugate a commuting conjugate so that its fixed involution in D lies in M. -/
public theorem exists_aligned_commuting_conjugate
    {G : Type*} [Group G] [Finite G] {M D : Subgroup G} {u v : G}
    (hu : PFAppendixIII.IsInvolution u) (huv : u ≠ v) (hconj : IsConj u v)
    (hcomm : Commute u v) (hDC : D ≤ Subgroup.centralizer ({u} : Set G))
    (hvN : v ∈ Subgroup.normalizer (D : Set G))
    (hSE : IsStronglyEmbedded (M.comap D.subtype)) :
    ∃ w : G, ∃ t : D, PFAppendixIII.IsInvolution w ∧ u ≠ w ∧ IsConj u w ∧
      Commute u w ∧ PFAppendixIII.IsInvolution t ∧ (t : G) ∈ M ∧ Commute (t : G) w := by
  let n : Subgroup.normalizer (D : Set G) := ⟨v, hvN⟩
  let a := D.normalizerMonoidHom n
  have hv := involution_of_isConj hu hconj
  have hn2 : n ^ 2 = 1 := Subtype.ext hv.sq_eq_one
  have ha2 : a ^ 2 = 1 := by rw [← map_pow, hn2, map_one]
  obtain ⟨t, htM, ht⟩ := hSE.exists_involution
  have heven : Even (Nat.card D) := by
    rw [even_iff_two_dvd, ← orderOf_eq_prime ht.sq_eq_one ht.ne_one]
    exact orderOf_dvd_natCard t
  obtain ⟨s, hsfix, hs⟩ := exists_fixed_involution_of_even a ha2 heven
  obtain ⟨g, hg⟩ := hSE.involutions_conjugate hs ht
  let e := MulAut.conj (g : G)⁻¹
  have heu : e u = u := by
    change (g : G)⁻¹ * u * ((g : G)⁻¹)⁻¹ = u
    rw [inv_inv, (show Commute (g : G) u from
      Subgroup.mem_centralizer_singleton_iff.mp (hDC g.property)).inv_left.eq]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  have hes : e (s : G) = (t : G) := by
    simpa only [rightConjugateElem, e, MulAut.conj_apply, inv_inv,
      Subgroup.coe_mul, Subgroup.coe_inv] using congrArg (fun x : D => (x : G)) hg
  have hsv : Commute (s : G) v := by
    have hh := congrArg D.subtype ((MulAut.mem_fixedSubgroup a s).mp hsfix)
    change v * (s : G) * v⁻¹ = (s : G) at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  refine ⟨e v, t, BenderSuzuki.IsInvolution.map_of_injective hv e.toMonoidHom e.injective,
    ?_, hconj.trans (isConj_iff.mpr ⟨(g : G)⁻¹, rfl⟩), ?_, ht, htM, ?_⟩
  · intro hh
    exact huv (e.injective (heu.trans hh))
  · have hh := hcomm.map e.toMonoidHom
    change Commute (e u) (e v) at hh
    rwa [heu] at hh
  · have hh := hsv.map e.toMonoidHom
    change Commute (e (s : G)) (e v) at hh
    rwa [hes] at hh

/-- Distinguished involutions in a conjugate centralizer give products in the source set P. -/
public theorem local_conjugate_distinguished_product
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G} {u v : G}
    (h : IsProductDisconnected Z M) (hu : PFAppendixIII.IsInvolution u) (huM : u ∈ M)
    (hC : ¬ Subgroup.centralizer ({u} : Set G) ≤ M)
    (hne : ∃ z ∈ Z, z ∈ Subgroup.centralizer ({u} : Set G) ∧ z ∈ M)
    (huL : u ∈ centralizerClosure Z u)
    (hs : StructureConclusion ((Subgroup.centralizer ({u} : Set G)).subtype ⁻¹' Z)
      (M.comap (Subgroup.centralizer ({u} : Set G)).subtype))
    (hconj : IsConj u v) {z : G} (hz : z ∈ Z) (hcomm : Commute z v) :
    ∃ a ∈ Z, ∃ b ∈ Z, Commute a b ∧ v * z = a * b := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let e := MulAut.conj g
  let z₀ := MulAut.conj g⁻¹ z
  have he : e u = v := hg
  have hei : MulAut.conj g⁻¹ v = u := by
    rw [← he]
    simp only [e, MulAut.conj_apply, inv_inv]
    group
  have hez : e z₀ = z := by
    simp only [e, z₀, MulAut.conj_apply, inv_inv]
    group
  have hz₀ : z₀ ∈ Z := h.invariant g⁻¹ z hz
  have hc₀ : Commute z₀ u := by
    have hh := hcomm.map (MulAut.conj g⁻¹).toMonoidHom
    change Commute z₀ (MulAut.conj g⁻¹ v) at hh
    rwa [hei] at hh
  have huZ := (not_mem_or_product_of_centralizer_not_le h hu huM hC).1
  have hi : PFAppendixIII.IsInvolution (u * z₀) := by
    refine ⟨?_, ?_⟩
    · intro hh
      have heq := congrArg (fun x => x * z₀) hh
      have huz : u = z₀ := by
        simpa only [mul_assoc, ← pow_two, (h.involutions z₀ hz₀).sq_eq_one,
          mul_one, one_mul] using heq
      exact huZ (huz ▸ hz₀)
    · rw [hc₀.symm.mul_pow, hu.sq_eq_one, (h.involutions z₀ hz₀).sq_eq_one, one_mul]
  obtain ⟨_, hZD⟩ := LocalCosetIdentification.central_factor_of_structure hu huL hs
  obtain ⟨_, _, hprod⟩ := LocalCosetIdentification.local_involution_identifications_of_structure
    h hu huM hC hne huL hs
  obtain ⟨a, ha, b, hb, hab, heq⟩ := hprod (u * z₀)
    (hZD z₀ hz₀ (Subgroup.mem_centralizer_singleton_iff.mpr hc₀.eq)) hi
  refine ⟨e a, h.invariant g a ha, e b, h.invariant g b hb, hab.map e.toMonoidHom, ?_⟩
  have hh := congrArg e heq
  simpa only [map_mul, he, hez] using hh

end BenderSuzuki.ZD
