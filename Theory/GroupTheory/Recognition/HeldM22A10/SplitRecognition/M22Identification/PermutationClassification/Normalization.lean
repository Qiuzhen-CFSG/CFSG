module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.PermutationClassification.Candidates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.PermutationClassification.Normalization.SquareAdjustment
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.PermutationClassification.Normalization.ElevenFiveCoordinates

/-!
# Janko's normalized degree-22 generators

The faithful action in `PermutationData` admits a relabeling containing the
concrete eleven- and five-generators, together with an order-four generator
satisfying all the square conditions used by the terminal enumeration.

First the two fixed points of the five-generator give origins for the two
eleven-cycles. Then conjugating the order-four generator by a power of the
five-generator gives the displayed square. This latter change is internal
to the conjugated image subgroup. Injectivity and permutation conjugation
preserve the required orders and fixed-point counts.

This is the conditional coordinate argument from Section 9 of Z. Janko,
*A characterization of the Mathieu simple groups, I*, J. Algebra 9 (1968),
pp.17–18, DOI 10.1016/0021-8693(68)90002-1. It constructs the normalization
from the supplied action data and is independent of candidate enumeration.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.PermutationClassification

open JankoModel

private theorem fixed_count_conj (p g : Equiv.Perm (Fin 22)) :
    (Finset.univ.filter (fun x => (MulAut.conj p) g x = x)).card =
      (Finset.univ.filter (fun x => g x = x)).card := by
  apply Finset.card_equiv p.symm
  intro x
  simp only [Finset.mem_filter_univ]
  change p (g (p.symm x)) = x ↔ g (p.symm x) = p.symm x
  constructor
  · intro h
    apply p.injective
    rwa [p.apply_symm_apply]
  · intro h
    rw [h, p.apply_symm_apply]

private theorem normalized_of_coordinates
    (H : Subgroup (Equiv.Perm (Fin 22)))
    (hl : ell ∈ H) (hm : m ∈ H) (n : Equiv.Perm (Fin 22)) (hn : n ∈ H)
    (hnord : orderOf n = 4)
    (hnfixed : (Finset.univ.filter (fun x => n x = x)).card = 2)
    (hsfixed : (Finset.univ.filter (fun x => (n ^ 2) x = x)).card = 6)
    (hconj : n * m * n⁻¹ = m ^ 2) : Nonempty (NormalizedGenerators H) := by
  obtain ⟨i, hi⟩ := exists_power_squareNormalized n hconj hsfixed
  let f := MulAut.conj (m ^ i.val)
  have hfm : f m = m := by
    change m ^ i.val * m * (m ^ i.val)⁻¹ = m
    rw [(Commute.refl m).pow_left i.val |>.eq, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨⟨f n, hl, hm, ?_, ?_, ?_, ?_, ?_, hi⟩⟩
  · exact H.mul_mem (H.mul_mem (H.pow_mem hm _) hn) (H.inv_mem (H.pow_mem hm _))
  · exact (f.orderOf_eq n).trans hnord
  · exact (fixed_count_conj (m ^ i.val) n).trans hnfixed
  · rw [← map_pow f n 2]
    exact (fixed_count_conj (m ^ i.val) (n ^ 2)).trans hsfixed
  · calc
      f n * m * (f n)⁻¹ = f (n * m * n⁻¹) := by
        rw [map_mul f, map_mul f, map_inv f, hfm]
      _ = f (m ^ 2) := congrArg f hconj
      _ = m ^ 2 := by rw [map_pow f, hfm]

universe u

/-- The faithful action data admits Janko's simultaneous generator coordinates
and the subsequent square normalization. No candidate enumeration is used. -/
public theorem exists_normalizedGenerators {G : Type u} [Group G]
    (R : M22Identification.PermutationData G) :
    ∃ p : Equiv.Perm (Fin 22),
      Nonempty (NormalizedGenerators (R.rho.range.map (MulAut.conj p).toMonoidHom)) := by
  have hlord : orderOf (R.rho R.ell) = 11 :=
    (orderOf_injective R.rho R.faithful R.ell).trans R.ell_order
  have hlfixed : (Finset.univ.filter (fun x => R.rho R.ell x = x)).card = 0 := by
    have h := R.order_fixed R.ell
    simpa [R.ell_order, allowedOrderFixedPairs] using h
  have hmfixed : (Finset.univ.filter (fun x => R.rho R.m x = x)).card = 2 := by
    have h := R.order_fixed R.m
    simpa [R.m_order, allowedOrderFixedPairs] using h
  have hfree : ∀ x, R.rho R.ell x ≠ x := by
    intro x hx
    have he := Finset.card_eq_zero.mp hlfixed
    have hxmem : x ∈ Finset.univ.filter (fun x => R.rho R.ell x = x) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
    rw [he] at hxmem
    exact Finset.notMem_empty x hxmem
  have hlm : R.rho R.m * R.rho R.ell * (R.rho R.m)⁻¹ = (R.rho R.ell) ^ 4 := by
    simpa only [map_mul, map_inv, map_pow] using congrArg R.rho R.m_conjugates_ell
  obtain ⟨p, hpell, hpm⟩ := exists_eleven_five_coordinates
    (R.rho R.ell) (R.rho R.m) hlord hfree hmfixed hlm
  let f := (MulAut.conj p).toMonoidHom.comp R.rho
  let H := R.rho.range.map (MulAut.conj p).toMonoidHom
  have hmem (g : G) : f g ∈ H :=
    Subgroup.mem_map_of_mem _ ⟨g, rfl⟩
  have hl : ell ∈ H := hpell ▸ hmem R.ell
  have hm : m ∈ H := hpm ▸ hmem R.m
  have hnord : orderOf (f R.n) = 4 := by
    exact ((MulAut.conj p).orderOf_eq (R.rho R.n)).trans
      ((orderOf_injective R.rho R.faithful R.n).trans R.n_order)
  have hnfixed : (Finset.univ.filter (fun x => R.rho R.n x = x)).card = 2 := by
    have h := R.order_fixed R.n
    simpa [R.n_order, allowedOrderFixedPairs] using h
  have hsord : orderOf (R.n ^ 2) = 2 := by
    rw [orderOf_pow' R.n (by decide : (2 : ℕ) ≠ 0), R.n_order]
    decide
  have hsfixed : (Finset.univ.filter (fun x => R.rho (R.n ^ 2) x = x)).card = 6 := by
    have h := R.order_fixed (R.n ^ 2)
    simpa [hsord, allowedOrderFixedPairs] using h
  have hnm : f R.n * m * (f R.n)⁻¹ = m ^ 2 := by
    have hm' : f R.m = m := hpm
    rw [← hm', ← map_inv f, ← map_mul f, ← map_mul f, R.n_conjugates_m, map_pow f]
  refine ⟨p, normalized_of_coordinates H hl hm (f R.n) (hmem R.n) hnord ?_ ?_ hnm⟩
  · exact (fixed_count_conj p (R.rho R.n)).trans hnfixed
  · rw [← map_pow f]
    exact (fixed_count_conj p (R.rho (R.n ^ 2))).trans hsfixed

end Theory.GroupTheory.HeldM22A10.M22Identification.PermutationClassification
