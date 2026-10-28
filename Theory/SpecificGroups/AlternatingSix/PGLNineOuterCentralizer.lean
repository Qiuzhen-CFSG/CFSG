module
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import GorensteinWalter.PGL2LowTorus
public import GorensteinWalter.PGL2OuterInvolutionFusion
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# Outer involution centralizers in the actual PGL₂(9)

The low torus has order ten, since its half-order is odd. Its reflected
centralizer has order twenty. Outer involution fusion transports this
cardinality to every involution outside the actual derived subgroup.
In particular no such involution centralizes an element of order three.

Source: the reflected torus and outer involution calculations in ABG II.3,
as used in Baumeister, A geometry for groups of J₃-type, Lemma 2.4.
-/

public noncomputable section
open Subgroup GorensteinWalter Atlas.Comparisons.Exceptional
namespace AlternatingSix.PGLNineOuterCentralizer

/-- Every outer involution of the literal PGL₂(9) has centralizer order twenty. -/
theorem outer_involution_centralizer_card (r : PGL2 Nine.F)
    (hr : orderOf r = 2) (hout : r ∉ commutator (PGL2 Nine.F)) :
    Nat.card (centralizer ({r} : Set (PGL2 Nine.F))) = 20 := by
  have hodd : IsOddPrimePower (Nat.card Nine.F) := by
    rw [Nine.card]
    exact ⟨3, 2, by decide, by decide, by decide, by decide⟩
  have hlarge : 3 < Nat.card Nine.F := by rw [Nine.card]; decide
  obtain ⟨U, s, t, w, _, hhalf, hcard, _, hsout, hsne, hs2,
      _, _, _, _, _, hwout, hw2, hwinv, hcent⟩ :=
    pgl2_low_two_part_torus_reflection_data Nine.F hodd hlarge
  have hU : Nat.card U = 10 := by
    rw [Nine.card] at hcard
    rcases hcard with h | h
    · norm_num [h] at hhalf
    · exact h
  have hwN : w ∈ normalizer (U : Set (PGL2 Nine.F)) := by
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      rw [hwinv x hx]
      exact U.inv_mem hx
    · intro hx
      have hh := hwinv _ hx
      have he : w * (w * x * w⁻¹) * w⁻¹ = x := by
        calc
          _ = (w * w) * x * (w * w)⁻¹ := by group
          _ = x := by rw [hw2]; simp
      rw [he] at hh
      exact hh ▸ U.inv_mem hx
  have hC : Nat.card (centralizer ({s} : Set (PGL2 Nine.F))) = 20 := by
    rw [hcent, card_sup_zpowers_of_normalizing_involution U w
      (by simpa only [pow_two] using hw2) hwout hwN, hU]
  have hrI : IsInvolution r := ⟨by intro h; simp [h] at hr,
    by simpa only [hr] using pow_orderOf_eq_one r⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (pgl2_outer_involutions_conjugate Nine.F hodd hlarge hrI
      ⟨hsne, by simpa only [pow_two] using hs2⟩ hout hsout)
  let e := MulAut.conj g
  have he : (centralizer ({r} : Set (PGL2 Nine.F))).map e.toMonoidHom =
      centralizer ({s} : Set (PGL2 Nine.F)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      change e y * s = s * e y
      rw [← hg]
      change e y * e r = e r * e y
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hy]
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      apply mem_centralizer_singleton_iff.mpr
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      change x * (g * r * g⁻¹) = (g * r * g⁻¹) * x
      rw [hg]
      exact mem_centralizer_singleton_iff.mp hx
  rw [← hC, ← he, card_map_of_injective e.injective]

/-- An actual outer involution cannot commute with a cubic element. -/
theorem outer_involution_not_commute_cubic (r x : PGL2 Nine.F)
    (hr : orderOf r = 2) (hout : r ∉ commutator (PGL2 Nine.F))
    (hx : orderOf x = 3) : ¬ Commute r x := by
  intro h
  have hd := (centralizer ({r} : Set (PGL2 Nine.F))).orderOf_dvd_natCard
    (mem_centralizer_singleton_iff.mpr h.eq.symm)
  rw [hx, outer_involution_centralizer_card r hr hout] at hd
  norm_num at hd

end AlternatingSix.PGLNineOuterCentralizer
