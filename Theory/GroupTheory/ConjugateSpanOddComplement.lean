module
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Conjugate spans above a normal Sylow subgroup

If U is invariant under a normal Sylow two-subgroup R of N, and every
noncommuting conjugator has even order, the entire N-conjugate span of U
centralizes U. Schur–Zassenhaus supplies an odd-order complement. Its
conjugates centralize U, and R preserves that centralizer.

Source application: Aschbacher–Smith, C.5.10, printed p.161.
-/
public section
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Odd-order representatives of a normal Sylow quotient centralize the original
module whenever every noncommuting conjugator has even order. -/
theorem normal_sylow_conjugate_span (R N U : Subgroup G)
    (hRN : R ≤ N) (hNR : N ≤ normalizer (R : Set G))
    (hSylow : ∃ P : Sylow 2 N, (P : Subgroup N).map N.subtype = R)
    (hUR : U ≤ R) (hRU : R ≤ normalizer (U : Set G))
    (heven : ∀ n ∈ N, ¬ U.map (MulAut.conj n⁻¹).toMonoidHom ≤ centralizer (U : Set G) →
      Even (orderOf n)) :
    conjugateSpanBy U N ≤ R ⊓ centralizer (U : Set G) := by
  let RN := R.subgroupOf N
  let : RN.Normal := (normal_subgroupOf_iff_le_normalizer hRN).mpr hNR
  obtain ⟨P,hP⟩ := hSylow
  have hPR : (P : Subgroup N) = RN := (map_injective N.subtype_injective)
    (hP.trans (map_subgroupOf_eq_of_le hRN).symm)
  have hp : IsPGroup 2 RN := hPR ▸ P.isPGroup'
  have ho : ¬ 2 ∣ RN.index := hPR ▸ P.not_dvd_index
  obtain ⟨k,hk⟩ := hp.exists_card_eq
  have hc : Nat.Coprime (Nat.card RN) RN.index := by
    rw [hk]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr ho).pow_left k
  obtain ⟨C,hC⟩ := exists_right_complement'_of_coprime hc
  have hCodd : ¬ 2 ∣ Nat.card C := by
    rw [← hC.symm.index_eq_card]
    exact ho
  have hRC : R ≤ normalizer (centralizer (U : Set G) : Set G) :=
    hRU.trans (normalizer_le_normalizer_centralizer U)
  apply le_inf (conjugateSpanBy_le hUR hNR)
  apply (closure_le _).mpr
  rintro v ⟨n,hn,u,hu,rfl⟩
  have hnprod : (⟨n,hn⟩ : N) ∈ (RN : Set N) * (C : Set N) := by
    rw [hC.mul_eq]
    trivial
  obtain ⟨r,hr,c,hc,he⟩ := hnprod
  have hcEven : ¬ Even (orderOf ((c : N) : G)) := by
    intro hh
    apply hCodd
    have hd : orderOf ((c : N) : G) ∣ Nat.card C := by
      rw [Subgroup.orderOf_coe]
      exact C.orderOf_dvd_natCard hc
    exact (even_iff_two_dvd.mp hh).trans hd
  have hcU : U.map (MulAut.conj ((c : N) : G)).toMonoidHom ≤ centralizer (U : Set G) := by
    by_contra h
    have hh := heven ((c : N) : G)⁻¹ (N.inv_mem c.property) (by simpa only [inv_inv] using h)
    exact hcEven (by simpa only [orderOf_inv] using hh)
  have hmem : (c : G) * u * (c : G)⁻¹ ∈ centralizer (U : Set G) :=
    hcU (mem_map_of_mem (MulAut.conj (c : G)).toMonoidHom hu)
  have h := (mem_normalizer_iff.mp (hRC hr) _).mp hmem
  have he' : (r : G) * (c : G) = n := congrArg (fun a : N => (a : G)) he
  rw [← he']
  have hg : (r : G) * (c : G) * u * ((r : G) * (c : G))⁻¹ =
      (r : G) * ((c : G) * u * (c : G)⁻¹) * (r : G)⁻¹ := by group
  rw [hg]
  exact h
end Subgroup
