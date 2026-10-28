module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups.Intersection
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.OvergroupModels
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Mathlib.NumberTheory.Multiplicity
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups.TorusExtensions.InvolutionModels

/-!
# Dihedral inner intersections give full torus normalizers

Let M be a maximal subgroup of odd PGL₂ containing a Sylow two-subgroup.
Its literal PSL₂ intersection has index two in M. If that intersection is
dihedral of order 2z, divisibility by the ambient Sylow order forces z to
be even. For z > 2 the unique central involution of the intersection is
fixed by conjugation by M. For z = 2, M has order eight; its normal
four-group meets its center nontrivially and again supplies an involution.

Thus M centralizes an inner involution. Its ambient centralizer is proper
because PGL₂ is centerless, so maximality identifies M with that whole
centralizer. `InvolutionModels` supplies its actual dihedral isomorphism,
with rotation order q-1 or q+1. All embeddings are the canonical maps from
`Intersection`; normality is used only inside M.

This discharges the dihedral premise of the prime-field maximal-overgroup
assembly used in Aschbacher--Smith E.1.14(6), printed p.214, citing
Aschbacher (1982), Lemma 4.10. No subgroup-classification conclusion or
E-generation statement is assumed.
-/

noncomputable section
open Subgroup GorensteinWalter

private theorem central_rotation_mem {n : ℕ} (hn : 2 < n)
    (x : DihedralGroup n) (hx : x ∈ center (DihedralGroup n)) :
    x ∈ zpowers (DihedralGroup.r 1 : DihedralGroup n) := by
  let : NeZero n := ⟨by omega⟩
  cases x with
  | r i =>
    have h := pow_mem (mem_zpowers (DihedralGroup.r 1 : DihedralGroup n)) i.val
    simpa only [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val] using h
  | sr i =>
    have hi : i - 1 = i + 1 := DihedralGroup.sr.inj
      (mem_center_iff.mp hx (DihedralGroup.r 1))
    have htwo : (2 : ZMod n) = 0 := by linear_combination -hi
    have hv := congrArg ZMod.val htwo
    have hval : ZMod.val (2 : ZMod n) = 2 := ZMod.val_natCast_of_lt hn
    rw [hval, ZMod.val_zero] at hv
    omega

private theorem rotation_involution_central {n : ℕ} {i : ZMod n}
    (hi : (DihedralGroup.r i) ^ 2 = 1) :
    DihedralGroup.r i ∈ center (DihedralGroup n) := by
  have hii : i + i = 0 := DihedralGroup.r.inj (by simpa [pow_two] using hi)
  have hiNeg : -i = i := neg_eq_iff_add_eq_zero.mpr hii
  rw [mem_center_iff]
  rintro (j | j)
  · simp [add_comm]
  · simp [sub_eq_add_neg, hiNeg]

private theorem dihedral_unique_central_involution {n : ℕ}
    (hn : 2 < n) (heven : 2 ∣ n) :
    ∃! x : DihedralGroup n, orderOf x = 2 ∧ x ∈ center (DihedralGroup n) := by
  let : NeZero n := ⟨by omega⟩
  let x : DihedralGroup n := (DihedralGroup.r 1) ^ (n / 2)
  have hx : orderOf x = 2 := by
    simpa only [DihedralGroup.orderOf_r_one] using
      (orderOf_pow_orderOf_div (x := (DihedralGroup.r 1 : DihedralGroup n))
        (by simpa using (show n ≠ 0 by omega)) (by simpa using heven))
  have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  have hxC : x ∈ center (DihedralGroup n) := by
    dsimp [x] at hx2 ⊢
    rw [DihedralGroup.r_one_pow] at hx2 ⊢
    exact rotation_involution_central hx2
  refine ⟨x, ⟨hx, hxC⟩, ?_⟩
  intro y hy
  let R := zpowers (DihedralGroup.r 1 : DihedralGroup n)
  let a : R := ⟨x, central_rotation_mem hn x hxC⟩
  let b : R := ⟨y, central_rotation_mem hn y hy.2⟩
  have ha : orderOf a = 2 := (Subgroup.orderOf_coe a).symm.trans hx
  have hb : orderOf b = 2 := (Subgroup.orderOf_coe b).symm.trans hy.1
  exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two hb ha)

private theorem normal_dihedral_has_central_involution
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    {n : ℕ} (hn : 2 < n) (heven : 2 ∣ n) (e : N ≃* DihedralGroup n) :
    ∃ x : G, x ∈ N ∧ orderOf x = 2 ∧ x ∈ center G := by
  obtain ⟨d, hd, hdUnique⟩ := dihedral_unique_central_involution hn heven
  let x : N := e.symm d
  have hxorder : orderOf x = 2 := (e.symm.orderOf_eq d).trans hd.1
  have hxC : x ∈ center N := MulEquivClass.apply_mem_center e.symm hd.2
  refine ⟨x, x.property, (Subgroup.orderOf_coe x).trans hxorder, ?_⟩
  rw [mem_center_iff]
  intro g
  let a : MulAut N := MulAut.conjNormal g
  have haxC : a x ∈ center N := MulEquivClass.apply_mem_center a hxC
  have heax : e (a x) = d := hdUnique _
    ⟨(e.orderOf_eq _).trans ((a.orderOf_eq x).trans hxorder),
      MulEquivClass.apply_mem_center e haxC⟩
  have hax : a x = x := e.injective (heax.trans (e.apply_symm_apply d).symm)
  have hconj : g * (x : G) * g⁻¹ = x := congrArg Subtype.val hax
  exact mul_inv_eq_iff_eq_mul.mp hconj

private theorem normal_four_has_central_involution
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 8)
    (N : Subgroup G) [N.Normal] (e : N ≃* DihedralGroup 2) :
    ∃ x : G, x ∈ N ∧ orderOf x = 2 ∧ x ∈ center G := by
  let : Fact (IsPGroup 2 G) := ⟨IsPGroup.of_card (n := 3) (by simpa using hG)⟩
  let : Nontrivial N := e.toEquiv.nontrivial
  obtain ⟨x, hxne, hxC⟩ := exists_nontrivial_center_mem_normal N (p := 2)
  have hsq : x ^ 2 = 1 := by
    apply e.injective
    simpa using (show ∀ y : DihedralGroup 2, y ^ 2 = 1 from by decide) (e x)
  have hxorder : orderOf x = 2 := orderOf_eq_prime hsq hxne
  exact ⟨x, x.property, (Subgroup.orderOf_coe x).trans hxorder, hxC⟩

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups

variable {F : Type*} [Field F] [Finite F]

private instance finitePGLTorus : Finite (PGL2 F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- An ambient Sylow two-subgroup forces the inner dihedral rotation order to be even. -/
public theorem inner_dihedral_parameter_even (hF : IsOddPrimePower (Nat.card F))
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F))
    (hTM : (T : Subgroup _) ≤ M) {z : ℕ}
    (hcard : Nat.card (inner M) = 2 * z) : 2 ∣ z := by
  have hodd : Odd (Nat.card F) := by
    obtain ⟨p, f, _, hp, _, hq⟩ := hF
    rw [hq]
    exact hp.pow
  have h8G : 2 ^ 3 ∣ Nat.card (PGL2 F) := by
    rw [pgl2_card_formula F]
    exact dvd_mul_of_dvd_right (Nat.eight_dvd_sq_sub_one_of_odd hodd) _
  have h8T : 2 ^ 3 ∣ Nat.card T := T.pow_dvd_card_of_pow_dvd_card h8G
  have h8M : 8 ∣ Nat.card M := h8T.trans (Subgroup.card_dvd_of_le hTM)
  rw [card_eq_two_mul_inner hF T M hTM, hcard] at h8M
  obtain ⟨a, ha⟩ := h8M
  exact ⟨a, by omega⟩

/-- The normal dihedral inner intersection supplies an inner involution
centralized by the whole Sylow overgroup, including the four-group case. -/
public theorem exists_inner_involution_centralized_of_dihedral
    (hF : IsOddPrimePower (Nat.card F))
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F))
    (hTM : (T : Subgroup _) ≤ M) {z : ℕ}
    (hcard : Nat.card (inner M) = 2 * z) (e : inner M ≃* DihedralGroup z) :
    ∃ s : PGL2 F, s ∈ innerRange F ∧ IsInvolution s ∧
      M ≤ centralizer ({s} : Set (PGL2 F)) := by
  have heven := inner_dihedral_parameter_even hF T M hTM hcard
  have hzpos : 0 < z := by
    have h := Nat.card_pos (α := inner M)
    rw [hcard] at h
    omega
  let : (innerIn M).Normal := innerIn_normal hF M
  let eN : innerIn M ≃* DihedralGroup z := (innerEquiv M).symm.trans e
  have hcentral : ∃ x : M, x ∈ innerIn M ∧ orderOf x = 2 ∧ x ∈ center M := by
    by_cases hz : z = 2
    · subst z
      exact normal_four_has_central_involution
        (by rw [card_eq_two_mul_inner hF T M hTM, hcard]) (innerIn M) eN
    · exact normal_dihedral_has_central_involution (innerIn M)
        (by obtain ⟨k, hk⟩ := heven; omega) heven eN
  obtain ⟨x, hxN, hxorder, hxC⟩ := hcentral
  have hxorderG : orderOf (x : PGL2 F) = 2 := (Subgroup.orderOf_coe x).trans hxorder
  refine ⟨x, hxN, ⟨?_, ?_⟩, ?_⟩
  · intro hx
    rw [hx, orderOf_one] at hxorderG
    omega
  · simpa only [hxorderG] using pow_orderOf_eq_one (x : PGL2 F)
  · intro y hy
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mem_center_iff.mp hxC ⟨y, hy⟩)

/-- The remaining geometric input is the actual dihedral model for an inner
involution centralizer. Maximality identifies the whole original overgroup. -/
private theorem torusModel_of_inner_dihedral_of_involution_centralizers
    (hF : IsOddPrimePower (Nat.card F))
    (hcentralizers : ∀ s : PGL2 F, s ∈ innerRange F → IsInvolution s →
      ∃ n : ℕ, (n = Nat.card F - 1 ∨ n = Nat.card F + 1) ∧
        Nonempty (centralizer ({s} : Set (PGL2 F)) ≃* DihedralGroup n))
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F))
    (hM : IsCoatom M) (hTM : (T : Subgroup _) ≤ M) {z : ℕ}
    (hcard : Nat.card (inner M) = 2 * z) (e : inner M ≃* DihedralGroup z) :
    ∃ n : ℕ, (n = Nat.card F - 1 ∨ n = Nat.card F + 1) ∧
      Nonempty (M ≃* DihedralGroup n) := by
  obtain ⟨s, hsinner, hs, hMC⟩ :=
    exists_inner_involution_centralized_of_dihedral hF T M hTM hcard e
  have hCne : centralizer ({s} : Set (PGL2 F)) ≠ ⊤ := by
    intro hC
    have hsC : s ∈ center (PGL2 F) :=
      (centralizer_eq_top_iff_subset.mp hC) (Set.mem_singleton s)
    rw [pgl2_center_eq_bot F, mem_bot] at hsC
    exact hs.1 hsC
  have hCM := (hM.le_iff_eq hCne).mp hMC
  obtain ⟨n, hn, ⟨en⟩⟩ := hcentralizers s hsinner hs
  exact ⟨n, hn, ⟨(MulEquiv.subgroupCongr hCM.symm).trans en⟩⟩


/-- A maximal Sylow overgroup with dihedral inner intersection is the full
centralizer of an inner involution, hence a full dihedral torus normalizer. -/
public theorem torusModel_of_inner_dihedral
    (hF : IsOddPrimePower (Nat.card F)) (hlarge : 3 < Nat.card F)
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F))
    (hM : IsCoatom M) (hTM : (T : Subgroup _) ≤ M) {z : ℕ}
    (hcard : Nat.card (inner M) = 2 * z) (he : Nonempty (inner M ≃* DihedralGroup z)) :
    ∃ n : ℕ, (n = Nat.card F - 1 ∨ n = Nat.card F + 1) ∧
      Nonempty (M ≃* DihedralGroup n) := by
  obtain ⟨e⟩ := he
  exact torusModel_of_inner_dihedral_of_involution_centralizers hF
    (inner_involution_centralizer_model hF hlarge) T M hM hTM hcard e

/-- The exact dihedral premise of `sylowOvergroupModel_of_inner_extension_cases`.
The proof in fact does not need Dickson's extra divisibility condition. -/
public theorem prime_torusModel_of_inner_dihedral
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hpgt : 5 < p)
    (hFcard : Nat.card F = p)
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F))
    (hM : IsCoatom M) (hTM : (T : Subgroup _) ≤ M)
    (z : ℕ) (_hz : z ∣ (Nat.card F - 1) / 2 ∨ z ∣ (Nat.card F + 1) / 2)
    (hcard : Nat.card (inner M) = 2 * z) (he : Nonempty (inner M ≃* DihedralGroup z)) :
    ∃ n : ℕ, (n = Nat.card F - 1 ∨ n = Nat.card F + 1) ∧
      Nonempty (M ≃* DihedralGroup n) := by
  have hF : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, Fact.out, hpodd, le_rfl, by simpa using hFcard⟩
  exact torusModel_of_inner_dihedral hF (by omega) T M hM hTM hcard he
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups
