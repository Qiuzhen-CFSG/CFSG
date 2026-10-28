module
public import Theory.SpecificGroups.PSL2.InvolutionCentralizerSolvable
public import GorensteinWalter.PSL2DihedralSylow
public import Theory.GroupTheory.PrimeRankDihedral
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.MinimalNormalPCore
public import Theory.GroupTheory.PerfectSmallTwoAction

/-!
# Two-cores of perfect subgroups of odd-field PSL₂

A nontrivial two-core contains a nontrivial normal elementary abelian
subgroup. Dihedral Sylow two-subgroups bound its order by four, so a perfect
group centralizes it. An involution in that subgroup then places the whole
perfect subgroup inside a solvable reflected-torus centralizer, a contradiction.
The homomorphism form retains the actual two-core kernel for central covers.

This extends the prime-field result to all finite odd fields, including
square fields. Source: the component inspection in Aschbacher--Smith 4.4.11,
printed p.621; the matrix centralizers and dihedral Sylow descriptions are
Huppert II.8.3--4, as proved in the imported modules.
-/

public section
open Subgroup Theory.GroupTheory GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

private theorem odd_field_prime_power
    (F : Type*) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    IsOddPrimePower (Nat.card F) := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hc : Nat.card F = ringChar F ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hn
  refine ⟨ringChar F, n, hp, ?_, n.pos, hc⟩
  apply hp.odd_of_ne_two
  intro heq
  rw [heq] at hc
  have heven : Even (Nat.card F) := by
    rw [hc]
    exact Nat.even_pow.mpr ⟨by decide, n.pos.ne'⟩
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- A perfect subgroup of an odd-field PSL₂ has trivial two-core. -/
theorem odd_perfect_subgroup_twoCore_eq_bot
    {F : Type*} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (P : Subgroup PSL(2,F)) [Group.IsPerfect P] : pCore 2 P = ⊥ := by
  by_contra hne
  have hPne : P ≠ ⊥ := by
    intro hP
    have : Subsingleton P := by rw [hP]; infer_instance
    exact hne (Subsingleton.elim _ _)
  let : Nontrivial P := (nontrivial_iff_ne_bot P).mpr hPne
  have hF := odd_field_prime_power F hodd
  have hr : primeRank 2 PSL(2,F) ≤ 2 := by
    let S : Sylow 2 PSL(2,F) := Classical.choice inferInstance
    obtain ⟨n, _, ⟨e⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hF S
    rw [S.primeRank_eq, primeRank_equiv 2 e]
    exact dihedral_rank_le_two n
  have hrP : primeRank 2 P ≤ 2 :=
    (primeRank_le_of_injective 2 P.subtype P.subtype_injective).trans hr
  obtain ⟨E,hEn,hEne,_,hE,_⟩ := exists_minimal_normal_le_pCore hne
  let : E.Normal := hEn
  let : IsElementaryAbelian 2 E := hE
  have hEcard : Nat.card E ≤ 4 :=
    (primeRank_le_iff_elementary_card_le P).mp hrP E hE
  have hc : (⊤ : Subgroup P) ≤ centralizer (E : Set P) :=
    le_centralizer_of_isPerfect_of_card_le_four _ _ hEcard
  let : Nontrivial E := (nontrivial_iff_ne_bot E).mpr hEne
  obtain ⟨u,hu,hu1⟩ := E.exists_ne_one_of_nontrivial
  have hu2 : u ^ 2 = 1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) ⟨u,hu⟩)
  have ht : IsInvolution (u : PSL(2,F)) :=
    ⟨fun he => hu1 (Subtype.ext he), congrArg Subtype.val hu2⟩
  let C := centralizer ({(u : PSL(2,F))} : Set PSL(2,F))
  let : Group.IsSolvable C := involution_centralizer_isSolvable hF u ht
  have hPC : P ≤ C := by
    intro x hx y hy
    obtain rfl : y = (u : PSL(2,F)) := hy
    exact congrArg Subtype.val (hc (mem_top (⟨x,hx⟩ : P)) u hu)
  let : Group.IsSolvable P := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective hPC)
  exact Group.IsPerfect.not_isSolvable P inferInstance

/-- A homomorphism from a perfect group into odd-field PSL₂ kills its two-core. -/
theorem odd_perfect_hom_twoCore_le_ker
    {F : Type*} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {A : Type*} [Group A] [Group.IsPerfect A] (f : A →* PSL(2,F)) :
    pCore 2 A ≤ f.ker := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have h : (pCore 2 A).map f.rangeRestrict ≤ pCore 2 f.range :=
    le_sSup ⟨(inferInstance : (pCore 2 A).Normal).map f.rangeRestrict
      f.rangeRestrict_surjective, pCore_isPGroup.map f.rangeRestrict⟩
  rw [odd_perfect_subgroup_twoCore_eq_bot hodd f.range] at h
  have hk := (Subgroup.map_eq_bot_iff _).mp (bot_unique h)
  intro a ha
  exact congrArg Subtype.val (hk ha)

end Theory.PSL2
