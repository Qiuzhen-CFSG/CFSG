module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.Preparation
public import CFSG.Quasithin.ChapterA.Section02.OddPrimeRank
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.GroupTheory.PGroup.OmegaCoprimeAction

/-!
# Involutions in the component centralizer of an SQTK quotient

A component centralizes the nilpotent kernel of the prepared cover, so its
centralizer pulls back to the literal component centralizer upstairs. An
involution lifts through the odd kernel by taking an odd power of any lift.
If the cyclic three-core's first omega subgroup lies in the lifted component,
coprime action forces that involution to fix the entire three-core. Its image
then centralizes F*(G), which is impossible when O₂(G) is trivial.

The rank-transfer lemma uses the cyclic Sylow criterion at the odd prime
three; no invariance of rank across a central quotient is asserted.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.7,
printed pp.105–106, and A.2.7, printed p.34.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.CoverCentralizer
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

omit [Finite G] in
/-- A surjective component image of three-rank greater than one has a lift
of three-rank greater than one. -/
theorem lift_rank {H : Type*} [Group H] [Finite H]
    (f : H →* G) (M : Subgroup H) {L : Subgroup G}
    (hmap : M.map f = L) (hr : 1 < primeRank 3 L) : 1 < primeRank 3 M := by
  by_contra hn
  have hm : primeRank 3 M ≤ 1 := by omega
  have hi := PrimeRank.le_of_surjective_of_source_le_one (by decide : 3 ≠ 2)
    (f.subgroupMap M) (f.subgroupMap_surjective M) hm
  rw [hmap] at hi
  omega

omit [Finite G] in
/-- The nilpotent kernel centralizes each actual component of the cover. -/
theorem centralizer_comap (c : PreparedCover K G)
    {M : Subgroup c.Cover} (hM : IsComponent c.Cover M) :
    (centralizer (M.map c.projection : Set G)).comap c.projection =
      centralizer (M : Set c.Cover) := by
  let := hM.2
  apply comap_centralizer_map_eq_of_perfect
  rcases hM.normal_dichotomy c.projection.ker with h | h
  · let : Group.IsNilpotent c.projection.ker := c.kernel_nilpotent
    let : Group.IsSolvable M := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective h)
    let : IsSimpleGroup (M ⧸ center M) := IsQuasisimple.simple
    let : Nontrivial M := (QuotientGroup.mk'_surjective (center M)).nontrivial
    exact (Group.IsPerfect.not_isSolvable M inferInstance).elim
  · exact commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans h)

omit [Finite G] in
/-- An involution lifts with the same order through the actual odd kernel. -/
theorem lift_involution (c : PreparedCover K G)
    (s : G) (hs : orderOf s = 2) :
    ∃ t : c.Cover, orderOf t = 2 ∧ c.projection t = s := by
  obtain ⟨a, ha⟩ := c.surjective s
  have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
  let n : c.projection.ker := ⟨a ^ 2, by simp only [MonoidHom.mem_ker, map_pow, ha, hs2]⟩
  have hn : Odd (orderOf n) := c.kernel_odd.of_dvd_nat (orderOf_dvd_natCard n)
  have he : c.projection (a ^ orderOf n) = s := by
    rw [map_pow, ha]
    obtain ⟨k, hk⟩ := hn
    rw [hk, pow_add, pow_mul, hs2]
    simp
  refine ⟨a ^ orderOf n, ?_, he⟩
  apply orderOf_eq_prime
  · have hn1 := congrArg c.projection.ker.subtype (pow_orderOf_eq_one n)
    change (a ^ 2) ^ orderOf n = 1 at hn1
    simpa only [← pow_mul, Nat.mul_comm] using hn1
  · intro ht
    have hs1 : s = 1 := he.symm.trans (by rw [ht, map_one])
    simp [hs1] at hs

/-- Fixing the first omega subgroup forces an involution to fix the cyclic core. -/
theorem centralizes_threeCore_of_involution (H : Type*) [Group H] [Finite H]
    (M : Subgroup H) (hcyc : IsCyclic (pCore 3 H))
    (hω : (omega₁ (pCore 3 H) (p := 3)).map (pCore 3 H).subtype ≤ M)
    (t : H) (ht : orderOf t = 2) (htM : t ∈ centralizer (M : Set H)) :
    t ∈ centralizer (pCore 3 H : Set H) := by
  let : IsCyclic (pCore 3 H) := hcyc
  let T := zpowers t
  have hT : IsPGroup 2 T := by
    apply IsPGroup.of_card (n := 1)
    simp only [T, Nat.card_zpowers, ht, pow_one]
  let α : T →* MulAut (pCore 3 H) :=
    (MulAut.conjNormal : H →* MulAut (pCore 3 H)).comp T.subtype
  have hfix := OmegaAction.fixes_of_fixes_omega_one
    (p := 3) pCore_isPGroup α
    (IsPGroup.coprime_card_of_ne 2 3 (by decide) T (pCore 3 H) hT pCore_isPGroup) (by
      intro a x hx
      have hTcentral : T ≤ centralizer (M : Set H) := zpowers_le.mpr htM
      have hxc : (x : H) ∈ M := hω (mem_map_of_mem _ hx)
      have hcomm := mem_centralizer_iff.mp (hTcentral a.property) (x : H) hxc
      apply Subtype.ext
      change (a : H) * (x : H) * (a : H)⁻¹ = x
      rw [← hcomm, mul_inv_cancel_right])
  intro x hx
  have he := congrArg (fun f : MulAut (pCore 3 H) => (f ⟨x, hx⟩ : H))
    (hfix ⟨t, mem_zpowers t⟩)
  change t * x * t⁻¹ = x at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- B.5.7's odd-centralizer argument with explicit, literal cover data. -/
theorem odd_centralizer (c : PreparedCover K G)
    {M : Subgroup c.Cover} {L : Subgroup G}
    (hM : IsComponent c.Cover M) (hmap : M.map c.projection = L)
    (hcore : pCore 2 G = ⊥)
    (hfit : generalizedFitting G = (L ⊔ pCore 3 G) ⊔ center G)
    (hcyc : IsCyclic (pCore 3 c.Cover))
    (hω : (omega₁ (pCore 3 c.Cover) (p := 3)).map
      (pCore 3 c.Cover).subtype ≤ M) :
    Odd (Nat.card (centralizer (L : Set G))) := by
  classical
  by_contra hodd
  have heven : 2 ∣ Nat.card (centralizer (L : Set G)) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card'
    (G := centralizer (L : Set G)) 2 heven
  have hsG : orderOf (s : G) = 2 := (orderOf_coe s).trans hs
  obtain ⟨t, ht, hts⟩ := lift_involution c (s : G) hsG
  have htM : t ∈ centralizer (M : Set c.Cover) := by
    rw [← centralizer_comap c hM]
    change c.projection t ∈ centralizer (M.map c.projection : Set G)
    rw [hts, hmap]
    exact s.property
  have htP := centralizes_threeCore_of_involution c.Cover M hcyc hω t ht htM
  have hsP : (s : G) ∈ centralizer (pCore 3 G : Set G) := by
    rw [← c.map_pCore 3]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa only [map_mul, hts] using
      congrArg c.projection (mem_centralizer_iff.mp htP y hy)
  have hsF : (s : G) ∈ centralizer (generalizedFitting G : Set G) := by
    rw [hfit]
    apply (le_centralizer_iff.mpr ?_ :
      zpowers (s : G) ≤ centralizer (↑((L ⊔ pCore 3 G) ⊔ center G) : Set G))
      (mem_zpowers _)
    apply sup_le
    · exact sup_le (le_centralizer_iff.mp (zpowers_le.mpr s.property))
        (le_centralizer_iff.mp (zpowers_le.mpr hsP))
    · exact center_le_centralizer _
  have hp : IsPGroup 2 (zpowers (s : G)) := by
    apply IsPGroup.of_card (n := 1)
    simp only [Nat.card_zpowers, hsG, pow_one]
  have hs1 : (s : G) = 1 :=
    (QuasisimpleSections.disjoint_centralizer_fitting hcore _ hp).le_bot
      ⟨mem_zpowers _, hsF⟩
  simp [hs1] at hsG

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.CoverCentralizer
