module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.ExceptionalCorank.Kernel
public import Theory.SpecificGroups.PSL2.OddAutomorphismRank
public import Theory.SpecificGroups.PSL2.PrimePerfectCentralizer
public import Theory.GroupTheory.PerfectSmallTwoAction
public import Theory.GroupTheory.PGroup.ElementaryNormalizer

/-!
# The prime projective-linear branch of the exceptional corank bound

A nontrivial perfect subgroup of Aut(PSL₂(p)) has trivial centralizer.
The automorphism group has two-rank at most two. Therefore it cannot
normalize a nontrivial two-subgroup: a characteristic elementary subgroup
of that two-subgroup has order at most four, so the perfect group fixes it.
Apply this to the literal images of L₁ and R₁ on K/O₂(K). The local quotient
model makes the L₁ image nontrivial, while R₁ = O₂(L₁T) supplies normalization.
Thus R₁ acts trivially in this branch, a stronger result than rank at most one.

The source application combines this with the residual kernel containment.
All primes greater than three are covered; no source exceptional congruence
is excluded. The odd-kernel SL₂ branch is a separate obligation.
Source: Aschbacher--Smith, 11.1.2(2) and 11.5.6(6), pp.761,780--781.
-/

public noncomputable section

open Subgroup
open scoped MatrixGroups

private theorem two_normalized_by_perfect_eq_bot
    {G : Type*} [Group G] [Finite G] (B R : Subgroup G) [Group.IsPerfect B]
    (hr : primeRank 2 G ≤ 2) (hc : centralizer (B : Set G) = ⊥)
    (hR : IsPGroup 2 R) (hn : B ≤ normalizer (R : Set G)) : R = ⊥ := by
  by_contra hne
  obtain ⟨A,hA,hAR,hAE,hNA⟩ := exists_nontrivial_elementary_with_normalizer_le R hR hne
  have hBA : B ≤ normalizer (A : Set G) := hn.trans hNA
  let J := normalizer (A : Set G)
  let BJ := B.subgroupOf J
  let AJ := A.subgroupOf J
  let : Group.IsPerfect BJ := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBA).symm.toMonoidHom)
    (subgroupOfEquivOfLe hBA).symm.surjective
  let : AJ.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hcard : Nat.card AJ ≤ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe A.le_normalizer).toEquiv]
    exact (primeRank_le_iff_elementary_card_le G).mp hr A hAE
  have hcomm := le_centralizer_of_isPerfect_of_card_le_four BJ AJ hcard
  have hAB : A ≤ centralizer (B : Set G) := by
    intro a ha b hb
    exact (congrArg J.subtype
      (hcomm (show (⟨b,hBA hb⟩ : J) ∈ BJ from hb)
        ⟨a,A.le_normalizer ha⟩ ha)).symm
  exact hA (bot_unique (hAB.trans_eq hc))

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- A nontrivial local PSL₂ quotient excludes equality with the local two-core. -/
theorem local_ne_core_of_projective_quotient {q : ℕ} (hq : 3 < q)
    (hm : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2 q) : E.L₁ ≠ E.L₁.pCoreIn 2 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : Nontrivial (E.L₁ ⧸ pCore 2 E.L₁) := e.surjective.nontrivial
  intro he
  have ht : pCore 2 E.L₁ = ⊤ := by
    apply map_injective E.L₁.subtype_injective
    change E.L₁.pCoreIn 2 = _
    rw [← MonoidHom.range_eq_map,range_subtype]
    exact he.symm
  have hs : Subsingleton (E.L₁ ⧸ pCore 2 E.L₁) := QuotientGroup.subsingleton_iff.mpr ht
  exact not_subsingleton (E.L₁ ⧸ pCore 2 E.L₁) hs

/-- The prime PSL₂ case has trivial, hence rank at most one, R₁ action. -/
theorem radical_centralizes_of_prime_projective_quotient (hT : (T : Subgroup G) ≤ E.G₁)
    (hlocal : E.L₁ ≠ E.L₁.pCoreIn 2)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hm : ClassicalGroup.IsPSL (E.K ⧸ pCore 2 E.K) 2 p) :
    E.R₁ ≤ coreQuotientCentralizer E.K := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  let Q := E.K ⧸ pCore 2 E.K
  let N := normalizer (E.K : Set G)
  let f := coreQuotientAction E.K
  have hLN : E.L₁ ≤ N := (le_conjugateSpanBy E.L₁ E.G₁).trans E.K.le_normalizer
  have hRN : E.R₁ ≤ N :=
    ((pCoreIn_le 2 _).trans (sup_le E.L₁_le_G₁ hT)).trans E.G₁_normalizes_K
  let B := (E.L₁.subgroupOf N).map f
  let R := (E.R₁.subgroupOf N).map f
  let : Group.IsPerfect E.L₁ := E.L₁_perfect
  let : Group.IsPerfect (E.L₁.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLN).symm.toMonoidHom) (subgroupOfEquivOfLe hLN).symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.map _
  have hB : B ≠ ⊥ := by
    intro hb
    have hLK : E.L₁ ≤ E.K.pCoreIn 2 := by
      intro l hl
      let k : E.K := ⟨l,le_conjugateSpanBy E.L₁ E.G₁ hl⟩
      have hfl : f (⟨l,hLN hl⟩ : N) = 1 :=
        mem_bot.mp (hb ▸ mem_map_of_mem f (show (⟨l,hLN hl⟩ : N) ∈ E.L₁.subgroupOf N from hl))
      have hcent : QuotientGroup.mk' (pCore 2 E.K) k ∈ center Q := by
        apply mem_center_iff.mpr
        intro x
        obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 E.K) x
        have he := congrArg (fun a : MulAut Q => a (QuotientGroup.mk' (pCore 2 E.K) x)) hfl
        rw [coreQuotientAction_apply_mk] at he
        change QuotientGroup.mk' (pCore 2 E.K) (k * x * k⁻¹) =
          QuotientGroup.mk' (pCore 2 E.K) x at he
        rw [map_mul,map_mul,map_inv] at he
        exact (mul_inv_eq_iff_eq_mul.mp he).symm
      have hz : center Q = ⊥ := by
        apply bot_unique
        intro x hx
        apply mem_bot.mpr
        apply e.injective
        rw [map_one]
        apply mem_bot.mp
        rw [← GorensteinWalter.psl2_center_eq_bot F]
        apply mem_center_iff.mpr
        intro y
        obtain ⟨y,rfl⟩ := e.surjective y
        exact (map_mul e y x).symm.trans
          ((congrArg e (mem_center_iff.mp hx y)).trans (map_mul e x y))
      exact ⟨k,(QuotientGroup.eq_one_iff k).mp (mem_bot.mp (hz ▸ hcent)),rfl⟩
    exact hlocal (le_antisymm ((le_inf le_rfl hLK).trans
      (inf_pCoreIn_le_of_le 2 (le_conjugateSpanBy E.L₁ E.G₁))) (pCoreIn_le 2 _))
  have htwo : primeRank 2 (MulAut Q) ≤ 2 := by
    rw [Theory.GroupTheory.primeRank_equiv 2 (MulAut.congr e)]
    exact Theory.PSL2.prime_card_automorphism_two_rank F hF hp3
  have hc : centralizer (B : Set (MulAut Q)) = ⊥ :=
    Theory.PSL2.prime_field_automorphism_centralizer_eq_bot_of_perfect hp3 hF e B hB
  have hLR : E.L₁ ≤ normalizer (E.R₁ : Set G) :=
    ((le_sup_left : E.L₁ ≤ E.L₁ ⊔ (T : Subgroup G)).trans
      (E.L₁ ⊔ (T : Subgroup G)).le_normalizer).trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hnorm : E.L₁.subgroupOf N ≤ normalizer (E.R₁.subgroupOf N : Set N) := by
    intro l hl
    apply mem_normalizer_iff.mpr
    intro r
    exact mem_normalizer_iff.mp (hLR hl) r
  have hBR : B ≤ normalizer (R : Set (MulAut Q)) :=
    (map_mono hnorm).trans ((E.R₁.subgroupOf N).le_normalizer_map f)
  have hzero : R = ⊥ := two_normalized_by_perfect_eq_bot B R htwo hc
    ((isPGroup_pCoreIn 2 _).comap_subtype.map f) hBR
  intro r hr
  exact ⟨⟨r,hRN hr⟩,
    mem_bot.mp (hzero ▸ mem_map_of_mem f (show (⟨r,hRN hr⟩ : N) ∈ E.R₁.subgroupOf N from hr)),rfl⟩
/-- In source case (2), every elementary subgroup of R₁ has corank zero
in O₂(H₁). The local quotient marking is preceding flag geometry. -/
theorem elementary_corank_eq_zero_of_prime_projective_quotient
    (H : Subgroup G)
    (hH : H ∈ Chapter1.HOutside G ((E.L₁ ⊔ (T : Subgroup G) : Subgroup G) : Set G)
      (E.M : Set G)) (hHG : H ≤ E.G₁)
    (hr : (pResidual 2 H).map H.subtype ≤ E.K)
    (hlocal : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2 (2 ^ E.input.field.degree))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hm : ClassicalGroup.IsPSL (E.K ⧸ pCore 2 E.K) 2 p)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : A ≤ E.R₁) :
    ChapterE.subgroupCorank A (A ⊓ H.pCoreIn 2) = 0 := by
  have hT : (T : Subgroup G) ≤ E.G₁ := (le_sup_right.trans hH.1.2).trans hHG
  have hq : 3 < 2 ^ E.input.field.degree := calc
    3 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ E.input.field.degree := Nat.pow_le_pow_right (by decide)
      (by have := E.input.nonbinary; omega)
  have hC := E.radical_centralizes_of_prime_projective_quotient hT
    (E.local_ne_core_of_projective_quotient hq hlocal) hp hp3 hm
  have hcore : E.R₁ ≤ H.pCoreIn 2 :=
    (le_inf le_rfl hC).trans (E.quotientCentralizer_le_localCore hT H hH.1.2 hHG hr)
  rw [inf_eq_left.mpr (hA.trans hcore)]
  simp [ChapterE.subgroupCorank]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
