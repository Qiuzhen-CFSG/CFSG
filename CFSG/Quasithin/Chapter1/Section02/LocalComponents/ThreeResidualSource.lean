module
public import Theory.GroupTheory.TwoOrbitThree.Quotient
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.PSL2.PrimeCardInnerIndex
public import Theory.SpecificGroups.SL2.SmallOddComparisons
/-!
# The cubic two-orbit residual for the actual rank-one models

The even-field PSL2 case uses the pure-field cubic obstruction in the pair
of automorphism groups. The odd prime-field case has outer order two;
perfectness excludes the degenerate field of order three. The original
component and its conjugate therefore have three-prime index. Simplicity
of the two-core quotient and component perfectness give the reverse
residual containment, retaining all actual groups and quotient maps.
Source: Aschbacher--Smith 1.2.2(a), p.504, 1 March 2004; the two model
families used in 1.3.4(1) and 15.4.20.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]

theorem rankOne_pair_index_coprime_three
    {L : Subgroup G} (hL : L.IsCComponent) [IsQuasisimple (L ⧸ pCore 2 L)]
    (hi : (normalizer (L : Set G)).index = 2) (t : G) (ht : t ∉ normalizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)) (hr : primeRank 3 G ≤ 2)
    (hm : (∃ n, ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n)) ∨
      ∃ p, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 p) :
    Nat.Coprime 3 (L ⊔ L.conjBy t).index := by
  rcases hm with ⟨n,F,hF,hfin,hcard,⟨e⟩⟩ | ⟨p,hp,ho,F,hF,hfin,hcard,⟨e⟩⟩
  · let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact TwoOrbitThree.binary_cComponent_pair_index_coprime_three hL hi t ht hd hr F e
  · let : Fact p.Prime := ⟨hp⟩
    have hlarge : 3 < p := by
      have hge := hp.two_le
      have hpne2 : p ≠ 2 := by obtain ⟨k,hk⟩ := ho; omega
      by_contra hn
      have hp3 : p = 3 := by omega
      have hperfect : Group.IsPerfect PSL(2,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three (hcard.trans hp3) hperfect
    have hz : center (L ⧸ pCore 2 L) = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      have hh : e x ∈ center PSL(2,F) := (centerCongr e ⟨x,hx⟩).property
      rw [GorensteinWalter.psl2_center_eq_bot F,mem_bot] at hh
      exact e.map_eq_one_iff.mp hh
    apply TwoOrbitThree.outer_cComponent_pair_index_coprime_three hL hi t ht hz hd hr
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    change Nat.Coprime 3 (MulAut.innerSubgroup PSL(2,F)).index
    rw [Theory.PSL2.prime_card_inner_index F ho hlarge hcard]
    decide

theorem rankOne_pair_eq_primeToResidual_three
    {L : Subgroup G} (hL : L.IsCComponent) [IsQuasisimple (L ⧸ pCore 2 L)]
    [IsSimpleGroup (L ⧸ pCore 2 L)]
    (hi : (normalizer (L : Set G)).index = 2) (t : G) (ht : t ∉ normalizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)) (hr : primeRank 3 G ≤ 2)
    (hm : (∃ n, ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n)) ∨
      ∃ p, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 p) :
    L ⊔ L.conjBy t = primeToResidual 3 G := by
  let : Group.IsPerfect L := hL.perfect
  have hperfect : IsPPerfect 2 L := by
    intro N hN hquot
    let := hN
    have hsub : Subsingleton (L ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hquot.isNilpotent
    apply eq_top_iff.mpr
    intro l _
    exact (QuotientGroup.eq_one_iff l).mp (Subsingleton.elim _ _)
  have hLR : L ≤ primeToResidual 3 G := le_primeToResidual_of_eq_top 3 L
    (primeToResidual_eq_top_of_simple_quotient 3 2 (pCore 2 L) pCore_isPGroup hperfect hd)
  let : (L ⊔ L.conjBy t).Normal := TwoOrbitThree.pair_normal_of_index_two L hi t ht
  apply le_antisymm
  · apply sup_le hLR
    rintro x ⟨l,hl,rfl⟩
    exact (inferInstance : (primeToResidual 3 G).Normal).conj_mem l (hLR hl) t
  · exact primeToResidual_le _ (rankOne_pair_index_coprime_three hL hi t ht hd hr hm)
end CFSG.Quasithin.Chapter1.Section02
