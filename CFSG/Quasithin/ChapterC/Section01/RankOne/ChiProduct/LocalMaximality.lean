module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankOne
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.BlockSylow
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.KnownSimple

/-!
# Local components in chi-zero blocks and exhaustive pairs

A full-Sylow local C-component contained in a chi-zero block equals that
block. The cubic case is solvable; in both noncubic cases the rank-one cover
theorem excludes a proper nonsolvable Sylow overgroup. In the strongly
quasithin rank range, two distinct ambient chi blocks exhaust the family.
Conjugation therefore preserves their join, and C.1.29 gives its ordered
product with any characteristic-normalizer control subgroup.

The literal paired D-normalizer consumer is in Chapter14, Section06,
SourcePairedNormalizerBlocks. Source: Aschbacher--Smith C.1.29, printed p.134,
and the paired-block argument in14.6.9, printed p.1026.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct
variable {G : Type*} [Group G] [Finite G]

private theorem solvable_of_core_quotient_three {A : Type*} [Group A] [Finite A]
    (hc : Nat.card (A ⧸ pCore 2 A) = 3) : Group.IsSolvable A := by
  let : IsCyclic (A ⧸ pCore 2 A) := isCyclic_of_prime_card hc
  let : Group.IsNilpotent (pCore 2 A) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 A)).mpr
    ⟨inferInstance,inferInstance⟩

/-- The full-Sylow local-component condition makes every non-solvable
subgroup of a chi-zero block maximal among such local components. -/
theorem local_component_eq_chiZero_of_le (S : Sylow 2 G)
    {B L : Subgroup G} (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hL : IsChiZeroBlockIn L) (hBL : B ≤ L) : B = L := by
  have hns : ¬ Group.IsSolvable L := by
    intro hsol
    let := hsol
    have hBs : Group.IsSolvable B :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective hBL)
    let := hBs
    exact hB.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup G) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup G) from le_sup_left)).injective)
  have hq : IsQuasisimple (L ⧸ pCore 2 L) :=
    hL.1.short.quotient.resolve_right (fun hc => hns (solvable_of_core_quotient_three hc))
  let := hq
  have hcomp : L.IsCComponent :=
    isCComponent_of_isPPerfect_of_quasisimple_core_quotient
      hL.1.subnormal hL.1.short.twoPerfect
  rcases hL.2 with ⟨n,_,_,F,_,_,hF,_,hm⟩ | h3 | h5
  · obtain ⟨e⟩ := hm.quotient_iso
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact ChapterA.Section03.SourceEmbeddings.eq_of_rankOne_cover S hB hcomp hBL
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  · obtain ⟨e⟩ := h3.2.2.quotient_iso
    exact (hns (solvable_of_core_quotient_three (by
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]; norm_num))).elim
  · obtain ⟨e⟩ := h5.2.2.quotient_iso
    obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
    let f := e.trans ((Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2)).trans a).symm
    exact ChapterA.Section03.SourceEmbeddings.eq_of_rankOne_cover S hB hcomp hBL
      (f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
      (f.surjective.comp (QuotientGroup.mk'_surjective _))

/-- Two distinct ambient chi blocks exhaust the family in the SQTK rank range. -/
theorem chi_pair_exhausts (hf : generalizedFitting G = pCore 2 G)
    (hr : primeRank 3 G ≤ 2) {B C : Subgroup G}
    (hB : IsChiBlockIn B) (hC : IsChiBlockIn C) (hne : B ≠ C)
    {L : Subgroup G} (hL : IsChiBlockIn L) : L = B ∨ L = C := by
  by_contra! hn
  have hcard : ({X : Subgroup G | IsChiBlockIn X} : Set (Subgroup G)).ncard ≤ 2 :=
    RankOne.ChiProduct.card_chiBlocks_le_two hf hr
  have hthree : 2 < ({X : Subgroup G | IsChiBlockIn X} : Set (Subgroup G)).ncard :=
    (Set.two_lt_ncard_iff (s := {X : Subgroup G | IsChiBlockIn X})).mpr ⟨B,C,L,hB,hC,hL,hne,hn.1.symm,hn.2.symm⟩
  omega

/-- The join of the two ambient blocks is normal because conjugation permutes
an exhausted chi family. -/
theorem chi_pair_join_normal (hf : generalizedFitting G = pCore 2 G)
    (hr : primeRank 3 G ≤ 2) {B C : Subgroup G}
    (hB : IsChiBlockIn B) (hC : IsChiBlockIn C) (hne : B ≠ C) :
    (B ⊔ C).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  apply le_normalizer_iff.mpr
  intro g _ x hx
  have hp (A : Subgroup G) (hA : IsChiBlockIn A) :
      A.map (MulAut.conj g).toMonoidHom ≤ B ⊔ C := by
    rcases chi_pair_exhausts hf hr hB hC hne
      (RankOne.ChiProduct.chi_map_equiv (MulAut.conj g) hA) with he | he
    · rw [he]; exact le_sup_left
    · rw [he]; exact le_sup_right
  have hm : (B ⊔ C).map (MulAut.conj g).toMonoidHom ≤ B ⊔ C := by
    rw [Subgroup.map_sup]
    exact sup_le (hp B hB) (hp C hC)
  exact hm (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)

/-- C.1.29 gives the literal product with the prescribed control subgroup
once two distinct ambient chi-zero blocks have been identified. -/
theorem chi_pair_product_knownSimple
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hf : generalizedFitting G = pCore 2 G)
    (S : Sylow 2 G) (M : Subgroup G)
    (hM : (S : Subgroup G).characteristicNormalizerClosure ≤ M)
    {B C : Subgroup G} (hB : IsChiBlockIn B) (hC : IsChiBlockIn C)
    (hne : B ≠ C) :
    (B ⊔ C).Normal ∧ ∀ g : G, ∃ k : (B ⊔ C : Subgroup G), ∃ m : M, g = (k : G) * (m : G) := by
  have hr := hG.stronglyQuasithin 3 Nat.prime_three (by decide)
  have hb : IsChiBlockIn B := hB
  have hc : IsChiBlockIn C := hC
  have hn := chi_pair_join_normal hf hr hb hc hne
  let := hn
  refine ⟨hn,?_⟩
  obtain ⟨r,_,L,hL,_,_,hprod⟩ :=
    RankOne.ChiProduct.SelectedRankOne.ordered_chiZero_product_knownSimple hG hf S M hM
  have hle (i : Fin r) : L i ≤ B ⊔ C := by
    rcases chi_pair_exhausts hf hr hb hc hne ⟨(hL i).1,(hL i).2.chi⟩ with he | he
    · rw [he]; exact le_sup_left
    · rw [he]; exact le_sup_right
  intro g
  obtain ⟨m,b,he⟩ := hprod g
  have hp : (List.ofFn (fun i => (b i : G))).prod ∈ B ⊔ C :=
    (B ⊔ C).list_prod_mem (fun a ha => by
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      exact hle i (b i).property)
  refine ⟨⟨(m : G) * (List.ofFn (fun i => (b i : G))).prod * (m : G)⁻¹,
    hn.conj_mem _ hp m⟩,m,?_⟩
  simpa only [Subtype.coe_mk,mul_assoc,inv_mul_cancel,mul_one] using he

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct
