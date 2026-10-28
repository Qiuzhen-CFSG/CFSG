module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.NaturalSelected
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.NaturalGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.CubicPropagation

/-!
# The original natural seven-point short-block seed

The chosen cubic is lifted through the actual odd-center component cover.
Its preimage with O₂(G)Baum(T) has Sylow index three and the literal
omega-center movement. The same preimage and the Baumann normalizer generate
G, so C.1.21 propagates the local seed to the original component L.
Source: Aschbacher–Smith C.1.24(a), printed pp.130–131.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.SevenSource.Natural
open SymmetricSix
open Theory.SpecificGroups.SymmetricSeven.ThreePairsCubic
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry
variable {G : Type*} [Group G] [Finite G]

private theorem perfect_twoPerfect {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] : IsPPerfect 2 E := by
  intro N hn hq
  let : N.Normal := hn
  by_contra hne
  let : Nontrivial (E ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (E ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (E ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (E ⧸ N) inferInstance

/-- The source local seed on the original Baumann subgroup. All image
premises concern the same marked natural action; the central cover is retained. -/
theorem normal_characteristic_or_block_of_marked_natural_seven
    (L U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hL : L.IsCComponent) (hf : generalizedFitting G=pCore 2 G)
    (hfL : generalizedFitting L=pCore 2 L) (T : Sylow 2 G)
    (hprod : ∀ g:G,∃l∈L,∃t∈(T:Subgroup G),l*t=g)
    (q : G →* Sym) (hq : Function.Surjective q)
    (hLq : L.map q=alternatingGroup (Fin 7))
    (f : Multiplicative (BinaryPermutation.natural (Fin 7)) →* U)
    (hfU : Function.Injective f)
    (he : ∀ (g : G) (v : BinaryPermutation.natural (Fin 7)),
      f (Multiplicative.ofAdd (BinaryPermutation.naturalRepresentation (Fin 7) (q g) v)) =
        MulAut.conjNormal g (f (Multiplicative.ofAdd v)))
    (P : Sylow 2 q.ker) (hP : (P : Subgroup q.ker).map q.ker.subtype=pCore 2 G)
    (hcore : (T : Subgroup G) ⊓ q.ker=pCore 2 G)
    (hJ : (elementaryAbelianMaxJ (T : Subgroup G)).map q=pairElementary)
    (hS : (ChapterB.baumann (T : Subgroup G)).map q=pairElementary) :
    (∃ C : Subgroup (ChapterB.baumann (T : Subgroup G)), C.Characteristic ∧ C≠⊥ ∧
      (C.map (ChapterB.baumann (T : Subgroup G)).subtype).Normal) ∨ IsBlock L := by
  let := hL.perfect
  have hpL : IsPPerfect 2 L := perfect_twoPerfect
  have hres : pResidual 2 G=L := pResidual_eq_of_subnormal_product L (T:Subgroup G)
    hL.subnormal hpL T.isPGroup' hprod
  let : L.Normal := hres ▸ (inferInstance : (pResidual 2 G).Normal)
  let S := ChapterB.baumann (T : Subgroup G)
  let R := pCore 2 G ⊔ S
  have hRT : R ≤ T := sup_le (pCore_isPGroup.le_sylow_of_normal T) inf_le_left
  have hpR : IsPGroup 2 R := T.isPGroup'.to_le hRT
  have hQR : pCore 2 G ≤ R := le_sup_left
  have hQ : pCore 2 G ≤ q.ker := hcore.symm.le.trans inf_le_right
  have hRq : R.map q=pairElementary := by
    rw [Subgroup.map_sup,(Subgroup.map_eq_bot_iff _).mpr hQ,bot_sup_eq]
    exact hS
  have hRker : R ⊓ q.ker=pCore 2 G := by
    apply le_antisymm
    · exact (inf_le_inf_right _ hRT).trans_eq hcore
    · exact le_inf hQR hQ
  have hBaum : ChapterB.baumann R=S :=
    (ChapterB.lemma_B_2_3_4 (T : Subgroup G) R le_sup_right hRT).symm
  have hJR : elementaryAbelianMaxJ (T : Subgroup G) ≤ R :=
    (ChapterB.elementaryAbelianMaxJ_le_baumann (T : Subgroup G)).trans le_sup_right
  have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq R (T : Subgroup G) hRT
  have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le (T : Subgroup G) R hJR
  have horder := le_antisymm hsmall.1 hlarge.1
  have hJeq : elementaryAbelianMaxJ R=elementaryAbelianMaxJ (T : Subgroup G) :=
    le_antisymm (hsmall.2 horder) (hlarge.2 horder.symm)
  have hrJ : swap01 ∈ (elementaryAbelianMaxJ R).map q := by
    rw [hJeq,hJ]
    exact pairElementary_generators.1
  have hUR : U ≤ R := (show U ≤ pCore 2 G from
    le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩).trans hQR
  have hgen : L ⊔ (T : Subgroup G)=⊤ := by
    apply top_unique
    intro g _
    obtain ⟨l,hl,t,ht,rfl⟩ := hprod g
    exact mul_mem (mem_sup_left hl) (mem_sup_right ht)
  obtain ⟨M,hML,hM,hn,hMc⟩ := exists_quotient_cubic L R q hQ hLq hpR hRq
  let H := selectedGroup R M
  let Y := (pResidual 2 H).map H.subtype
  have hYq : Y.map q=zpowers cubic := by
    let π := QuotientGroup.mk' (pCore 2 G)
    let qb := QuotientGroup.lift (pCore 2 G) q hQ
    have heq : qb.comp π=q := by ext x;rfl
    rw [←heq,←map_map,selected_residual_image R hpR M hM hn]
    exact hMc
  have hcH : cubic ∈ H.map q := (map_mono (map_subtype_le _))
    (by rw [hYq];exact mem_zpowers cubic)
  obtain ⟨P0,hP0,hi⟩ := selected_sylow_of_twoGroup R hpR hQR M hM hn
  have hmove := selected_omega_movement_of_embedding R U hUR M q hRq.le hrJ hcH f hfU he
  rw [←hP0] at hmove
  have hB : (ChapterB.baumann (P0 : Subgroup H)).map H.subtype=S := by
    rw [hP0,selected_baumann_map,hBaum]
  have hgenerate := selected_normalizer_generate L R (T : Subgroup G) q hq hQ hLq
    T.isPGroup' hgen P hP hpR hQR hRker hRq M hM hn hMc
  rw [hBaum] at hgenerate
  have hHgen : H ⊔ normalizer (S : Set G)=⊤ := by
    apply top_unique
    rw [←hgenerate]
    exact sup_le_sup (map_subtype_le _) le_rfl
  have hYL : Y ≤ L := (map_pResidual_le 2 H.subtype).trans_eq hres
  have hne := cubic_not_central_in_component L Y hL.subnormal hYL q hQ hLq hYq
  exact cubic_seed_block_alternative (T : Subgroup G) L H T.isPGroup' hf
    (core_le_selectedGroup R M) P0 hB hi hmove hHgen hYL hL.subnormal hpL hfL hne
end CFSG.Quasithin.ChapterC.RankOne.SevenSource.Natural
