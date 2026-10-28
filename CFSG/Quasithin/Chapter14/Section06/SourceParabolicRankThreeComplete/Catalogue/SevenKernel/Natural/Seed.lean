module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.NaturalSeed

/-!
# Cubic propagation for the relative natural seven-letter action

The prescribed two-subgroup need only contain the ambient two-core. We select
an invariant cubic above the literal permutation (016), retain the possible
odd central kernel, and use its index-three preimage to propagate a short
block. The permutation normalizer generation and the Thompson/Baumann image
conditions remain explicit; none assumes blockhood or a full A₇ core quotient.

Source: Aschbacher--Smith C.1.24(a), pp.130--131. This extends the proved
`SevenSource.NaturalSeed` argument from the Sylow case to the relative case.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel.Natural
open ChapterC ChapterC.RankOne.SevenSource ChapterC.RankOne.SevenSource.Natural
open ChapterC.RankOne.SymmetricSix
open Theory.SpecificGroups.SymmetricSeven.ThreePairsCubic
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry
open Theory.SpecificGroups.AlternatingSeven.CubicLift
variable {G : Type*} [Group G] [Finite G]

theorem exists_relative_quotient_cubic (L R : Subgroup G) [L.Normal]
    [IsQuasisimple (L ⧸ pCore 2 L)] (q : G →* Sym)
    (hQ : pCore 2 G ≤ q.ker) (hLq : L.map q = alternatingGroup (Fin 7))
    (hpR : IsPGroup 2 R) (hR : R.map q ≤ pairElementary) :
    ∃ M : Subgroup (G ⧸ pCore 2 G),
      M ≤ L.map (QuotientGroup.mk' (pCore 2 G)) ∧ Nat.card M=3 ∧
      R.map (QuotientGroup.mk' (pCore 2 G)) ≤ normalizer (M : Set (G ⧸ pCore 2 G)) ∧
      M.map (QuotientGroup.lift (pCore 2 G) q hQ)=zpowers cubic := by
  let π := QuotientGroup.mk' (pCore 2 G)
  let qb := QuotientGroup.lift (pCore 2 G) q hQ
  let B := L.map π
  let : B.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  let eB : (L ⧸ pCore 2 L) ≃* B := (inferInstance : L.Normal).isSubnormal.quotientCoreImageEquiv 2
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv eB
  have hBq : B.map qb=alternatingGroup (Fin 7) := by
    rw [map_map]
    exact hLq
  let f : B →* alternatingGroup (Fin 7) := (qb.comp B.subtype).codRestrict _
    (fun x => hBq ▸ mem_map_of_mem qb x.property)
  have hf : Function.Surjective f := by
    intro y
    have hy : (y:Sym)∈B.map qb := by rw [hBq]; exact y.property
    obtain ⟨x,hx,he⟩ := hy
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let := alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 7))
  let cover : Covering B (alternatingGroup (Fin 7)) := ⟨f,hf⟩
  have hk : f.ker=center B := cover.ker_eq_center_of_isSimple
  let e : B ⧸ center B ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he : ∀ x : B, qb x=(GLS3.Chapter5.alternatingQuotientHom e x : Sym) := by
    intro x
    rfl
  have ho : Odd (Nat.card (center B)) :=
    GLS3.Chapter5.OddCentralCovers.component_center_odd (pCore_quotient_pCore_eq_bot (G := G) 2)
      B ⟨(inferInstance : B.Normal).isSubnormal,inferInstance⟩
  have hRq : (R.map π).map qb ≤ pairElementary := by
    rw [map_map]
    exact hR
  exact exists_pair_cubic B e ho qb he (R.map π) (hpR.map π) hRq

theorem relative_selected_normalizer_generate (L R T : Subgroup G) [L.Normal]
    [IsQuasisimple (L ⧸ pCore 2 L)] (q : G →* Sym) (hq : Function.Surjective q)
    (hQ : pCore 2 G ≤ q.ker) (hLq : L.map q = alternatingGroup (Fin 7))
    (hT : IsPGroup 2 T) (hgen : L ⊔ T = ⊤)
    (P : Sylow 2 q.ker) (hP : (P : Subgroup q.ker).map q.ker.subtype = pCore 2 G)
    (hpR : IsPGroup 2 R) (hQR : pCore 2 G ≤ R) (hRker : R ⊓ q.ker = pCore 2 G)
    (hgenerate : normalizer (R.map q : Set Sym) ⊔ zpowers cubic = ⊤)
    (M : Subgroup (G ⧸ pCore 2 G)) (hM : Nat.card M = 3)
    (hn : R.map (QuotientGroup.mk' (pCore 2 G)) ≤ normalizer (M : Set (G ⧸ pCore 2 G)))
    (hMc : M.map (QuotientGroup.lift (pCore 2 G) q hQ) = zpowers cubic) :
    (pResidual 2 (selectedGroup R M)).map (selectedGroup R M).subtype ⊔
      normalizer (ChapterB.baumann R : Set G) = ⊤ := by
  let Y := (pResidual 2 (selectedGroup R M)).map (selectedGroup R M).subtype
  let K := Y ⊔ normalizer (ChapterB.baumann R : Set G)
  have hRN : normalizer (R : Set G) ≤ normalizer (ChapterB.baumann R : Set G) :=
    Stellmacher.normalizer_le_normalizer_baumann R
  have hQK : pCore 2 G ≤ K := hQR.trans (R.le_normalizer.trans (hRN.trans le_sup_right))
  have hN := normalizer_map_eq_of_kernel_intersection R hpR q hq P (hP.trans hRker.symm)
  let π := QuotientGroup.mk' (pCore 2 G)
  let qb := QuotientGroup.lift (pCore 2 G) q hQ
  have he : qb.comp π = q := by ext x; rfl
  have hYq : Y.map q = zpowers cubic := by
    rw [←he,←map_map]
    rw [selected_residual_image R hpR M hM hn]
    exact hMc
  have hKq : K.map q = ⊤ := by
    apply top_unique
    rw [←hgenerate]
    apply sup_le
    · rw [←hN]
      exact map_mono (hRN.trans le_sup_right)
    · rw [←hYq]
      exact map_mono le_sup_left
  exact eq_top_of_full_symmetric_image L T q hQ hLq hT hgen P hP K hQK hKq

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
theorem relative_marked_seed
    (L U : Subgroup G) [L.Normal] [U.Normal] [IsElementaryAbelian 2 U]
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hL : L.IsCComponent) (hf : generalizedFitting G=pCore 2 G)
    (hfL : generalizedFitting L=pCore 2 L)
    (R₀ : Subgroup G) (hpR₀ : IsPGroup 2 R₀)
    (hQR₀ : pCore 2 G ≤ R₀) (hgen : L ⊔ R₀ = ⊤)
    (q : G →* Sym) (hq : Function.Surjective q)
    (hLq : L.map q=alternatingGroup (Fin 7))
    (f : Multiplicative (BinaryPermutation.natural (Fin 7)) →* U)
    (hfU : Function.Injective f)
    (he : ∀ (g : G) (v : BinaryPermutation.natural (Fin 7)),
      f (Multiplicative.ofAdd (BinaryPermutation.naturalRepresentation (Fin 7) (q g) v)) =
        MulAut.conjNormal g (f (Multiplicative.ofAdd v)))
    (P : Sylow 2 q.ker) (hP : (P : Subgroup q.ker).map q.ker.subtype=pCore 2 G)
    (hcore : R₀ ⊓ q.ker=pCore 2 G)
    (hJ : swap01 ∈ (elementaryAbelianMaxJ R₀).map q)
    (hS : (ChapterB.baumann R₀).map q ≤ pairElementary)
    (hgenerate : normalizer ((ChapterB.baumann R₀).map q : Set Sym) ⊔
      zpowers cubic = ⊤) :
    (∃ C : Subgroup (ChapterB.baumann R₀), C.Characteristic ∧ C≠⊥ ∧
      (C.map (ChapterB.baumann R₀).subtype).Normal) ∨ IsBlock L := by
  let := hL.perfect
  have hpL : IsPPerfect 2 L := perfect_twoPerfect
  have hprod : ∀ g : G, ∃ l ∈ L, ∃ r ∈ R₀, l*r=g := by
    intro g
    exact mem_sup_of_normal_left.mp (hgen.ge (mem_top g))
  have hres : pResidual 2 G=L := pResidual_eq_of_subnormal_product L R₀
    hL.subnormal hpL hpR₀ hprod
  let : L.Normal := hres ▸ (inferInstance : (pResidual 2 G).Normal)
  let S := ChapterB.baumann R₀
  let R := pCore 2 G ⊔ S
  have hRT : R ≤ R₀ := sup_le hQR₀ inf_le_left
  have hpR : IsPGroup 2 R := hpR₀.to_le hRT
  have hQR : pCore 2 G ≤ R := le_sup_left
  have hQ : pCore 2 G ≤ q.ker := hcore.symm.le.trans inf_le_right
  have hRq : R.map q = S.map q := by
    rw [Subgroup.map_sup,(Subgroup.map_eq_bot_iff _).mpr hQ,bot_sup_eq]
  have hRpair : R.map q ≤ pairElementary := hRq.le.trans hS
  have hRker : R ⊓ q.ker=pCore 2 G := by
    apply le_antisymm
    · exact (inf_le_inf_right _ hRT).trans_eq hcore
    · exact le_inf hQR hQ
  have hBaum : ChapterB.baumann R=S :=
    (ChapterB.lemma_B_2_3_4 R₀ R le_sup_right hRT).symm
  have hJR : elementaryAbelianMaxJ R₀ ≤ R :=
    (ChapterB.elementaryAbelianMaxJ_le_baumann R₀).trans le_sup_right
  have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq R R₀ hRT
  have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le R₀ R hJR
  have horder := le_antisymm hsmall.1 hlarge.1
  have hJeq : elementaryAbelianMaxJ R=elementaryAbelianMaxJ R₀ :=
    le_antisymm (hsmall.2 horder) (hlarge.2 horder.symm)
  have hrJ : swap01 ∈ (elementaryAbelianMaxJ R).map q := by
    rwa [hJeq]
  have hUR : U ≤ R := (show U ≤ pCore 2 G from
    le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩).trans hQR
  obtain ⟨M,hML,hM,hn,hMc⟩ := exists_relative_quotient_cubic L R q hQ hLq hpR hRpair
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
  have hmove := selected_omega_movement_of_embedding R U hUR M q hRpair hrJ hcH f hfU he
  rw [←hP0] at hmove
  have hB : (ChapterB.baumann (P0 : Subgroup H)).map H.subtype=S := by
    rw [hP0,selected_baumann_map,hBaum]
  have hgenerate := relative_selected_normalizer_generate L R R₀ q hq hQ hLq
    hpR₀ hgen P hP hpR hQR hRker (hRq ▸ hgenerate) M hM hn hMc
  rw [hBaum] at hgenerate
  have hHgen : H ⊔ normalizer (S : Set G)=⊤ := by
    apply top_unique
    rw [←hgenerate]
    exact sup_le_sup (map_subtype_le _) le_rfl
  have hYL : Y ≤ L := (map_pResidual_le 2 H.subtype).trans_eq hres
  have hne := cubic_not_central_in_component L Y hL.subnormal hYL q hQ hLq hYq
  exact cubic_seed_block_alternative R₀ L H hpR₀ hf
    (core_le_selectedGroup R M) P0 hB hi hmove hHgen hYL hL.subnormal hpL hfL hne

end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel.Natural
