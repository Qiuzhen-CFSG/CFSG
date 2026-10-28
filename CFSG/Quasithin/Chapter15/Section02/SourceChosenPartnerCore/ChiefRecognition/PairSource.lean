module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ChiefRecognition.LinearSource
public import Theory.GroupTheory.CComponent.SimplePairQuotient
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ChiefRecognition.NormalizerClifford

/-!
# The actual component-normalizer action on the partner chief section

The surviving structural row supplies the original C-component C and
exchanger t. Their images modulo O₂(KcT) are distinct simple components,
so the first component normalizer has index two and still excludes t.
The Sylow-central marked involution normalizes this component. Clifford
restriction therefore gives an irreducible normalizer action or two actual
exchanged constituents with rank-one displacement and a G.6.4 faithful-image
model.

The final theorem applies this reduction to the saturated source chief
section. It retains C, t, the literal join and set product, both original
PSL₂ parameter alternatives, the original quotient map and the same nonzero
H-fixed image of the source plane. This is a reduction, not the final paired
natural recognition: excluding the irreducible restriction and identifying
the factor actions and full wreath action remain with the critical-pair
assembly. Earlier residual and plane premises retain their original source
producers and their discharge in qt-e-152-chosen-action-contradiction.

Source: Aschbacher–Smith 15.2.12(2)(iii) and 15.2.27(2), printed p.1119;
G.6.4, printed pp.345–346; Clifford theory, Isaacs, Theorem 6.5.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChosenGeometry
open NoncentralChiefRefinement PartnerChiefRecognition
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem psl2_simple_even {X : Type*} [Group X] [Group.IsPerfect X]
    {q : ℕ} (hm : ClassicalGroup.IsPSL X 2 q) :
    IsSimpleGroup X ∧ 2 ∣ Nat.card X := by
  obtain ⟨F,_,_,_,⟨e⟩⟩ := hm
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    MulAction.IwasawaStructure.isSimpleGroup Group.IsPerfect.commutator_eq_top
      PSL2.Iwasawa inferInstance
  refine ⟨e.isSimpleGroup,?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact Theory.PSL2.two_dvd_card

/-- The literal component normalizer in the source chief quotient has index
two; the original t still exchanges the two simple components. -/
theorem source_chosen_pair_normalizer_data
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (hg : ChosenPlaneGeometry h H ZS)
    (C : Subgroup G) (t : G) (hC : C ∈ Chapter1.cComponentsIn Mc)
    (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (C : Set G))
    (he : partnerSpan H Mc = C ⊔ C.conjBy t)
    (hm : (∃ n : ℕ, Even n ∧ ClassicalGroup.IsPSL (Chapter1.XiQuotient C) 2 (2 ^ n)) ∨
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (Chapter1.XiQuotient C) 2 p) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 L)
    let tL : L := ⟨t,(show (T : Subgroup G) ≤ L from le_sup_right) ht⟩
    let A := (C.subgroupOf L).map q
    IsComponent (L ⧸ pCore 2 L) A ∧ IsSimpleGroup A ∧ 2 ∣ Nat.card A ∧
      (normalizer (A : Set (L ⧸ pCore 2 L))).index = 2 ∧
      q tL ∉ normalizer (A : Set (L ⧸ pCore 2 L)) := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 L)
  let tL : L := ⟨t,(show (T : Subgroup G) ≤ L from le_sup_right) ht⟩
  have hTM := hg.outside.1.1.2.trans hg.in_partner
  have hKM : partnerSpan H Mc ≤ Mc :=
    conjugateSpanBy_le_self ((map_subtype_le _).trans hg.in_partner)
  have hLM : L ≤ Mc := sup_le hKM hTM
  have hCL : C ≤ L := (show C ≤ partnerSpan H Mc from he ▸ le_sup_left).trans le_sup_left
  have hDL : C.conjBy t ≤ L :=
    (show C.conjBy t ≤ partnerSpan H Mc from he ▸ le_sup_right).trans le_sup_left
  have hconj : (C.conjBy t).subgroupOf L = (C.subgroupOf L).conjBy tL := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le hDL,map_conjBy_hom,map_subgroupOf_eq_of_le hCL]
    rfl
  have hpair : (partnerSpan H Mc).subgroupOf L =
      C.subgroupOf L ⊔ (C.subgroupOf L).conjBy tL := by
    rw [he,subgroupOf_sup hCL hDL,hconj]
  let : ((partnerSpan H Mc).subgroupOf L).Normal :=
    normal_subgroupOf_of_le_normalizer (hLM.trans (le_normalizer_conjugateSpanBy _ _))
  let : (C.subgroupOf L ⊔ (C.subgroupOf L).conjBy tL).Normal := hpair ▸ inferInstance
  have hCc : (C.subgroupOf L).IsCComponent := hC.2.subgroupOf_of_le hCL hLM
  have hdistinct : C.subgroupOf L ≠ (C.subgroupOf L).conjBy tL := by
    intro hh
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hm := congrArg (Subgroup.map L.subtype) hh
    rw [map_conjBy_hom,map_subgroupOf_eq_of_le hCL] at hm
    exact hm.symm
  let := hC.2.perfect
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hC.1).toMonoidHom) (subgroupOfEquivOfLe hC.1).surjective
  let : Group.IsPerfect (C ⧸ pCore 2 C) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hs : IsSimpleGroup (C ⧸ pCore 2 C) ∧ 2 ∣ Nat.card (C ⧸ pCore 2 C) := by
    rcases hm with ⟨_,_,hm⟩ | ⟨_,_,_,hm⟩ <;> exact psl2_simple_even hm
  let := hs.1
  let eC := subgroupOfEquivOfLe hCL
  let eQ := QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)
  let : IsSimpleGroup (C.subgroupOf L ⧸ pCore 2 (C.subgroupOf L)) := eQ.isSimpleGroup
  have hdiv : 2 ∣ Nat.card (C.subgroupOf L ⧸ pCore 2 (C.subgroupOf L)) := by
    rw [Nat.card_congr eQ.toEquiv]
    exact hs.2
  obtain ⟨hA,hsA,_,hdA,_,_,_,_,_,hi,htI,_⟩ :=
    simpleCore_pair_quotient_structure (C.subgroupOf L) hCc tL hdistinct hdiv
  exact ⟨hA,hsA,hdA,hi,htI⟩

/-- Apply the actual source component normalizer to the already constructed
rank-two chief action. The central involution and the exchanger are unchanged. -/
theorem source_chosen_pair_chief_dichotomy
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (C : Subgroup G) (t : G) (hC : C ∈ Chapter1.cComponentsIn Mc)
    (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (C : Set G))
    (he : partnerSpan H Mc = C ⊔ C.conjBy t)
    (hm : (∃ n : ℕ, Even n ∧ ClassicalGroup.IsPSL (Chapter1.XiQuotient C) 2 (2 ^ n)) ∨
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (Chapter1.XiQuotient C) 2 p)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 L)
    let tL : L := ⟨t,(show (T : Subgroup G) ≤ L from le_sup_right) ht⟩
    let A := (C.subgroupOf L).map q
    let I := normalizer (A : Set (L ⧸ pCore 2 L))
    ∀ (σ : Representation (ZMod 2) (L ⧸ pCore 2 L) W),
      PartnerChiefQuotientProperties T V L σ →
      ∀ a : L, (a : G) ∈ V → orderOf (q a) = 2 →
      (∀ s ∈ (T : Subgroup G).subgroupOf L, Commute (q a) (q s)) →
      Module.finrank (ZMod 2) (LinearMap.range (σ (q a) - 1)) = 2 →
      ∃ hi : I.index = 2, letI := normal_of_index_eq_two hi
        ∃ haI : q a ∈ I, IsIrreducible (σ.comp I.subtype) ∨
          Nonempty (ExchangedCentralConstituents σ I (q tL) ⟨q a,haI⟩) := by
  dsimp only
  intro σ hp a ha ho hc hr
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 L)
  let tL : L := ⟨t,(show (T : Subgroup G) ≤ L from le_sup_right) ht⟩
  let A := (C.subgroupOf L).map q
  let I := normalizer (A : Set (L ⧸ pCore 2 L))
  obtain ⟨hA,hsA,hdA,hi,htI⟩ := source_chosen_pair_normalizer_data hg C t hC ht htn he hm
  let : IsSimpleGroup A := hsA
  let : I.Normal := normal_of_index_eq_two hi
  obtain ⟨_,hirr,_,_,_,S,hS,hAS,_,_⟩ := hp
  let : IsIrreducible σ := hirr
  have hcomm : ∀ s ∈ S, Commute (q a) s := by
    intro s hs
    change s ∈ (S : Subgroup _) at hs
    rw [hS] at hs
    obtain ⟨b,hb,rfl⟩ := hs
    exact hc b hb
  have haI : q a ∈ I := mem_normalizer_of_central_sylow_simple_component
    A hA hdA S (q a) hcomm
  have htS : q tL ∈ S := by
    change q tL ∈ (S : Subgroup _)
    rw [hS]
    exact mem_map_of_mem q ht
  have haS : q a ∈ S := hAS (mem_map_of_mem q ha)
  have hsq : IsSQTK KnownSimple.IsKnownSimple (L ⧸ pCore 2 L) := by
    have hs := source_chosen_partner_join_sqtk h hg
    refine ⟨?_,hs.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 L) pCore_isPGroup).trans
      (hs.stronglyQuasithin p hp ho)
  exact ⟨hi,haI,central_rank_two_restriction σ hsq I hi (q tL) htI S htS
    ⟨q a,haI⟩ haS ((Subgroup.orderOf_coe (⟨q a,haI⟩ : I)).symm.trans ho) hcomm hr⟩
/-- The remaining source row, with its original conjugate components and
saturated chief section, satisfies the actual normalizer-action dichotomy.
The nonzero H-fixed vector is the one projected from the source plane. -/
theorem source_chosen_noncore_partner_normalizer_chief
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc) (hn : ¬ V ≤ twoCoreIn Mc)
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G)) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 L)
    ∃ (C : Subgroup G) (t : G) (ht : t ∈ (T : Subgroup G)),
      C ∈ Chapter1.LStar G (T : Subgroup G) ∧ C ∈ Chapter1.cComponentsIn Mc ∧
      t ∉ normalizer (C : Set G) ∧ partnerSpan H Mc = C ⊔ C.conjBy t ∧
      (partnerSpan H Mc : Set G) = (C : Set G) * (C.conjBy t : Set G) ∧
      ((∃ n : ℕ, Even n ∧ ClassicalGroup.IsPSL (Chapter1.XiQuotient C) 2 (2 ^ n)) ∨
        ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (Chapter1.XiQuotient C) 2 p) ∧
      ∃ (B U : NormalNode L) (hc : B ⋖ U)
        (hU : U.val.map L.subtype ≤ twoCoreIn Mc),
        centralInvolutions T ≤ B.val.map L.subtype ∧
        let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
          (map_le_iff_le_comap.mp hU)
        letI := chief_elementary B U hc hp
        ∃ σ : Representation (ZMod 2) (L ⧸ pCore 2 L) (Additive (Section B U)),
          σ.comp q = binarySectionRepresentation B U ∧
          PartnerChiefQuotientProperties T V L σ ∧
          ∃ a : L, (a : G) ∈ V ∧ orderOf (q a) = 2 ∧
            (∀ s ∈ (T : Subgroup G).subgroupOf L, Commute (q a) (q s)) ∧
            Module.finrank (ZMod 2) (LinearMap.range
              (σ (q a) - (1 : Module.End (ZMod 2) (Additive (Section B U))))) = 2 ∧
            ∃ w : Additive (Section B U), w ≠ 0 ∧
              (∀ g : L, (g : G) ∈ centralizer (ZS : Set G) → σ (q g) w = w) ∧
              (∀ g ∈ (H.subgroupOf L).map q, σ g w = w) ∧
              let tL : L := ⟨t,(show (T : Subgroup G) ≤ L from le_sup_right) ht⟩
              let I := normalizer (((C.subgroupOf L).map q : Subgroup (L ⧸ pCore 2 L)) : Set _)
              ∃ hi : I.index = 2, letI := normal_of_index_eq_two hi
                ∃ haI : q a ∈ I, IsIrreducible (σ.comp I.subtype) ∨
                  Nonempty (ExchangedCentralConstituents σ I (q tL) ⟨q a,haI⟩) := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  obtain ⟨C,t,hCL,hC,ht,htn,he,hset,hm⟩ :=
    source_chosen_noncore_partner_pair h hg hMc hZ hquotient hres hs hn hplane
  refine ⟨C,t,ht,hCL,hC,htn,he,hset,hm,?_⟩
  obtain ⟨B,U,hc,hU,hB,hσ⟩ :=
    source_chosen_partner_saturated_chief h hg hMc hZ hquotient hres hs hn
  refine ⟨B,U,hc,hU,hB,?_⟩
  have hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
    (map_le_iff_le_comap.mp hU)
  let := chief_elementary B U hc hp
  obtain ⟨σ,hσeq,hprop,⟨a,ha,ho,hacent,hr⟩,_,_,_,_,_,_,w,hw,hfix,hHfix⟩ := hσ
  exact ⟨σ,hσeq,hprop,a,ha,ho,hacent,hr,w,hw,hfix,hHfix,
    source_chosen_pair_chief_dichotomy h hg C t hC ht htn he hm σ hprop a ha ho hacent hr⟩

end CFSG.Quasithin.Chapter15.Section02
