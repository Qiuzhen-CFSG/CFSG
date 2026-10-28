module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ChiefRecognition.PairSource
public import CFSG.Quasithin.ChapterG.Section06.CentralPairConstituents
public import Theory.GroupTheory.GeneralizedFitting.ComponentPrimeRankNormal

/-!
# Natural constituents of the actual partner component pair

A simple component in the surviving conjugate pair has three-rank at most
one: a larger rank would force it to be normal, contrary to the original
exchanger. Apply this bound to the faithful images of the exchanged Clifford
constituent. The central rank-one classification then leaves only its marked
binary natural three-space. Exactly one literal component image is the full
actor and the other is trivial. The two exchanged constituents give chief
dimension six.

The final theorem applies this recognition to the saturated chief section
already constructed from the source. It retains C, the actual t outside its
normalizer, the literal join and set product, both original PSL₂ alternatives,
the original quotient map, and the same nonzero H-fixed source-plane vector.
The irreducible normalizer alternative remains explicit. Its exclusion and
reconstruction of the full paired action, partner-core placement and final
critical-pair assembly remain with qt-e-152-critical-pair. Earlier source
premises retain their existing producers and final discharge in
qt-e-152-chosen-action-contradiction.

Source: Aschbacher–Smith 15.2.12(2)(iii) and 15.2.27(2), printed p.1119;
G.6.4, printed pp.345–346; component calculus in A.3.3.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section02.PartnerChiefRecognition
universe v
variable {G W : Type v} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

/-- The marked natural constituent and the literal full/trivial component images. -/
@[expose] def ExchangedCentralConstituents.NaturalFactors
    {ρ : Representation (ZMod 2) G W} {I : Subgroup G} [I.Normal] {t : G} {a : I}
    (E : ExchangedCentralConstituents ρ I t a) (A B : Subgroup G) : Prop :=
  ChapterG.Section06.HasModelOn
    (BinaryOffender.imageRepresentation E.constituent.toRepresentation)
    ⊤ ⊤ (ChapterG.Section06.binaryLinearAction 3) ∧
  (((A.subgroupOf I).map (BinaryOffender.actionHom E.constituent.toRepresentation) = ⊤ ∧
    (B.subgroupOf I).map (BinaryOffender.actionHom E.constituent.toRepresentation) = ⊥) ∨
   ((A.subgroupOf I).map (BinaryOffender.actionHom E.constituent.toRepresentation) = ⊥ ∧
    (B.subgroupOf I).map (BinaryOffender.actionHom E.constituent.toRepresentation) = ⊤))
end CFSG.Quasithin.Chapter15.Section02.PartnerChiefRecognition

namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChosenGeometry
open NoncentralChiefRefinement PartnerChiefRecognition
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual conjugate-component row forces the exchanged constituent to be natural of degree three. -/
theorem source_chosen_exchanged_constituent_natural_three
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
    let B := A.conjBy (q tL)
    let I := normalizer (A : Set (L ⧸ pCore 2 L))
    ∀ (σ : Representation (ZMod 2) (L ⧸ pCore 2 L) W),
      PartnerChiefQuotientProperties T V L σ →
      ∀ hi : I.index = 2, letI := normal_of_index_eq_two hi
        ∀ (a : I) (E : ExchangedCentralConstituents σ I (q tL) a),
        E.NaturalFactors A B := by
  dsimp only
  intro σ hp hi a E
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 L)
  let tL : L := ⟨t,(show (T : Subgroup G) ≤ L from le_sup_right) ht⟩
  let A := (C.subgroupOf L).map q
  let B := A.conjBy (q tL)
  let I := normalizer (A : Set (L ⧸ pCore 2 L))
  let : I.Normal := normal_of_index_eq_two hi
  obtain ⟨hA,hsA,_,_,htI⟩ := source_chosen_pair_normalizer_data hg C t hC ht htn he hm
  change IsComponent (L ⧸ pCore 2 L) A at hA
  change q tL ∉ I at htI
  let : IsSimpleGroup A := hsA
  let : IsSimpleGroup B := ((MulAut.conj (q tL)).subgroupMap A).symm.isSimpleGroup
  have hB : IsComponent (L ⧸ pCore 2 L) B := hA.map_conj (q tL)
  have hne : A ≠ B := fun hh => htI (mem_normalizer_iff_map_conj_eq.mpr hh.symm)
  have hAI : A ≤ I := A.le_normalizer
  have hBI : B ≤ I := (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (hA.commutator_eq_bot_of_ne hB hne))).trans
      (_root_.centralizer_le_normalizer A)
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
  let : (A ⊔ B).Normal := by
    change ((C.subgroupOf L).map q ⊔ ((C.subgroupOf L).map q).conjBy (q tL)).Normal
    rw [←map_conjBy_hom,←Subgroup.map_sup,←hpair]
    exact Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hrG : primeRank 3 (L ⧸ pCore 2 L) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 L) pCore_isPGroup).trans
      ((source_chosen_partner_join_sqtk h hg).stronglyQuasithin 3 (by decide) (by decide))
  have hrA : primeRank 3 A ≤ 1 := by
    by_contra hn
    let := hA.2
    have hz : center A = ⊥ :=
      (inferInstance : (center A).Normal).eq_bot_or_eq_top.resolve_right
        (fun hh => Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp hh))
    let : A.Normal := hA.normal_of_centerless_of_primeRank hz 3 (by omega)
    exact htI (by
      change q tL ∈ normalizer (A : Set _)
      rw [normalizer_eq_top]
      exact mem_top _)
  have hrB : primeRank 3 B ≤ 1 := by
    have hh : primeRank 3 A = primeRank 3 B := primeRank_equiv 3
      (A.equivMapOfInjective (MulAut.conj (q tL)).toMonoidHom (MulAut.conj (q tL)).injective)
    exact hh ▸ hrA
  let : IsIrreducible σ := hp.2.1
  let : IsIrreducible E.constituent.toRepresentation := E.irreducible
  exact ChapterG.Section06.normal_pair_constituent_natural_three σ hp.1 I E.constituent
    A B hA hB hne hAI hBI hrA hrB E.model
end CFSG.Quasithin.Chapter15.Section02

namespace CFSG.Quasithin.Chapter15.Section02.PartnerChiefRecognition
open Representation.BinaryOffender
universe v
variable {G W : Type v} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- Two exchanged natural three-spaces give chief dimension six. -/
theorem ExchangedCentralConstituents.finrank_six
    {ρ : Representation (ZMod 2) G W} {I : Subgroup G} [I.Normal] {t : G} {a : I}
    (E : ExchangedCentralConstituents ρ I t a)
    (hm : ChapterG.Section06.HasModelOn (imageRepresentation E.constituent.toRepresentation)
      ⊤ ⊤ (ChapterG.Section06.binaryLinearAction 3)) :
    Module.finrank (ZMod 2) E.constituent.toSubmodule = 3 ∧ Module.finrank (ZMod 2) W = 6 := by
  obtain ⟨_,f,_,_⟩ := hm
  let e := (Submodule.topEquiv (R := ZMod 2) (M := E.constituent.toSubmodule)).symm.trans f
  have hd : Module.finrank (ZMod 2) E.constituent.toSubmodule = 3 := by
    simpa only [Module.finrank_pi,Fintype.card_fin] using e.finrank_eq
  refine ⟨hd,?_⟩
  have hh := E.coordinates.toLinearEquiv.finrank_eq
  rw [Module.finrank_prod,hd] at hh
  exact hh
end CFSG.Quasithin.Chapter15.Section02.PartnerChiefRecognition

namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChosenGeometry
open NoncentralChiefRefinement PartnerChiefRecognition
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Refine the original normalizer dichotomy with natural coordinates and the literal component images. -/
theorem source_chosen_pair_chief_natural_dichotomy
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
    let B := A.conjBy (q tL)
    let I := normalizer (A : Set (L ⧸ pCore 2 L))
    ∀ (σ : Representation (ZMod 2) (L ⧸ pCore 2 L) W),
      PartnerChiefQuotientProperties T V L σ →
      ∀ a : L, (a : G) ∈ V → orderOf (q a) = 2 →
      (∀ s ∈ (T : Subgroup G).subgroupOf L, Commute (q a) (q s)) →
      Module.finrank (ZMod 2) (LinearMap.range (σ (q a) - 1)) = 2 →
      ∃ hi : I.index = 2, letI := normal_of_index_eq_two hi
        ∃ haI : q a ∈ I, IsIrreducible (σ.comp I.subtype) ∨
          ∃ E : ExchangedCentralConstituents σ I (q tL) ⟨q a,haI⟩,
            Module.finrank (ZMod 2) E.constituent.toSubmodule = 3 ∧ Module.finrank (ZMod 2) W = 6 ∧
            E.NaturalFactors A B := by
  dsimp only
  intro σ hp a ha ho hc hr
  obtain ⟨hi,haI,hh⟩ := source_chosen_pair_chief_dichotomy h hg C t hC ht htn he hm
    σ hp a ha ho hc hr
  let := normal_of_index_eq_two hi
  refine ⟨hi,haI,?_⟩
  rcases hh with hirr | hred
  · exact Or.inl hirr
  · let E := Classical.choice hred
    have hnat := source_chosen_exchanged_constituent_natural_three
      h hg C t hC ht htn he hm σ hp hi ⟨_,haI⟩ E
    obtain ⟨hdC,hdW⟩ := E.finrank_six hnat.1
    exact Or.inr ⟨E,hdC,hdW,hnat⟩
end CFSG.Quasithin.Chapter15.Section02

namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChosenGeometry
open NoncentralChiefRefinement PartnerChiefRecognition
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Apply the constituent recognition to the saturated source chief section, retaining its H-fixed vector. -/
theorem source_chosen_noncore_partner_natural_chief
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
                  ∃ E : ExchangedCentralConstituents σ I (q tL) ⟨q a,haI⟩,
                    Module.finrank (ZMod 2) E.constituent.toSubmodule = 3 ∧
                    Module.finrank (ZMod 2) (Additive (Section B U)) = 6 ∧
                    E.NaturalFactors ((C.subgroupOf L).map q)
                      (((C.subgroupOf L).map q).conjBy (q tL)) := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  obtain ⟨C,t,ht,hCL,hC,htn,he,hset,hm,B,U,hc,hU,hB,hσ⟩ :=
    source_chosen_noncore_partner_normalizer_chief h hg hMc hZ hquotient hres hs hn hplane
  refine ⟨C,t,ht,hCL,hC,htn,he,hset,hm,B,U,hc,hU,hB,?_⟩
  have hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
    (map_le_iff_le_comap.mp hU)
  let := chief_elementary B U hc hp
  obtain ⟨σ,hσeq,hprop,a,ha,ho,hacent,hr,w,hw,hfix,hHfix,_⟩ := hσ
  exact ⟨σ,hσeq,hprop,a,ha,ho,hacent,hr,w,hw,hfix,hHfix,
    source_chosen_pair_chief_natural_dichotomy h hg C t hC ht htn he hm σ hprop a ha ho hacent hr⟩
end CFSG.Quasithin.Chapter15.Section02
