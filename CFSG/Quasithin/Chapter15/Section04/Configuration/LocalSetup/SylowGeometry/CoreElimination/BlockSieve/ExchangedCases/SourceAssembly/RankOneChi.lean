module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.CanonicalAction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.ControlSource
public import Theory.ElementaryAbelian.Injective
public import Theory.SpecificGroups.Alternating.ThreeRank

/-!
# The original rank-one B.5 row closes the exchanged source branch

The original row constructs the Sylow, marked Borel and minimal parabolic.
Its canonical Sylow-center module has the same faithful star action kernel,
and the checked inclusion comparison preserves its actual natural section.
The proved uniform characteristic-pair source then recognizes the original
perfect residual as a χ-block. Strong quasithin rank bounds and the original
swapped quotient marking leave only the allowed even rank-one or A₅ block.
The source seed excludes A₅, and the literal exchanged-block endgame gives
the contradiction.

This proves the complete rank-one B.5 branch without C.2.7 or C.1.34 as
inputs. The other B.5 rows remain separate obligations of the final source
sieve; this module does not assert the universal C.2.7 classification.
Source: Aschbacher–Smith C.2.7(3)(a)(i), pp.146–147; 15.4.20, p.1164.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
open SL3Geometry.SourceCases ChapterB.QuasisimpleSource
universe u

private theorem chi_of_canonical_conclusion
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (P : Sylow 2 A) (hmin : ChapterB.IsMinimalParabolicOver P ⊤)
    (W : Subgroup A) [W.Normal] [IsElementaryAbelian 2 W]
    (q : A →* B) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (W : Set A))
    (C : Subgroup (offenderSubgroup (NormalElementaryQuotient.representation W q hq hker)))
    [IsQuasisimple C]
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((NormalElementaryQuotient.representation W q hq hker).comp
        (offenderSubgroup (NormalElementaryQuotient.representation W q hq hker)).subtype) C)
    (F : BinaryField)
    (hnatural : IsLinearNatural (c.sectionData.action.comp C.subtype) F 2)
    (hspan : W = normalClosure (omegaOneCenterAmbient (P : Subgroup A) : Set A))
    (hfit : generalizedFitting A = pCore 2 A) (M : Subgroup A)
    (hcontrol : (P : Subgroup A).characteristicNormalizerClosure ≤ M) (hproper : M ≠ ⊤) :
    ChapterC.IsChiBlockIn (pResidual 2 A) := by
  let σ := NormalElementaryQuotient.representation W q hq hker
  let J := offenderSubgroup σ
  have hqs : IsQuasisimple (generalizedFitting J) := c.fitting_eq ▸ inferInstance
  obtain ⟨sF,hF⟩ : ∃ sF : MovedSection (σ.comp J.subtype) (generalizedFitting J),
      IsLinearNatural (sF.action.comp (generalizedFitting J).subtype) F 2 := by
    rw [←c.fitting_eq]
    exact ⟨c.sectionData,hnatural⟩
  exact (ChapterC.RankOne.ChiProduct.SelectedRankOne.quasisimple_linear_outside_of_control
    P hmin W q hq hker hqs sF F hF hspan hfit M hcontrol hproper).2.1

private theorem perfect_card_ne_three {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] [Nontrivial A] : Nat.card A ≠ 3 := by
  intro hc
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsCyclic A := isCyclic_of_prime_card hc
  exact Group.IsPerfect.not_isMulCommutative A inferInstance

variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K K₁ : Subgroup G} {r : G}

theorem source_selected_rankOne_chi
    (h : Input d i j H U K) (s : Selected H U K K₁ r)
    (hc : ComponentHypotheses KnownSimple.IsKnownSimple H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K₁.subgroupOf H))
    (c : StarSourceConclusion (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H))
    (hi : IsIrrPlus
      ((starRepresentation (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)).comp
        (offenderSubgroup (starRepresentation (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H))).subtype)
      ((starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)).subgroupOf
        (offenderSubgroup (starRepresentation (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H))))
      c.sectionData.space.toSubmodule)
    (F : BinaryField)
    (natural : ActionEquiv
      (c.sectionData.action.comp
        ((starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)).subgroupOf
          (offenderSubgroup (starRepresentation (K₁.subgroupOf H)
            ((sourceRadical d U).subgroupOf H)))).subtype) (linearNatural F 2))
    (hratio : quadraticRatio c.sectionData.action = 1)
    (hoff : ∀ B, IsBestOffender c.sectionData.action B →
      ∃ S : Sylow 2 ((starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)).subgroupOf
        (offenderSubgroup (starRepresentation (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)))),
        B = (S : Subgroup _).map
          ((starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)).subgroupOf
            (offenderSubgroup (starRepresentation (K₁.subgroupOf H)
              ((sourceRadical d U).subgroupOf H)))).subtype) : ChapterC.IsChiBlock K₁ := by
  let L := K₁.subgroupOf H
  let R := (sourceRadical d U).subgroupOf H
  let D := L ⊔ R
  have hr := source_local_radical h s hc.normalized
  let eq := SL3Geometry.source_componentStarEquiv h s hc.normalized hr
  let := hc.quasisimple
  let : IsQuasisimple (K₁ ⧸ pCore 2 K₁) :=
    IsQuasisimple.of_mulEquiv s.internalQuotientEquiv.symm
  let : IsSimpleGroup (K₁ ⧸ pCore 2 K₁) :=
    EmbeddingReduction.swapped_model_simple inferInstance s.model
  let : IsQuasisimple (starComponent L R) := IsQuasisimple.of_mulEquiv eq
  let : IsSimpleGroup (starComponent L R) := eq.symm.isSimpleGroup
  have hCJ := (source_selected_ff_classification h s hc).1
  let e := (subgroupOfEquivOfLe hCJ).symm.trans natural.groupEquiv
  obtain ⟨S,hS⟩ := source_rankOne_thompson_sylow h L hc hr hCJ c hratio hoff
  obtain ⟨P,hP,hmin,hWdata,hfit,hres⟩ :=
    source_selected_rankOne_canonicalModule h s hc F e S hS
  let W := normalClosure (omegaOneCenterAmbient (P : Subgroup D) : Set D)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (Subgroup.inclusion hWdata.1) (Subgroup.inclusion_injective hWdata.1)
  obtain ⟨hker,hCJ',cW,hnat⟩ :=
    source_canonical_natural_section h L hc hr P hP W rfl c hi F natural
  let σ := NormalElementaryQuotient.representation W (starProjection L R)
    (QuotientGroup.mk'_surjective _) hker
  let C := (starComponent L R).subgroupOf (offenderSubgroup σ)
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hCJ').symm
  have hcontrol : (P : Subgroup D).characteristicNormalizerClosure ≤
      (d.M₁.subgroupOf H).subgroupOf D := by
    rw [hP]
    exact characteristicNormalizerClosure_subgroupOf_le le_sup_right hc.characteristic_control
  have hproper : (d.M₁.subgroupOf H).subgroupOf D ≠ ⊤ := by
    intro he
    exact hc.outside (le_sup_left.trans (subgroupOf_eq_top.mp he))
  have hchi := chi_of_canonical_conclusion P hmin W (starProjection L R)
    (QuotientGroup.mk'_surjective _) hker C cW F hnat rfl hfit _ hcontrol hproper
  rw [hres] at hchi
  let eL : (L.subgroupOf D) ≃* K₁ :=
    (subgroupOfEquivOfLe (show L ≤ D from le_sup_left)).trans
      (subgroupOfEquivOfLe s.component.1)
  exact ChapterC.RankOne.ChiProduct.chi_of_equiv eL hchi.2

/-- The source quotient marking and strong quasithin rank bound reduce an
actual selected χ-block to precisely the two required exchanged types. -/
theorem selectedConclusion_of_chi
    (s : Selected H U K K₁ r) (κ : GroupClass.{u})
    (hc : ComponentHypotheses κ H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K₁.subgroupOf H))
    (hchi : ChapterC.IsChiBlock K₁) : SelectedConclusion H U K K₁ r := by
  refine ⟨s,s.relative_subnormal,?_⟩
  rcases hchi with ⟨n,hb⟩ | ⟨n,hodd,hb⟩
  · have hp := l2Block_parameter hb s.model
    exact Or.inl ⟨n,hp.1,hp.2,hb⟩
  · let := hc.quasisimple
    let : IsQuasisimple (K₁ ⧸ pCore 2 K₁) :=
      IsQuasisimple.of_mulEquiv s.internalQuotientEquiv.symm
    let : IsSimpleGroup (K₁ ⧸ pCore 2 K₁) :=
      EmbeddingReduction.swapped_model_simple inferInstance s.model
    obtain ⟨e⟩ := hb.2.2.quotient_iso
    have h3 := hb.1
    have h5 : 5 ≤ n := by
      by_contra hlo
      have hn : n = 3 := by rcases hodd with ⟨k,hk⟩; omega
      subst n
      apply perfect_card_ne_three (A := K₁ ⧸ pCore 2 K₁)
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      norm_num
    have hsK : IsSQTK κ K₁ :=
      (IsSQTK.equiv (subgroupOfEquivOfLe s.component.1)).mp (hc.sqtk.subgroup _)
    have hq : primeRank 3 (K₁ ⧸ pCore 2 K₁) ≤ 2 :=
      (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans
        (hsK.stronglyQuasithin 3 (by decide) (by decide))
    have h8 : n ≤ 8 := by
      by_contra hn
      have hlow := alternatingGroup.ThreeRank.three_le_primeRank (by omega : 9 ≤ n)
      rw [← primeRank_equiv 3 e] at hlow
      omega
    obtain rfl := alternatingBlock_degree h5 h8 hb s.model
    exact Or.inr hb

/-- A constructed χ-block on the actual selected factor closes the original
contrary endgame, without either universal C.2.7 or C.1.34. -/
theorem chi_sieve_contradiction
    {κ : GroupClass.{u}} (c₀ : BlockEndgame.ContraryData κ d i j)
    (h : Input d i j c₀.H c₀.U c₀.K) (s : Selected c₀.H c₀.U c₀.K K₁ r)
    (hc : ComponentHypotheses κ c₀.H ((sourceRadical d c₀.U).subgroupOf c₀.H)
      (d.M₁.subgroupOf c₀.H) (K₁.subgroupOf c₀.H))
    (hchi : ChapterC.IsChiBlock K₁) : False := by
  have hb : ∃ n, Even n ∧ Nat.ModEq 3 (2 ^ n) 1 ∧ ChapterC.IsL2EvenBlock K₁ n := by
    rcases (selectedConclusion_of_chi s κ hc hchi).2.2 with hb | hb
    · exact hb
    · exact (h.not_alternatingFive_block K₁ s.component.1 s.relative_subnormal hb).elim
  obtain ⟨n,hn,hm,hmodel⟩ := hb
  let b : BlockEndgame.ExchangedBlock c₀ := {
    first := K₁
    first_le := s.component.1
    relative_block := ⟨inferInstance, ChapterC.RankOne.Solvable.isShort_of_equiv
      (subgroupOfEquivOfLe s.component.1).symm hmodel.2.1, s.relative_subnormal⟩
    quotient_quasisimple := by
      let := hc.quasisimple
      exact IsQuasisimple.of_mulEquiv s.internalQuotientEquiv.symm
    n := n
    even_parameter := hn
    model := hmodel
    exchanger := r
    exchanger_mem := s.conjugator_mem
    exchanger_moves := s.conjugator_moves
    product := s.join_eq
    product_set := s.product_eq.symm
    core_normalizes := by
      have hRH : sourceRadical d c₀.U ≤ c₀.H :=
        h.radical_le_sylow.trans (h.placed.sylow_image ▸ map_subtype_le _)
      have he := hc.normalized
      rw [← subgroupOf_normalizer_eq s.component.1] at he
      exact fun x hx => he (show (⟨x,hRH hx⟩ : c₀.H) ∈
        (sourceRadical d c₀.U).subgroupOf c₀.H from hx) }
  exact BlockEndgame.source_contradiction c₀ b

/-- The complete original rank-one B.5 row now reaches the source contradiction. -/
theorem source_rankOne_row_contradiction
    (c₀ : BlockEndgame.ContraryData KnownSimple.IsKnownSimple d i j)
    (h : Input d i j c₀.H c₀.U c₀.K) (s : Selected c₀.H c₀.U c₀.K K₁ r)
    (hc : ComponentHypotheses KnownSimple.IsKnownSimple c₀.H ((sourceRadical d c₀.U).subgroupOf c₀.H)
      (d.M₁.subgroupOf c₀.H) (K₁.subgroupOf c₀.H))
    (c : StarSourceConclusion (K₁.subgroupOf c₀.H) ((sourceRadical d c₀.U).subgroupOf c₀.H))
    (hi : IsIrrPlus
      ((starRepresentation (K₁.subgroupOf c₀.H) ((sourceRadical d c₀.U).subgroupOf c₀.H)).comp
        (offenderSubgroup (starRepresentation (K₁.subgroupOf c₀.H) ((sourceRadical d c₀.U).subgroupOf c₀.H))).subtype)
      ((starComponent (K₁.subgroupOf c₀.H) ((sourceRadical d c₀.U).subgroupOf c₀.H)).subgroupOf
        (offenderSubgroup (starRepresentation (K₁.subgroupOf c₀.H) ((sourceRadical d c₀.U).subgroupOf c₀.H))))
      c.sectionData.space.toSubmodule)
    (F : BinaryField)
    (natural : ActionEquiv
      (c.sectionData.action.comp
        ((starComponent (K₁.subgroupOf c₀.H) ((sourceRadical d c₀.U).subgroupOf c₀.H)).subgroupOf
          (offenderSubgroup (starRepresentation (K₁.subgroupOf c₀.H)
            ((sourceRadical d c₀.U).subgroupOf c₀.H)))).subtype) (linearNatural F 2))
    (hratio : quadraticRatio c.sectionData.action = 1)
    (hoff : ∀ B, IsBestOffender c.sectionData.action B →
      ∃ S : Sylow 2 ((starComponent (K₁.subgroupOf c₀.H) ((sourceRadical d c₀.U).subgroupOf c₀.H)).subgroupOf
        (offenderSubgroup (starRepresentation (K₁.subgroupOf c₀.H) ((sourceRadical d c₀.U).subgroupOf c₀.H)))),
        B = (S : Subgroup _).map
          ((starComponent (K₁.subgroupOf c₀.H) ((sourceRadical d c₀.U).subgroupOf c₀.H)).subgroupOf
            (offenderSubgroup (starRepresentation (K₁.subgroupOf c₀.H)
              ((sourceRadical d c₀.U).subgroupOf c₀.H)))).subtype) : False :=
  chi_sieve_contradiction c₀ h s hc
    (source_selected_rankOne_chi h s hc c hi F natural hratio hoff)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
