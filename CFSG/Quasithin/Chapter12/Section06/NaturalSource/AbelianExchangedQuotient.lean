module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianExchangedSections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.Sections
public import Theory.GroupTheory.ConjugatePairInternalLift
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# Faithful maximal quotients of the original exchanged actor

The actual component images form a conjugation-invariant pair in H/O₂(H).
A maximal proper submodule of the literal U_H/V₁ has a faithful irreducible
quotient, still moved by the component orbit. The original quadratic actor
retains its cubic bound on this quotient. The F.9 dichotomy also retains a
nonzero image of the perpendicular and an FF or component-central kernel.

All earlier source geometry remains explicit. This is the quotient used by
the tensor recognition and the two-layer filtration in 12.6.33, not yet the
exclusion of the exchanged branch.
Source: Aschbacher--Smith 12.6.33, printed pp.837--838; F.9.18, pp.325--326.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter13.Section08.Components Chapter13.Section08.Components.Swapped
open Chapter13.Section08.Components.Swapped.LinearTwo
open ModuleAlternatives ModuleAlternatives.F918Sections ModuleAlternatives.F918Sections.NoStrong
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)


include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The original two component images form a conjugation-invariant pair. -/
theorem SourceHypothesis.original_abelian_exchanged_pair_conjugates
    (hn : ¬ (K.subgroupOf H).Normal)
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (K : Set G)) :
    (∀ g : H ⧸ pCore 2 H,
      (actorImage H K).conjBy g = actorImage H K ∨
      (actorImage H K).conjBy g = actorImage H (K.conjBy t)) ∧
    (∀ g : H ⧸ pCore 2 H,
      (actorImage H (K.conjBy t)).conjBy g = actorImage H K ∨
      (actorImage H (K.conjBy t)).conjBy g = actorImage H (K.conjBy t)) := by
  have hi : (normalizer (K.subgroupOf H : Set H)).index = 2 := by
    let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
    exact (cComponent_normalizer_index_quotient hK (pCore 2 H)).symm.trans
      (S.original_abelian_nonnormal_component_models D hZ z hz hTV hTz hbound hTI hns
        hH hKH hK hgen hn).1
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  let tH : H := ⟨t,hTH ht⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  have hm : (K.subgroupOf H).conjBy tH ≠ K.subgroupOf H := by
    intro he
    have he' := congrArg (Subgroup.map H.subtype) he
    rw [map_conjBy_hom,map_subgroupOf_eq_of_le hKH] at he'
    exact htn (mem_normalizer_iff_map_conj_eq.mpr he')
  have htstar : (actorImage H K).conjBy (q tH) = actorImage H (K.conjBy t) :=
    starImage_conjBy H K hKH (hTH ht)
  have hfirst (g : H ⧸ pCore 2 H) :
      (actorImage H K).conjBy g = actorImage H K ∨
      (actorImage H K).conjBy g = actorImage H (K.conjBy t) := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) g
    rcases NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi hm x with he | he
    · left
      exact (map_conjBy_hom q (K.subgroupOf H) x).symm.trans
        (congrArg (Subgroup.map q) he)
    · right
      exact ((map_conjBy_hom q (K.subgroupOf H) x).symm.trans
        (congrArg (Subgroup.map q) he)).trans
        ((map_conjBy_hom q (K.subgroupOf H) tH).trans htstar)
  refine ⟨hfirst,fun g => ?_⟩
  have he : (actorImage H (K.conjBy t)).conjBy g =
      (actorImage H K).conjBy (g * q tH) := by
    rw [conjBy_mul,htstar]
  rw [he]
  exact hfirst _

variable [IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H)]
  (a : LocalQuotientAction H ((D.fullSetup hZ T z).UH H) (D.fullSetup hZ T z).V₁)

local instance quotient_source_span_elementary (E : Nonabelian.Setup G) (J : Subgroup G)
    [IsElementaryAbelian 2 (E.UH J)] :
    IsElementaryAbelian 2 (Chapter13.Section08.Source.UH J E.V₅) :=
  inferInstanceAs (IsElementaryAbelian 2 (E.UH J))
local instance quotient_source_span_normal (E : Nonabelian.Setup G) (J : Subgroup G)
    [IsElementaryAbelian 2 (E.UH J)] :
    (E.V₁.subgroupOf (Chapter13.Section08.Source.UH J E.V₅)).Normal :=
  inferInstanceAs ((E.V₁.subgroupOf (E.UH J)).Normal)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- A maximal literal quotient is faithful and irreducible and retains the
original quadratic actor's cubic bound. Its kernel is FF or component-central. -/
theorem SourceHypothesis.original_abelian_exchanged_faithful_quotient
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    ∃ W : Subrepresentation a.representation, W ≠ ⊤ ∧
      W.quotientRepresentation.IsIrreducible ∧
      Function.Injective W.quotientRepresentation ∧
      cubicRatio W.quotientRepresentation ≤ 2 ∧
      (sourceSeedSpace H (D.fullSetup hZ T z).V₅ (D.fullSetup hZ T z).V₁).map
        W.toSubmodule.mkQ ≠ ⊥ ∧
      ((IsFFModule (imageRepresentation W.toRepresentation) ∧
        IsFFModule (imageRepresentation W.quotientRepresentation)) ∨
       W.toSubmodule ≤ fixedSpace a.representation
          (actorImage H (conjugateSpanBy K (T : Subgroup G)))) := by
  obtain ⟨W,hW,hmax,hseed,halt⟩ := S.original_abelian_exchanged_section_dichotomy
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen a hn hm
  let : W.quotientRepresentation.IsIrreducible :=
    FFFactors.maximal_avoiding_irreducible a.representation W hW hmax
  let : Nontrivial ((Additive ((D.fullSetup hZ T z).UH H ⧸
      (D.fullSetup hZ T z).V₁.subgroupOf ((D.fullSetup hZ T z).UH H))) ⧸ W.toSubmodule) :=
    Subrepresentation.irreducible_module_nontrivial W.quotientRepresentation
  obtain ⟨t,ht,hTH,htn,F,hF,hfin,hchar,b,_,_,ho,_,_⟩ :=
    S.original_abelian_exchanged_actor D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen hn hm
  have hfull := S.original_abelian_exchanged_movement
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen a hn hm
  have hqfull : subspaceCommutator W.quotientRepresentation ⊤ b.orbit = ⊤ := by
    rw [ho]
    exact FFFactors.quotient_full_commutator a.representation W _ hfull
  have hfaith : Function.Injective W.quotientRepresentation :=
    b.faithful_of_noncentral W.quotientRepresentation (by
      intro hh
      have hz : subspaceCommutator W.quotientRepresentation ⊤ b.orbit = ⊥ :=
        (subspaceCommutator_eq_bot_iff _ _ _).mpr (fun v _ g => hh g g.property v)
      exact (top_ne_bot : (⊤ : Submodule (ZMod 2) _) ≠ ⊥) (hqfull.symm.trans hz))
  obtain ⟨_,hU,c,B,hB,hBT,hEA,hquad,hcod,_,_⟩ :=
    S.original_abelian_component_span_actors D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen
  have heq := a.representation_eq c
  rw [←heq] at hquad hcod
  have hq := quadratic_of_equivariant_surjection a.representation W.quotientRepresentation
    W.toSubmodule.mkQ W.toSubmodule.mkQ_surjective
    (fun g v => (W.quotientRepresentation_mk g v).symm) _ hquad
  have hb : fixedCodim W.quotientRepresentation (B.map (QuotientGroup.mk' (pCore 2 H))) ≤
      2 * rank (B.map (QuotientGroup.mk' (pCore 2 H))) :=
    (Nat.le_add_right _ _).trans
      ((fixedCodim_quotient_add_subrepresentation_le a.representation W _).trans hcod)
  refine ⟨W,hW,inferInstance,hfaith,
    (cubicRatio_le_nat_iff _ 2).mpr ⟨_,hEA,isCubic_of_isQuadratic hq,hb⟩,hseed,?_⟩
  rcases halt with hff | ⟨hc,_⟩
  · exact Or.inl hff
  · exact Or.inr ((subspaceCommutator_eq_bot_iff _ _ _).mp hc)

end CFSG.Quasithin.Chapter12.Section06
