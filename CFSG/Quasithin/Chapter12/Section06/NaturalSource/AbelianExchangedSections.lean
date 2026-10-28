module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianExchangedActor
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSections
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ResidualPairAction
public import Theory.Representation.BinaryOffender.Homogeneous.Existence

/-!
# Marked sections for the original exchanged field-four actor

The original point residual moves the entire perpendicular quotient. Its
component orbit therefore moves all of the literal U_H/V₁. The constructed
exchanged actor excludes strong FF modules on the faithful images of both
sections, and the original quadratic actor supplies the F.9.18 dichotomy.
In the central branch, the selected Irr⁺ seed is homogeneous under the
original T image and both its Sylow and ambient orbit spans are the whole
module. The image of the actual perpendicular remains nonzero in the
maximal quotient.

The earlier geometry hypotheses are retained. The tensor/non-tensor model
recognition and final 12.6.33 exclusion still require their source assembly.
Source: Aschbacher--Smith 12.6.33, printed pp.837--838; F.9.18(5--6),
printed pp.325--326; A.1.42, printed p.32.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
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

include hz hTV hTz hbound hH in
/-- The original point residual generates the entire perpendicular section
by commutators; no module classification is used. -/
theorem SourceHypothesis.original_perpendicular_residual_movement :
    (D.fullSetup hZ T z).V₅ =
      ⁅(D.fullSetup hZ T z).L₁,(D.fullSetup hZ T z).V₅⁆ ⊔ (D.fullSetup hZ T z).V₁ := by
  let E := D.fullSetup hZ T z
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have hTL : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) :=
    (le_inf h.T_le_H hTV).trans
      (S.original_module_normalizer_normalizes_residual D hZ z hTV hH)
  have hnL : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) :=
    sup_le E.L₁.le_normalizer hTL
  have hnV : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₅ : Set G) := h.local_normalizes
  have hnZ : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₁ : Set G) := h.local_le.trans
    (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  have hW : ⁅E.L₁,E.V₅⁆ ⊔ E.V₁ ≤ E.V₅ := sup_le
    (le_normalizer_iff_commutator_le_right.mp (le_sup_left.trans h.local_normalizes))
    h.point_lt.le
  have hnW : E.L₁ ⊔ (T : Subgroup G) ≤
      normalizer ((⁅E.L₁,E.V₅⁆ ⊔ E.V₁ : Subgroup G) : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_sup,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hnL hg),
      mem_normalizer_iff_map_conj_eq.mp (hnV hg),
      mem_normalizer_iff_map_conj_eq.mp (hnZ hg)]
  rcases h.irreducible _ le_sup_right hW hnW with he | he
  · exfalso
    let P : Sylow 3 E.L₁ := Classical.choice inferInstance
    obtain ⟨hP,hcard⟩ := S.original_point_residual_sylow D hZ z hz hTz P
    let := hP
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 3 (by rw [hcard]; decide)
    have hx3 : (x.val.val : G)^3 = 1 := congrArg (fun y : P => (y.val.val : G))
      (show x ^ 3 = 1 by simpa only [hx] using pow_orderOf_eq_one x)
    have hx1 : (x.val.val : G) = 1 :=
      S.original_cubic_detected_on_point_quotient D hZ z hz hTV hTz hbound
        x.val.val x.val.property hx3 (fun w hw =>
          (le_sup_left.trans he.le) (commutator_mem_commutator x.val.property hw))
    have hxone : x = 1 := Subtype.ext (Subtype.ext hx1)
    simp [hxone] at hx
  · exact he.symm

variable [IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H)]
  (a : LocalQuotientAction H ((D.fullSetup hZ T z).UH H) (D.fullSetup hZ T z).V₁)

local instance original_source_span_elementary (E : Nonabelian.Setup G) (J : Subgroup G)
    [IsElementaryAbelian 2 (E.UH J)] :
    IsElementaryAbelian 2 (Chapter13.Section08.Source.UH J E.V₅) :=
  inferInstanceAs (IsElementaryAbelian 2 (E.UH J))

local instance original_source_span_normal (E : Nonabelian.Setup G) (J : Subgroup G)
    [IsElementaryAbelian 2 (E.UH J)] :
    (E.V₁.subgroupOf (Chapter13.Section08.Source.UH J E.V₅)).Normal :=
  inferInstanceAs ((E.V₁.subgroupOf (E.UH J)).Normal)

local instance original_source_quotient_elementary (E : Nonabelian.Setup G) (J : Subgroup G)
    [IsElementaryAbelian 2 (E.UH J)] :
    IsElementaryAbelian 2 (Chapter13.Section08.Source.Utilde J E.V₅ E.V₁) :=
  inferInstanceAs (IsElementaryAbelian 2 (E.UH J ⧸ E.V₁.subgroupOf (E.UH J)))

/-- The local quotient action is exactly the original source conjugation action. -/
private theorem original_source_action : IsSourceAction H (D.fullSetup hZ T z).V₅
    (D.fullSetup hZ T z).V₁ a.representation := by
  intro g u
  exact a.conjugation g u

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The literal point-span quotient is fully moved by the original component orbit. -/
theorem SourceHypothesis.original_abelian_exchanged_movement
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    subspaceCommutator a.representation ⊤
      (actorImage H (conjugateSpanBy K (T : Subgroup G))) = ⊤ := by
  let E := D.fullSetup hZ T z
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  obtain ⟨t,ht,hTH,htn,hOH,e,P,he,hP,hstar,hsol,hLB,hBM,hnB,
    heven,hrank,hOT,hBeq,hMeq⟩ :=
    S.original_abelian_exchanged_borel D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen hn (n := 2) (by decide) hm
  have hLO : E.L₁ ≤ conjugateSpanBy K (T : Subgroup G) := hLB.trans (borelLift_le H _ hOH _)
  apply source_moved_eq_top H E.V₅ E.V₁ a.representation (original_source_action S D hZ z a)
    K E.L₁ T (by simpa only [sup_assoc] using hgen.symm) hLO
    (le_sup_left.trans h.local_normalizes) h.point_lt.le
  exact (S.original_perpendicular_residual_movement D hZ z hz hTV hTz hbound hH).le

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- Both literal sections have no strong FF offender. The faithful image
identifications retain the original component orbit. -/
theorem SourceHypothesis.original_abelian_exchanged_section_noStrong
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    (∀ W : Subrepresentation a.representation, W ≠ ⊤ →
      ¬ W.toSubmodule ≤ fixedSpace a.representation
        (actorImage H (conjugateSpanBy K (T : Subgroup G))) →
      ¬ IsStrongFFModule (imageRepresentation W.toRepresentation)) ∧
    (∀ W : Subrepresentation a.representation, W ≠ ⊤ →
      ¬ IsStrongFFModule (imageRepresentation W.quotientRepresentation)) := by
  obtain ⟨t,ht,hTH,htn,F,hF,hfin,hchar,b,ha,hb,ho,hT,hts⟩ :=
    S.original_abelian_exchanged_actor D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen hn hm
  have hfull := S.original_abelian_exchanged_movement D hZ z hz hTV hTz hbound hTI hns
    hH hKH hK hgen a hn hm
  rw [←ho] at hfull ⊢
  exact b.section_exclusions_of_faithful_exclusion a.representation
    (fun _ _ _ _ ρ hf => ModuleAlternatives.SourceRecognition.exchanged_not_strong b ρ hf) hfull

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The original F.9 actor gives the maximal-section FF/central dichotomy
on U_H/V₁, with a nonzero image of the actual perpendicular seed. -/
theorem SourceHypothesis.original_abelian_exchanged_section_dichotomy
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    ∃ W : Subrepresentation a.representation, W ≠ ⊤ ∧
      (∀ Y : Subrepresentation a.representation, W ≤ Y → Y ≠ ⊤ → Y = W) ∧
      (sourceSeedSpace H (D.fullSetup hZ T z).V₅ (D.fullSetup hZ T z).V₁).map
        W.toSubmodule.mkQ ≠ ⊥ ∧
      ((IsFFModule (imageRepresentation W.toRepresentation) ∧
        IsFFModule (imageRepresentation W.quotientRepresentation)) ∨
        (subspaceCommutator a.representation W.toSubmodule
          (actorImage H (conjugateSpanBy K (T : Subgroup G))) = ⊥ ∧
          ∃ I, IsIrrPlus a.representation
            (actorImage H (conjugateSpanBy K (T : Subgroup G))) I ∧
            seedSpan a.representation I = ⊤)) := by
  let E := D.fullSetup hZ T z
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  obtain ⟨t,ht,hTH,htn,hOH,e,P,he,hP,hstar,hsol,hLB,hBM,hnB,
    heven,hrank,hOT,hBeq,hMeq⟩ :=
    S.original_abelian_exchanged_borel D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen hn (n := 2) (by decide) hm
  have hLO : E.L₁ ≤ conjugateSpanBy K (T : Subgroup G) := hLB.trans (borelLift_le H _ hOH _)
  have hq : IsQuasisimple (actorImage H K) :=
    (S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK).of_mulEquiv
      (componentStarEquiv H K hKH hK)
  obtain ⟨_,hU,b,B,hB,hBT,hEA,hquad,hcod,hfaith,_⟩ :=
    S.original_abelian_component_span_actors D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen
  have heq := a.representation_eq b
  rw [←heq] at hcod
  obtain ⟨hW,hQ⟩ := S.original_abelian_exchanged_section_noStrong D hZ z hz hTV hTz hbound
    hTI hns hH hKH hK hgen a hn hm
  exact exists_source_section_dichotomy H E.V₅ E.V₁ a.representation
    (original_source_action S D hZ z a) K E.L₁ T (by simpa only [sup_assoc] using hgen.symm)
    hLO hK hq (le_sup_left.trans h.local_normalizes) h.point_lt
    (S.original_perpendicular_residual_movement D hZ z hz hTV hTz hbound hH).le
    (B.map (QuotientGroup.mk' (pCore 2 H))) hEA hcod hfaith hW hQ

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The central branch admits a homogeneous Irr⁺ seed for the original
Sylow image, whose Sylow and whole-group orbit spans are both U_H/V₁. -/
theorem SourceHypothesis.original_abelian_exchanged_homogeneous_dichotomy
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    ∃ W : Subrepresentation a.representation, W ≠ ⊤ ∧
      (∀ Y : Subrepresentation a.representation, W ≤ Y → Y ≠ ⊤ → Y = W) ∧
      (sourceSeedSpace H (D.fullSetup hZ T z).V₅ (D.fullSetup hZ T z).V₁).map
        W.toSubmodule.mkQ ≠ ⊥ ∧
      ((IsFFModule (imageRepresentation W.toRepresentation) ∧
        IsFFModule (imageRepresentation W.quotientRepresentation)) ∨
       (subspaceCommutator a.representation W.toSubmodule
          (actorImage H (conjugateSpanBy K (T : Subgroup G))) = ⊥ ∧
        ∃ I, Homogeneous.IsIrrPlusWith a.representation
          (actorImage H (conjugateSpanBy K (T : Subgroup G))) (actorImage H T) I ∧
          seedSpan a.representation I = ⊤ ∧
          Homogeneous.orbitSpan a.representation ⊤ I = ⊤ ∧
          Homogeneous.orbitSpan a.representation (actorImage H T) I = ⊤)) := by
  obtain ⟨W,hW,hmax,hseed,halt⟩ := S.original_abelian_exchanged_section_dichotomy
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen a hn hm
  refine ⟨W,hW,hmax,hseed,?_⟩
  rcases halt with hff | ⟨hc,I,hI,_⟩
  · exact Or.inl hff
  · obtain ⟨t,ht,hTH,htn,F,hF,hfin,hchar,b,_,_,ho,hS,_⟩ :=
      S.original_abelian_exchanged_actor D hZ z hz hTV hTz hbound hTI hns
        hH hKH hK hgen hn hm
    have hTN : actorImage H T ≤ normalizer
        (actorImage H (conjugateSpanBy K (T : Subgroup G)) : Set (H ⧸ pCore 2 H)) := by
      let : b.orbit.Normal := b.orbit_normal
      rw [←ho,normalizer_eq_top]
      exact le_top
    have hp : IsPGroup 2 (actorImage H T) := by
      rw [←hS]
      exact b.sylow.isPGroup'
    obtain ⟨J,_,hJ⟩ := Homogeneous.exists_isIrrPlusWith_le_orbitSpan a.representation hTN hp hI
    have hfull := S.original_abelian_exchanged_movement
      D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen a hn hm
    have hspan := orbitSpan_eq_top_of_central_maximal a.representation _ hfull W hW hmax
      ((subspaceCommutator_eq_bot_iff a.representation _ _).mp hc) J hJ.isIrrPlus
    have hg : actorImage H (conjugateSpanBy K (T : Subgroup G)) ⊔ actorImage H T = ⊤ := by
      rw [←ho,←hS]
      exact b.generated
    let U : Subrepresentation a.representation :=
      Homogeneous.orbitSubrepresentation a.representation hTN hJ.isIrrPlus hg
    have hJU : seedSpan a.representation J ≤ U := by
      change (seedSpan a.representation J).toSubmodule ≤ U.toSubmodule
      apply Submodule.span_le.mpr
      rintro _ ⟨g,v,hv,rfl⟩
      exact U.apply_mem_toSubmodule g (Homogeneous.le_orbitSpan a.representation _ J hv)
    have hU : U = ⊤ := top_unique (hspan ▸ hJU)
    have hTfull : Homogeneous.orbitSpan a.representation (actorImage H T) J = ⊤ :=
      congrArg Subrepresentation.toSubmodule hU
    have hGfull : Homogeneous.orbitSpan a.representation ⊤ J = ⊤ := by
      apply top_unique
      rw [←hTfull]
      apply iSup_le
      intro t
      exact le_iSup (fun g : (⊤ : Subgroup (H ⧸ pCore 2 H)) => J.map (a.representation g))
        ⟨t,trivial⟩
    exact Or.inr ⟨hc,J,hJ,hspan,hGfull,hTfull⟩

end CFSG.Quasithin.Chapter12.Section06

