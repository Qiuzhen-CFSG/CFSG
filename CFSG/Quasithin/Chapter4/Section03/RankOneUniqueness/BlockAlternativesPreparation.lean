module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Configuration
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Star
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedLinearTwo
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels

/-!
# Literal source inputs for the rank-one block alternatives

The original configuration already provides a normal component and its
escaping inclusion. C.4.4 therefore supplies the exact C.2.7 input, with
R = O₂(I), without another source premise. In the block branch the star
quotient is the full quotient by O₂, with its projection equation preserved.
The canonical moved/fixed section transports an actual action marking back
to c.K, including its module intertwining data.

The proved constrained obstructions remove the SL₂ and A₅ star rows.
The radical-action normalizer also contains a nontrivial perfect subgroup,
so it is not solvable. These are inputs to the remaining concrete row
recognitions; neither a normalizer equality nor the group catalogue asserts
the block trichotomy.
Source: Aschbacher--Smith C.4.3--7, pp.152--153, and 4.3.7, pp.615--616.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterC Chapter1.RadicalExclusions.ModelReduction
open FullSieve.SourceInterface ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

omit [Finite G] in
/-- The escaping component is outside the literal local subgroup of C.2.8. -/
theorem SourceConfiguration.block_source_outside (c : SourceConfiguration T L) :
    ¬ c.K ≤ (c.H ⊓ normalizer (L : Set G)).subgroupOf c.H := by
  intro hle
  apply c.component_outside
  rintro x ⟨k,hk,rfl⟩
  exact (hle hk).2

/-- C.4.4 is discharged by the existing original-source theorem. -/
theorem SourceConfiguration.block_source_input (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) :
    Input KnownSimple.IsKnownSimple c.H (c.I.pCoreIn 2)
      (c.H ⊓ normalizer (L : Set G)) (c.K.map c.H.subtype) :=
  c.c28.constrained_source_input c.K c.component c.quotient c.block_source_outside hf

omit [Finite G] in
/-- Transport shortness along the actual inclusion K ≤ H ≤ G. -/
theorem SourceConfiguration.block_ambient_short (c : SourceConfiguration T L)
    (hb : IsBlock c.K) : IsShort (c.K.map c.H.subtype) :=
  hb.short.of_mulEquiv (c.K.equivMapOfInjective c.H.subtype c.H.subtype_injective)

omit [Finite G] in
/-- The original radical lies in H = N_G(K). -/
theorem SourceConfiguration.block_radical_normalizes (c : SourceConfiguration T L) :
    c.I.pCoreIn 2 ≤ normalizer (c.K.map c.H.subtype : Set G) :=
  ((pCoreIn_le 2 c.I).trans c.I_le_H).trans c.normalizer_component.le

/-- The actual star kernel is the two-core of KR in the block branch. -/
theorem SourceConfiguration.block_star_kernel (c : SourceConfiguration T L)
    (hb : IsBlock c.K) :
    starKernel (c.K.map c.H.subtype) (c.I.pCoreIn 2) =
      pCore 2 (c.K.map c.H.subtype ⊔ c.I.pCoreIn 2 : Subgroup G) :=
  BlockOmega.starKernel_eq_core (c.block_ambient_short hb)
    (isPGroup_pCoreIn 2 c.I) c.block_radical_normalizes

/-- No central kernel is discarded in the literal component core quotient. -/
@[expose] noncomputable def SourceConfiguration.block_star_quotientEquiv
    (c : SourceConfiguration T L) (hb : IsBlock c.K) :
    (c.K ⧸ pCore 2 c.K) ≃*
      starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) :=
  let e := c.K.equivMapOfInjective c.H.subtype c.H.subtype_injective
  (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (BlockOmega.coreStarEquiv (c.block_ambient_short hb)
      (isPGroup_pCoreIn 2 c.I) c.block_radical_normalizes)

/-- The full quotient identification retains the original projection. -/
@[simp] theorem SourceConfiguration.block_star_quotientEquiv_mk
    (c : SourceConfiguration T L) (hb : IsBlock c.K) (k : c.K) :
    c.block_star_quotientEquiv hb (QuotientGroup.mk' (pCore 2 c.K) k) =
      toStarImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.K.equivMapOfInjective c.H.subtype c.H.subtype_injective k) := rfl

/-- The complete group catalogue of K*, retaining concrete isomorphisms. -/
theorem SourceConfiguration.block_star_models (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) :
    C27Source.StarModels.Model
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)) :=
  C27Source.star_model_from_source (c.block_source_input hf)

/-- The C.4.6 rank-one obstruction on the actual star component. -/
theorem SourceConfiguration.block_star_not_linearTwo (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (F : BinaryField)
    (e : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F.Carrier) : False :=
  c.c28.no_constrained_component_star_linear_two c.K c.component c.quotient
    c.block_source_outside hf F e

/-- Minimal simplicity eliminates the A₅ star row. -/
theorem SourceConfiguration.block_star_not_alternatingFive (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (e : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
      alternatingGroup (Fin 5)) : False :=
  c.c28.no_constrained_component_star_alternating_five c.K c.component c.quotient
    c.block_source_outside hf e

/-- The radical's automorphism normalizer contains a nontrivial perfect image. -/
theorem SourceConfiguration.block_radical_action_normalizer_not_solvable
    (c : SourceConfiguration T L) :
    ¬ Group.IsSolvable (normalizer
      (coreCentralActorImage c.K ((c.I.pCoreIn 2).subgroupOf c.H) :
        Set (MulAut (coreCentralQuotient c.K)))) := by
  let X := conjugateSpanBy L (c.H ⊓ normalizer (L : Set G))
  let A := X.subgroupOf c.H
  let B := coreCentralActorImage c.K A
  have hXH : X ≤ c.H :=
    (conjugateSpanBy_le_self c.c28.component_le).trans c.c28.local_le
  let : Group.IsPerfect X := c.c28.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXH).symm.surjective
  let : Group.IsPerfect B := coreCentralActorImage_perfect c.K A
    (c.c28.constrained_span_normalizes_intrinsic c.K c.component c.quotient)
  have hne : B ≠ ⊥ := c.c28.constrained_span_action_nontrivial
    c.K c.component c.quotient c.block_source_outside
  let : Nontrivial B := B.nontrivial_iff_ne_bot.mpr hne
  have hn : B ≤ normalizer
      (coreCentralActorImage c.K ((c.I.pCoreIn 2).subgroupOf c.H) :
        Set (MulAut (coreCentralQuotient c.K))) := by
    apply coreCentralActorImage_normalizes
    intro a ha r
    exact c.c28.span_normalizes_radical ha (r : G)
  intro hs
  let := hs
  exact Group.IsPerfect.not_isSolvable B
    (Group.isSolvable_of_isSolvable_injective (f := inclusion hn) (inclusion_injective hn))

open Representation Representation.BinaryOffender
open scoped IsMulCommutative

/-- The canonical moved/fixed section on the literal star module of the source. -/
@[expose] noncomputable def SourceConfiguration.block_star_section
    (c : SourceConfiguration T L) :
    MovedSection (starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2))
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)) := by
  let A := c.K.map c.H.subtype
  let R := c.I.pCoreIn 2
  let : (A.subgroupOf (A ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer c.block_radical_normalizes)
  let : (starImage A R A).Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  exact MovedSection.ofNormal (starRepresentation A R) (starImage A R A)

/-- Source application of the moved-section bridge, on c.K with its actual
quotient and conjugation. The marked section action remains an explicit premise. -/
theorem SourceConfiguration.block_model_of_star_moving
    (c : SourceConfiguration T L) (hb : IsBlock c.K)
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) A W)
    (E : ActionEquiv (c.block_star_section.action.comp
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)).subtype) σ) :
    IsLinearBlockModel c.K σ := by
  let K := c.K.map c.H.subtype
  let R := c.I.pCoreIn 2
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer c.block_radical_normalizes)
  have hm := BlockOmega.model_of_star_moving (c.block_ambient_short hb)
    (isPGroup_pCoreIn 2 c.I) c.block_radical_normalizes σ E
  exact hm.of_mulEquiv (c.K.equivMapOfInjective c.H.subtype c.H.subtype_injective).symm

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
