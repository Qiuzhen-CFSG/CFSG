module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Source
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFQuasisimple
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Stellmacher.CentralizerQuotientRepresentation

/-!
# The original chosen module under Thompson movement

Let U=R₂(LT). Nontrivial J(T)-action on the original chosen V gives an
FF-module on the faithful conjugation image of LT on U. Its component image
is quasisimple, has two-group quotient, and inherits the actual SQTK data.
The full B.5.1 conclusion therefore applies to that same action.

If C_V(L) is nontrivial, the moved module cannot split from its fixed space.
B.5.1(2) makes [U,L] an Irr⁺ member; it contains the original chosen member,
so they agree. This proves the literal ambient commutator containment.
The Section06 OriginalOmega consumer supplies Thompson movement from
L=[L,J(T)], obtaining the canonical comparison used in 12.6.1(6).

This narrow proof module avoids the unrelated ambient-residual imports.
The original ReducedChosenMovement module reexports this theorem and retains
its previous imports. The faithful-action and Irr⁺ transports follow the existing eight-letter
normalizer proof in FusionReducibleNormalizerBlockReductionEight, with the
precise Thompson-action premise supplied directly. No structural1222 or
escaping Sylow-normalizer premise is needed.
Source: Aschbacher--Smith B.5.1(2), printed p.99, and 12.6.1(6), p.823,
combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ReducedChosenMovement
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
namespace EightReducedAction
private abbrev H (T : Sylow 2 G) (L : Subgroup G) := L ⊔ (T : Subgroup G)
private abbrev actor (T : Sylow 2 G) (L : Subgroup G) := (reducedConjugation (H T L)).range

private def projection : H T L →* actor T L := (reducedConjugation (H T L)).rangeRestrict
private theorem projection_surjective : Function.Surjective (projection (T := T) (L := L)) :=
  MonoidHom.rangeRestrict_surjective _

private abbrev representation : Representation (ZMod 2) (actor T L) (Additive (ReducedModule (H T L))) :=
  elementaryRepresentation (actor T L).subtype
local notation "ρ₀" => (representation (T := T) (L := L))

private theorem representation_projection (a : H T L) (w : Additive (ReducedModule (H T L))) :
    ρ₀ (projection a) w = reducedRepresentation (H T L) a w := rfl

private theorem projection_ker :
    (projection (T := T) (L := L)).ker = centralizer (ReducedModule (H T L) : Set (H T L)) := by
  ext a
  constructor
  · intro ha w hw
    have he := congrArg (fun f : MulAut (ReducedModule (H T L)) => (f ⟨w, hw⟩ : H T L))
      (congrArg Subtype.val (show projection a = 1 from ha))
    change a * w * a⁻¹ = w at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro ha
    apply Subtype.ext
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    change a * (w : H T L) * a⁻¹ = w
    rw [← ha w w.property, mul_inv_cancel_right]

private abbrev component : Subgroup (actor T L) := (L.subgroupOf (H T L)).map projection
local notation "K₀" => (component (T := T) (L := L))

private def componentHom : L →* (component (T := T) (L := L)) :=
  (projection.subgroupMap (L.subgroupOf (H T L))).comp
    (subgroupOfEquivOfLe (show L ≤ H T L from le_sup_left)).symm.toMonoidHom

private theorem componentHom_surjective : Function.Surjective (componentHom (T := T) (L := L)) :=
  (projection.subgroupMap_surjective _).comp (subgroupOfEquivOfLe le_sup_left).symm.surjective

private theorem component_normal (D : ChosenModule T L V) : (component (T := T) (L := L)).Normal := by
  let : (L.subgroupOf (H T L)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer D.sylow_normalizes_component)
  exact Normal.map inferInstance projection projection_surjective

private theorem chosen_irrPlus (D : ChosenModule T L V) :
    IsIrrPlus ρ₀ K₀ D.space := by
  apply D.irrPlus.isIrrPlus.of_intertwining (reducedRepresentation (H T L)) ρ₀
    (projection.subgroupMap (L.subgroupOf (H T L))) (projection.subgroupMap_surjective _)
    (LinearMap.id) Function.injective_id
  · intro l w
    rfl
  · exact Submodule.map_id _

private theorem component_ne_bot (D : ChosenModule T L V) : (component (T := T) (L := L)) ≠ ⊥ := by
  intro he
  apply (chosen_irrPlus D).not_le_fixedSpace ρ₀
  intro w hw k
  have hk : k.val = 1 := mem_bot.mp (he ▸ k.property)
  change ρ₀ k.val w = w
  rw [hk, map_one, Module.End.one_apply]

private theorem componentHom_core (D : ChosenModule T L V) :
    pCore 2 L ≤ (componentHom (T := T) (L := L)).ker := by
  intro l hl
  apply Subtype.ext
  apply Subtype.ext
  apply MulEquiv.ext
  intro w
  apply Subtype.ext
  apply Subtype.ext
  change (l : G) * (w.val : G) * (l : G)⁻¹ = (w.val : G)
  have hcore : (l : G) ∈ (H T L).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component) (mem_map_of_mem L.subtype hl)
  have hc := (le_centralizer_iff.mp (reducedPSubgroup_le_centralizer_pCore 2 (H T L)))
    (show (⟨l, (le_sup_left : L ≤ H T L) l.property⟩ : H T L) ∈ pCore 2 (H T L) from
      by
        obtain ⟨a, ha, he⟩ := hcore
        have he' : a = (⟨l, (le_sup_left : L ≤ H T L) l.property⟩ : H T L) := Subtype.ext he
        exact he' ▸ ha) w w.property
  have hc' : (w.val : G) * (l : G) = (l : G) * (w.val : G) :=
    congrArg (fun x : H T L => (x : G)) hc
  rw [← hc', mul_inv_cancel_right]

private def componentQuotientHom (D : ChosenModule T L V) :
    (L ⧸ pCore 2 L) →* (component (T := T) (L := L)) :=
  QuotientGroup.lift _ componentHom (componentHom_core D)

private theorem component_quasisimple (D : ChosenModule T L V)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) : IsQuasisimple (component (T := T) (L := L)) := by
  let := hq
  let : Nontrivial (component (T := T) (L := L)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr (component_ne_bot D)
  exact IsQuasisimple.of_surjective (componentQuotientHom D)
    (QuotientGroup.lift_surjective_of_surjective _ componentHom componentHom_surjective (componentHom_core D))

private theorem quotient_two (D : ChosenModule T L V) : letI := component_normal D
    IsPGroup 2 (actor T L ⧸ (component (T := T) (L := L))) := by
  let X := L.subgroupOf (H T L)
  let : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let := component_normal D
  have hp : IsPGroup 2 (H T L ⧸ X) := by
    apply isPGroup_quotient_of_sup_eq_top X ((T : Subgroup G).subgroupOf (H T L))
      T.isPGroup'.comap_subtype
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hx : X ≤ (K₀).comap projection := fun _ hx => mem_map_of_mem _ hx
  exact hp.of_surjective (QuotientGroup.map _ _ projection hx)
    (QuotientGroup.map_surjective_of_surjective _ _ projection
      ((QuotientGroup.mk'_surjective _).comp projection_surjective) hx)

private theorem actor_core : pCore 2 (actor T L) = ⊥ := by
  have hk : (reducedConjugation (H T L)).ker = centralizer (ReducedModule (H T L) : Set (H T L)) := by
    simpa only [projection, MonoidHom.ker_rangeRestrict] using (projection_ker (T := T) (L := L))
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange (reducedConjugation (H T L)))
  have hm := pCore_map_iso 2 e
  rw [isPReduced_reducedPSubgroup.quotient_pCore_eq_bot, Subgroup.map_bot] at hm
  exact hm.symm

private theorem component_sqtk [Finite G] (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    IsSQTK KnownSimple.IsKnownSimple (component (T := T) (L := L)) := by
  have hL : IsSQTK KnownSimple.IsKnownSimple L :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (show L ≤ H T L from le_sup_left))).mp
      (h.join_sqtk.subgroup (L.subgroupOf (H T L)))
  let := component_quasisimple D h.quasisimple
  have hs : ChapterA.Section02.IsSemisimple (component (T := T) (L := L)) := by
    apply top_unique
    exact le_sSup (show IsComponent (component (T := T) (L := L)) ⊤ from
      ⟨Subgroup.IsSubnormal.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  exact ⟨(show ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple L from
      ChapterA.Section02.theoremA_knownSimple).stronglyQuasithin_section
    hL.stronglyQuasithin hL.isKGroup
    (ChapterA.Section02.IsSectionOf.of_surjective componentHom componentHom_surjective) hs,
    hL.isKGroup.of_surjective componentHom componentHom_surjective⟩

private theorem representation_injective : Function.Injective (representation (T := T) (L := L)) := by
  intro a b he
  apply Subtype.ext
  apply MulEquiv.ext
  intro w
  exact congrArg (fun f : Module.End (ZMod 2) (Additive (ReducedModule (H T L))) =>
    (f (Additive.ofMul w)).toMul) he

private theorem ff [Finite G]
    (D : ChosenModule T L V)
    (hmove : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    IsFFModule (representation (T := T) (L := L)) := by
  let S : Sylow 2 (H T L) := T.subtype le_sup_right
  have hUS : ReducedModule (H T L) ≤ (S : Subgroup (H T L)) :=
    (reducedPSubgroup_le_pCore 2 _).trans (pCore_isPGroup.le_sylow_of_normal S)
  have hJS : ¬ elementaryAbelianMaxJ (S : Subgroup (H T L)) ≤ projection.ker := by
    intro hj
    apply hmove
    have hm := map_mono hj (f := (H T L).subtype)
    rw [← elementaryAbelianMaxJ_map_injective (H T L).subtype (H T L).subtype_injective,
      show (S : Subgroup (H T L)).map (H T L).subtype = (T : Subgroup G) from
        map_subgroupOf_eq_of_le le_sup_right] at hm
    intro a ha v hv
    obtain ⟨b, hb, he⟩ := hm ha
    rw [projection_ker] at hb
    obtain ⟨w, hw, hew⟩ := D.le_reduced hv
    rw [← he, ← hew]
    exact congrArg (fun x : H T L => (x : G)) (hb w hw)
  let σ := Representation.NormalElementaryQuotient.representation
    (ReducedModule (H T L)) projection projection_surjective projection_ker
  have hf : IsFFModule σ := Representation.NormalElementaryQuotient.isFFModule_of_thompson_not_le
    (ReducedModule (H T L)) projection projection_surjective projection_ker S hUS hJS
  apply hf.map_equivariant σ ρ₀ (MonoidHom.id _) Function.injective_id (LinearEquiv.refl _ _)
  intro a w
  obtain ⟨g, rfl⟩ := projection_surjective a
  apply Additive.toMul.injective
  apply Subtype.ext
  exact Representation.NormalElementaryQuotient.representation_apply
    (ReducedModule (H T L)) projection projection_surjective projection_ker g w

private theorem source_conclusion [Finite G]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmove : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    K₀ ≤ offenderSubgroup (representation (T := T) (L := L)) ∧
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((ρ₀).comp (offenderSubgroup ρ₀).subtype)
      ((K₀).subgroupOf (offenderSubgroup ρ₀))) := by
  let := component_normal D
  let := component_quasisimple D h.quasisimple
  exact ChapterB.QuasisimpleSource.SourceCompletion.ff_quasisimple_source_conclusion
    ρ₀ K₀ (quotient_two D) actor_core (component_sqtk D h.toHypothesis1221)
    representation_injective (ff D hmove)

private theorem mem_chosen (D : ChosenModule T L V)
    (w : Additive (ReducedModule (H T L))) : w ∈ D.space ↔ (w.toMul.val : G) ∈ V := by
  constructor
  · intro hw
    exact D.image_eq.le (mem_map_of_mem _ (mem_map_of_mem _ hw))
  · intro hw
    obtain ⟨v, ⟨a, ha, rfl⟩, he⟩ := D.image_eq.ge hw
    have he' : Additive.ofMul a = w := Additive.toMul.injective (Subtype.ext (Subtype.ext he))
    exact he' ▸ ha

open ChapterB.QuasisimpleSource in
private theorem moved_not_compl (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    ¬ IsCompl (moved ρ₀ K₀) (fixedSpace ρ₀ K₀) := by
  have hle : D.space ≤ moved ρ₀ K₀ := by
    rw [← (chosen_irrPlus D).choose_spec.1]
    exact subspaceCommutator_mono_left _ le_top _
  obtain ⟨⟨z, hz⟩, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hz1 : z ≠ 1 := fun he => hz1' (Subtype.ext he)
  obtain ⟨w, hw, he⟩ := D.le_reduced hz.1
  have he' : (w : G) = z := he
  let v : Additive (ReducedModule (H T L)) := Additive.ofMul ⟨w, hw⟩
  have hv : v ∈ moved ρ₀ K₀ := hle ((mem_chosen D v).mpr (by
    change (w : G) ∈ V
    exact he'.symm ▸ hz.1))
  have hvfix : v ∈ fixedSpace ρ₀ K₀ := by
    intro k
    obtain ⟨l, rfl⟩ := componentHom_surjective k
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (l : G) * (w : G) * (l : G)⁻¹ = (w : G)
    rw [he', hz.2 l l.property, mul_inv_cancel_right]
  intro hc
  have hv0 : v = 0 := hc.disjoint.le_bot ⟨hv, hvfix⟩
  apply hz1
  exact he'.symm.trans (congrArg (fun x : Additive (ReducedModule (H T L)) => (x.toMul.val : G)) hv0)

open ChapterB.QuasisimpleSource in
private theorem moved_eq_chosen [Finite G]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hmove : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    moved ρ₀ K₀ = D.space := by
  obtain ⟨hKJ, ⟨c⟩⟩ := source_conclusion h D hmove
  have hspace : c.sectionData.space.toSubmodule = moved ρ₀ K₀ := by
    rw [c.sectionData.space_eq, moved_comp_map, map_subgroupOf_eq_of_le hKJ]
  have hfix := fixedSpace_subgroupOf ρ₀ K₀ (offenderSubgroup ρ₀) hKJ
  have hn : ¬ IsCompl c.sectionData.space.toSubmodule
      (fixedSpace ((ρ₀).comp (offenderSubgroup ρ₀).subtype)
        ((K₀).subgroupOf (offenderSubgroup ρ₀))) := by
    rw [hspace, hfix]
    exact moved_not_compl D hne
  have hi := (IsIrrPlus.subgroupOf_iff ρ₀ K₀
    (offenderSubgroup ρ₀) hKJ c.sectionData.space.toSubmodule).mp (c.clause_two hn).1
  rw [hspace] at hi
  apply Eq.symm
  apply (chosen_irrPlus D).eq_of_le ρ₀ hi
  rw [← (chosen_irrPlus D).choose_spec.1]
  exact subspaceCommutator_mono_left _ le_top _


end EightReducedAction

/-- For the original reducible chosen module, B.5.1(2) puts the full reduced
L-commutator in the original chosen module. No A₈ marking is used here. -/
theorem reduced_commutator_le_chosen_of_thompson_movement [Finite G]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hmove : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    ⁅(ReducedModule (L ⊔ (T : Subgroup G))).map
      (L ⊔ (T : Subgroup G)).subtype, L⁆ ≤ V := by
  rw [commutator_comm]
  apply commutator_le.mpr
  rintro l hl _ ⟨w, hw, rfl⟩
  let v : Additive (ReducedModule (L ⊔ (T : Subgroup G))) := Additive.ofMul ⟨w, hw⟩
  let a := EightReducedAction.componentHom (T := T) (L := L) ⟨l, hl⟩
  have hm : EightReducedAction.representation a.val v - v ∈ D.space := by
    rw [← EightReducedAction.moved_eq_chosen h D hne hmove]
    exact Submodule.subset_span ⟨a.val, a.property, v, Submodule.mem_top, rfl⟩
  have hv := (EightReducedAction.mem_chosen D _).mp hm
  change l * (w : G) * l⁻¹ / (w : G) ∈ V at hv
  simpa only [commutatorElement_def, div_eq_mul_inv, Subgroup.subtype_apply] using hv


end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ReducedChosenMovement
