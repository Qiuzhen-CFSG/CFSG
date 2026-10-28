module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockReduction
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerAmbientResidual
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationPrefix
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFQuasisimple
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction
public import Theory.Representation.BinarySylowFixedSpace
public import Theory.GroupTheory.ReducedNormal.SylowCenter
public import Theory.Representation.BinaryPermutation.AlternatingEightSylowFixed
public import Stellmacher.CentralizerQuotientRepresentation

/-!
# The eight-letter row of the reducible normalizer argument

The actual seven-dimensional A₈ augmentation core excludes an escaping Sylow
normalizer. This supplies the Thompson equality for the literal O²-centralizer
core. The ambient residual theorem separately supplies the O^{3′} identity
using the quotient marking of the same action. Together they discharge the
existing eight-letter residual-construction consumer.
The original subtype maps, residuals and public contracts are unchanged.

Put H = LT and U = R₂(H). Under escape, J(T) moves the chosen V, hence U.
The faithful conjugation image on U therefore satisfies the complete B.5.1
hypotheses after restriction to its actual offender subgroup. Since C_V(L)
is nonzero, B.5.1(2) makes [U,L] an Irr⁺ member; containment then gives
[U,L] = V. Odd-coset averaging lifts every Sylow-fixed vector modulo V to
an L-fixed vector. The marked A₈ core itself has equal Sylow and L fixed
spaces, so Ω₁Z(T) centralizes L. Uniqueness now forces N_G(T) ≤ N_G(L).

This is a specialized alternative to the B.5.1(6)/B.4.2(10) route through
the canonical block module. The chosen augmentation-core marking does not
by itself identify that other module with a natural-plus-dual model.
No such identification or residual identity is assumed here.

Source: Aschbacher--Smith, B.5.1(2), printed p.99; 3.3.21(d--e), p.596;
12.2.16, pp.799--800. For the augmentation-core Sylow fixed line compare
12.6.1(2), p.823.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem thompson_moves_chosen [Finite G]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) := by
  intro hc
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hJQ : elementaryAbelianMaxJ (T : Subgroup G) ≤ Q := by
    change elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [← chosen_sylow_centralizer_eq_core h D structural]
    exact le_inf (sSup_le fun _ hA => hA.1) hc
  have he := elementaryAbelianMaxJ_eq_of_intermediate_finite (T : Subgroup G) Q hJQ hQT
  have hQne : Q ≠ ⊥ := fun he => D.ne_bot (bot_unique (D.le_core.trans_eq he))
  have hnQ : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hNJ := D.normal_subgroup_normalizer_le h.toHypothesis1221
    ((sSup_le fun _ hA => hA.1).trans (map_subtype_le _))
    (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup Q (pCore_isPGroup.map _) hQne)
    (hnQ.trans (normalizer_le_normalizer_elementaryAbelianMaxJ Q))
  apply hescape
  apply (normalizer_le_normalizer_elementaryAbelianMaxJ (T : Subgroup G)).trans
  rw [← he]
  exact hNJ

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
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    IsFFModule (representation (T := T) (L := L)) := by
  let S : Sylow 2 (H T L) := T.subtype le_sup_right
  have hUS : ReducedModule (H T L) ≤ (S : Subgroup (H T L)) :=
    (reducedPSubgroup_le_pCore 2 _).trans (pCore_isPGroup.le_sylow_of_normal S)
  have hJS : ¬ elementaryAbelianMaxJ (S : Subgroup (H T L)) ≤ projection.ker := by
    intro hj
    apply thompson_moves_chosen h D structural hescape
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
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    K₀ ≤ offenderSubgroup (representation (T := T) (L := L)) ∧
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((ρ₀).comp (offenderSubgroup ρ₀).subtype)
      ((K₀).subgroupOf (offenderSubgroup ρ₀))) := by
  let := component_normal D
  let := component_quasisimple D h.quasisimple
  exact ChapterB.QuasisimpleSource.SourceCompletion.ff_quasisimple_source_conclusion
    ρ₀ K₀ (quotient_two D) actor_core (component_sqtk D h.toHypothesis1221)
    representation_injective (ff h D structural hescape)

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
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    moved ρ₀ K₀ = D.space := by
  obtain ⟨hKJ, ⟨c⟩⟩ := source_conclusion h D structural hescape
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

/-- The actual A₈ core has no new vectors fixed only by a Sylow two-subgroup. -/
private theorem chosen_sylow_fixed [Finite G] (D : ChosenModule T L V)
    (E : ChapterB.QuasisimpleSource.ActionEquiv D.quotientAction
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8)))
    (P : Sylow 2 L) (v : D.space) (hv : ∀ l ∈ (P : Subgroup L), D.chosenAction l v = v) :
    ∀ l : L, D.chosenAction l v = v := by
  let f : L →* alternatingGroup (Fin 8) :=
    E.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f :=
    E.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))
  let S := P.mapSurjective hf
  have hfixed : ∀ a ∈ (S : Subgroup (alternatingGroup (Fin 8))),
      BinaryPermutation.alternatingCoreRepresentation (Fin 8) a (E.linearEquiv v) = E.linearEquiv v := by
    rintro a ⟨l, hl, rfl⟩
    exact (E.intertwines (QuotientGroup.mk' (pCore 2 L) l) v).symm.trans
      (congrArg E.linearEquiv (hv l hl))
  have hc := BinaryPermutation.alternatingEight_core_sylow_fixed_constant S (E.linearEquiv v) hfixed
  have hall := (BinaryPermutation.core_fixed_iff_constant (Ω := Fin 8) (by simp) (E.linearEquiv v)).mpr hc
  intro l
  apply E.linearEquiv.injective
  exact (E.intertwines (QuotientGroup.mk' (pCore 2 L) l) v).trans (hall _)

private theorem exists_sylow_in_component [Finite G] (D : ChosenModule T L V) :
    ∃ P : Sylow 2 L, ∀ l ∈ (P : Subgroup L), (l : G) ∈ (T : Subgroup G) := by
  let X := L.subgroupOf (H T L)
  let : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let S : Sylow 2 (H T L) := T.subtype le_sup_right
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_normal X
  let e : X ≃* L := subgroupOfEquivOfLe (le_sup_left : L ≤ H T L)
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  rintro l ⟨r, hr, rfl⟩
  rw [hR] at hr
  exact hr

open ChapterB.QuasisimpleSource in
private theorem omega_centralizes [Finite G]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (E : ActionEquiv D.quotientAction (BinaryPermutation.alternatingCoreRepresentation (Fin 8))) :
    omegaCenterIn (T : Subgroup G) ≤ centralizer (L : Set G) := by
  let i : L →* H T L := inclusion (show L ≤ H T L from le_sup_left)
  let ρ := (reducedRepresentation (H T L)).comp i
  have hd : ∀ a z, ρ a z - z ∈ D.space := by
    intro a z
    rw [← moved_eq_chosen h D structural hne hescape]
    have he : ρ a z = ρ₀ ((componentHom (T := T) (L := L) a).val) z := rfl
    rw [he]
    exact Submodule.subset_span ⟨(componentHom (T := T) (L := L) a).val,
      (componentHom (T := T) (L := L) a).property, z, Submodule.mem_top, rfl⟩
  obtain ⟨P, hP⟩ := exists_sylow_in_component D
  let S : Sylow 2 (H T L) := T.subtype le_sup_right
  have hZU := sylow_omegaCenter_le_reduced S (join_characteristicTwo h)
  intro z hz
  have hzdata := (mem_omegaCenterIn_iff _ _).mp hz
  let zH : H T L := ⟨z, (le_sup_right : (T : Subgroup G) ≤ H T L) hzdata.1⟩
  have hzS : zH ∈ omegaCenterIn (S : Subgroup (H T L)) := by
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hzdata.1, ?_, ?_⟩
    · intro a ha
      exact Subtype.ext (hzdata.2.1 a ha)
    · exact Subtype.ext hzdata.2.2
  let y : Additive (ReducedModule (H T L)) := Additive.ofMul ⟨zH, hZU hzS⟩
  have hy : y ∈ fixedSpace ρ (P : Subgroup L) := by
    intro a
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (a.val : G) * z * (a.val : G)⁻¹ = z
    rw [hzdata.2.1 a.val (hP a.val a.property), mul_inv_cancel_right]
  obtain ⟨w, hw, hyw⟩ := Representation.BinarySylowFixedSpace.fixed_lift_mod_trivial_quotient
    ρ P D.space hd y hy
  let v : D.space := ⟨y-w, hyw⟩
  have hv : ∀ a ∈ (P : Subgroup L), D.chosenAction a v = v := by
    intro a ha
    apply Subtype.ext
    change ρ a (y-w) = y-w
    have hy' : ρ a y = y := hy ⟨a, ha⟩
    rw [map_sub, hy', hw a]
  have hvall := chosen_sylow_fixed D E P v hv
  have hyall (a : L) : ρ a y = y := by
    have hv' : ρ a (y-w) = y-w := congrArg Subtype.val (hvall a)
    rw [map_sub, hw a] at hv'
    exact sub_left_inj.mp hv'
  intro l hl
  have he := congrArg (fun x : Additive (ReducedModule (H T L)) => (x.toMul.val : G)) (hyall ⟨l, hl⟩)
  change l * z * l⁻¹ = z at he
  exact mul_inv_eq_iff_eq_mul.mp he

end EightReducedAction

/-- In every reducible escaping row, B.5.1(2) puts the full reduced
L-commutator in the original chosen module. No A₈ marking is used here. -/
theorem reduced_commutator_le_chosen_of_escape [Finite G]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ⁅(ReducedModule (L ⊔ (T : Subgroup G))).map
      (L ⊔ (T : Subgroup G)).subtype, L⁆ ≤ V := by
  rw [commutator_comm]
  apply commutator_le.mpr
  rintro l hl _ ⟨w, hw, rfl⟩
  let v : Additive (ReducedModule (L ⊔ (T : Subgroup G))) := Additive.ofMul ⟨w, hw⟩
  let a := EightReducedAction.componentHom (T := T) (L := L) ⟨l, hl⟩
  have hm : EightReducedAction.representation a.val v - v ∈ D.space := by
    rw [← EightReducedAction.moved_eq_chosen h D structural hne hescape]
    exact Submodule.subset_span ⟨a.val, a.property, v, Submodule.mem_top, rfl⟩
  have hv := (EightReducedAction.mem_chosen D _).mp hm
  change l * (w : G) * l⁻¹ / (w : G) ∈ V at hv
  simpa only [commutatorElement_def, div_eq_mul_inv, Subgroup.subtype_apply] using hv

/-- The marked seven-dimensional A₈ core forces control of the Sylow normalizer. -/
theorem sylow_normalizer_le_of_alternatingEight_core [Finite G]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (E : ChapterB.QuasisimpleSource.ActionEquiv D.quotientAction
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8))) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  have hc := EightReducedAction.omega_centralizes h D structural hne hescape E
  let Z := omegaCenterIn (T : Subgroup G)
  have hZT : Z ≤ (T : Subgroup G) := fun z hz => ((mem_omegaCenterIn_iff _ _).mp hz).1
  have hTne : (T : Subgroup G) ≠ ⊥ := fun he => D.ne_bot (bot_unique (D.le_sylow.trans_eq he))
  have hZne : Z ≠ ⊥ := by
    have hh := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup
      (T : Subgroup G) (T : Subgroup G) le_rfl T.isPGroup' (T : Subgroup G).le_normalizer hTne
    exact fun he => hh (by rw [show omegaCenterIn (T : Subgroup G) = ⊥ from he, inf_bot_eq])
  have hLZ : L ≤ normalizer (Z : Set G) :=
    (le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)
  have hNZ : normalizer (T : Set G) ≤ normalizer (Z : Set G) := normalizer_le_normalizer_omegaCenterIn _
  exact hescape (hNZ.trans (D.normal_subgroup_normalizer_le h.toHypothesis1221
    (hZT.trans le_sup_right) hZne (sup_le hLZ ((T : Subgroup G).le_normalizer.trans hNZ))))

/-- The Thompson identity for the literal O²-centralizer core in the escaping A₈ row. -/
theorem alternatingEight_omegaResidual_thompson [Finite G]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (E : ChapterB.QuasisimpleSource.ActionEquiv D.quotientAction
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8))) :
    elementaryAbelianMaxJ (omegaResidualCore T L) =
      elementaryAbelianMaxJ ((L ⊔ (T : Subgroup G)).pCoreIn 2) :=
  (hescape (sylow_normalizer_le_of_alternatingEight_core h D structural hne E)).elim

/-- The actual action marking supplies the ambient residual identity without
normalizer escape or an identification with the omega-generated module. -/
theorem alternatingEight_omegaResidual [Finite G]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (E : ChapterB.QuasisimpleSource.ActionEquiv D.quotientAction
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8))) :
    (primeToResidual 3 (centralizer (omegaCenterIn (T : Subgroup G) : Set G))).map
      (centralizer (omegaCenterIn (T : Subgroup G) : Set G)).subtype = omegaLocalResidual T L :=
  omega_residual_eq_of_alternatingEight h D hne E.groupEquiv

/-- The concrete A₈ row discharges both clauses of the existing
residual-construction consumer, using the literal marked quotient. -/
theorem alternatingEightResidualConstruction [Finite G] : AlternatingEightResidualConstruction T L V := by
  intro h D structural _ hne hescape E
  exact ⟨alternatingEight_omegaResidual h D hne E,
    alternatingEight_omegaResidual_thompson h D structural hne hescape E⟩

/-- The existing block reduction now requires only the other three model rows. -/
theorem blockReductionSource_of_remaining_model_constructions [Finite G]
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (linearThree : LinearThreeBlockConstruction T L V)
    (six : AlternatingSixBlockConstruction T L V)
    (g2 : G2BlockConstruction T L V) : BlockReductionSource T L V :=
  blockReductionSource_of_model_constructions modules linearThree six g2
    alternatingEightResidualConstruction

/-- Application to the preserved normalizer conclusion, with the A₈ row discharged. -/
theorem sylow_normalizer_le_of_remaining_model_constructions [Finite G]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (linearThree : LinearThreeBlockConstruction T L V)
    (six : AlternatingSixBlockConstruction T L V)
    (g2 : G2BlockConstruction T L V)
    (terminal : BlockCentralizerSource T L V) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) :=
  sylow_normalizer_le_of_model_constructions h D structural hnone hne modules
    linearThree six g2 alternatingEightResidualConstruction terminal

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
