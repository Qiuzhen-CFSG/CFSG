module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.SourceReduction.Actor
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.SourceReduction.Interfaces
public import Theory.Representation.BinaryOffender.AmbientSectionTransport
public import Theory.SpecificGroups.PSL3Two.Cardinality

/-!
# Identify the source commutator with the original component module

The literal group inclusion U_L -> U_I is binary linear and intertwines
conjugation by every element of I*. Each source action difference belongs
to [U_I,L]. Conversely, full commutator generation of U_L puts the entire
image of the inclusion in that moved space. Thus its range is exactly the
space classified by B.5.1, including after restriction to J(I)*.

The resulting equivalence transports Irr+ with its actual fixed-vector
quotient. In the doubled case it transports full coordinates on the moved
subrepresentation, without inferring a splitting from quotient coordinates.
The last theorem is a conditional assembly step: its moved alternative and
parabolic-order premise remain to be obtained from the source comparison.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(1),
printed p.99, and 15.3.26–31, pp.1130–1132.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents.SourceReduction
open EightGeometry EightGeometry.NaturalModule EightGeometry.NaturalModule.Recognition
open Parabolics.Placement.ModelComparison
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable {G : Type*} [Group G] [Finite G]
  (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
  (hn : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S)
  (hf : HasCharacteristicTwo I)
  (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
  [IsElementaryAbelian 2 ((d.componentModule I c.L).subgroupOf I)]
  [IsElementaryAbelian 2 ((d.UI I).subgroupOf I)]

/-- The literal inclusion U_L -> U_I as a binary linear map. -/
noncomputable def componentEmbedding :
    Additive ((d.componentModule I c.L).subgroupOf I) →ₗ[ZMod 2]
      Additive ((d.UI I).subgroupOf I) :=
  (Subgroup.inclusion (comap_mono (componentModule_le_span d c))).toAdditive.toZModLinearMap 2

omit [Finite G] in
theorem componentEmbedding_injective : Function.Injective (componentEmbedding d c) := by
  intro x y h
  exact Additive.toMul.injective (Subtype.ext (congrArg (fun v => v.toMul.val) h))

theorem componentEmbedding_equivariant (hZI : d.Z ≤ I) (g : d.Star I)
    (v : Additive ((d.componentModule I c.L).subgroupOf I)) :
    componentEmbedding d c (componentAction d c hn hI hf P hP g v) =
      d.UIAction I hZI g (componentEmbedding d c v) := by
  obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective (localActionKernel d.Z I) g
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  exact (componentAction_apply d c hn hI hf P hP i v).trans
    (d.UIAction_apply I hZI i (componentEmbedding d c v)).symm

private theorem moved_eq_coinvariants {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (L : Subgroup D) :
    moved ρ L = Representation.Coinvariants.ker (ρ.comp L.subtype) := by
  apply congrArg (Submodule.span (ZMod 2))
  ext w
  constructor
  · rintro ⟨l, hl, v, _, rfl⟩
    exact ⟨(⟨l, hl⟩, v), rfl⟩
  · rintro ⟨⟨l, v⟩, rfl⟩
    exact ⟨l, l.property, v, trivial, rfl⟩

include hn hI hf P hP in
/-- The inclusion has exactly the full component commutator as its image. -/
theorem componentEmbedding_range (hZI : d.Z ≤ I) (hYL : d.Yplus ≤ c.L) :
    (componentEmbedding d c).range = moved (d.UIAction I hZI) (d.starImage I c.L) := by
  apply le_antisymm
  · have hfull : moved (componentAction d c hn hI hf P hP) (d.starImage I c.L) = ⊤ := by
      rw [moved_eq_coinvariants]
      exact FFSpecialization.componentAction_full d c hn hI hf P hP hYL
    have he := subspaceCommutator_map_embedding (d.UIAction I hZI)
      (componentAction d c hn hI hf P hP) (MonoidHom.id (d.Star I))
      (componentEmbedding d c)
      (fun g v => (componentEmbedding_equivariant d c hn hI hf P hP hZI g v).symm)
      (d.starImage I c.L) ⊤
    simp only [Subgroup.map_id, Submodule.map_top] at he
    change subspaceCommutator _ _ _ = (moved _ _).map _ at he
    rw [hfull, Submodule.map_top] at he
    rw [← he]
    exact subspaceCommutator_mono_left _ le_top _
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, _, rfl⟩
    obtain ⟨l, hl, rfl⟩ := hg
    have hm : (((d.UIAction I hZI (d.starMap I l) v - v).toMul : I) : G) ∈
        d.componentModule I c.L := by
      change _ ∈ ⁅d.UI I, c.L⁆
      rw [commutator_comm]
      have ha := d.UIAction_apply I hZI l v
      simpa only [toMul_sub, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv,
        ha, commutatorElement_def] using
        (commutator_mem_commutator hl v.toMul.property :
          ⁅(l : G), ((v.toMul : I) : G)⁆ ∈ ⁅c.L, d.UI I⁆)
    exact ⟨Additive.ofMul ⟨(d.UIAction I hZI (d.starMap I l) v - v).toMul.val, hm⟩, rfl⟩

omit [Finite G] [IsElementaryAbelian 2 ((d.componentModule I c.L).subgroupOf I)] in
/-- Restrict the source actor without changing the literal commutator space. -/
theorem thompson_moved_eq (hZI : d.Z ≤ I) :
    moved (d.thompsonStarAction I hZI)
        ((d.starImage I c.L).subgroupOf (d.thompsonStar I)) =
      moved (d.UIAction I hZI) (d.starImage I c.L) := by
  rw [moved_eq_coinvariants, moved_eq_coinvariants]
  exact FFSpecialization.coinvariants_subgroupOf _ _ _ (component_star_le_thompson d c)

/-- An Irr+ assertion on the actual source commutator transfers to all of U_L. -/
theorem component_isIrrPlus_of_source (hZI : d.Z ≤ I) (hYL : d.Yplus ≤ c.L)
    (h : IsIrrPlus (d.thompsonStarAction I hZI)
      ((d.starImage I c.L).subgroupOf (d.thompsonStar I))
      (moved (d.thompsonStarAction I hZI)
        ((d.starImage I c.L).subgroupOf (d.thompsonStar I)))) :
    IsIrrPlus (componentAction d c hn hI hf P hP) (d.starImage I c.L) ⊤ := by
  apply h.of_intertwining _ _ (componentThompsonEquiv d c).toMonoidHom
    (componentThompsonEquiv d c).surjective (componentEmbedding d c)
    (componentEmbedding_injective d c)
  · intro g v
    exact componentEmbedding_equivariant d c hn hI hf P hP hZI g.val.val v
  · rw [Submodule.map_top, componentEmbedding_range d c hn hI hf P hP hZI hYL,
      thompson_moved_eq]

/-- Actual coordinates on U_L from any source subrepresentation equal to
the full moved space. No splitting of a central quotient is used. -/
noncomputable def componentSectionEquiv (hZI : d.Z ≤ I) (hYL : d.Yplus ≤ c.L)
    (W : Subrepresentation (d.thompsonStarAction I hZI))
    (hW : W.toSubmodule = moved (d.thompsonStarAction I hZI)
      ((d.starImage I c.L).subgroupOf (d.thompsonStar I))) :
    Additive ((d.componentModule I c.L).subgroupOf I) ≃ₗ[ZMod 2] W.toSubmodule :=
  (LinearEquiv.ofInjective (componentEmbedding d c) (componentEmbedding_injective d c)).trans
    (LinearEquiv.ofEq _ _ (by
      rw [componentEmbedding_range d c hn hI hf P hP hZI hYL, hW, thompson_moved_eq]))

theorem componentSectionEquiv_apply (hZI : d.Z ≤ I) (hYL : d.Yplus ≤ c.L)
    (W : Subrepresentation (d.thompsonStarAction I hZI))
    (hW : W.toSubmodule = moved (d.thompsonStarAction I hZI)
      ((d.starImage I c.L).subgroupOf (d.thompsonStar I)))
    (v : Additive ((d.componentModule I c.L).subgroupOf I)) :
    (componentSectionEquiv d c hn hI hf P hP hZI hYL W hW v :
        Additive ((d.UI I).subgroupOf I)) = componentEmbedding d c v := rfl

/-- The coordinate map intertwines the original star component with its
literal inclusion in the classified Thompson actor. -/
noncomputable def componentSectionActionEquiv (hZI : d.Z ≤ I) (hYL : d.Yplus ≤ c.L)
    (W : Subrepresentation (d.thompsonStarAction I hZI))
    (hW : W.toSubmodule = moved (d.thompsonStarAction I hZI)
      ((d.starImage I c.L).subgroupOf (d.thompsonStar I))) :
    ActionEquiv ((componentAction d c hn hI hf P hP).comp (d.starImage I c.L).subtype)
      (W.toRepresentation.comp
        ((d.starImage I c.L).subgroupOf (d.thompsonStar I)).subtype) where
  groupEquiv := (componentThompsonEquiv d c).symm
  linearEquiv := componentSectionEquiv d c hn hI hf P hP hZI hYL W hW
  intertwines g v := by
    apply Subtype.ext
    exact componentEmbedding_equivariant d c hn hI hf P hP hZI g v

/-- Transfer full doubled coordinates, using one actor identification on
both natural summands. -/
noncomputable def component_double_of_source (hZI : d.Z ≤ I) (hYL : d.Yplus ≤ c.L)
    (W : Subrepresentation (d.thompsonStarAction I hZI))
    (hW : W.toSubmodule = moved (d.thompsonStarAction I hZI)
      ((d.starImage I c.L).subgroupOf (d.thompsonStar I)))
    (e : ActionEquiv (W.toRepresentation.comp
        ((d.starImage I c.L).subgroupOf (d.thompsonStar I)).subtype)
      (repeated binaryNatural 2)) :
    ActionEquiv ((componentAction d c hn hI hf P hP).comp (d.starImage I c.L).subtype)
      (repeated binaryNatural 2) where
  groupEquiv := (componentThompsonEquiv d c).symm.trans e.groupEquiv
  linearEquiv := (componentSectionEquiv d c hn hI hf P hP hZI hYL W hW).trans e.linearEquiv
  intertwines g v := by
    exact (congrArg e.linearEquiv
      ((componentSectionActionEquiv d c hn hI hf P hP hZI hYL W hW).intertwines g v)).trans
        (e.intertwines _ _)

/-- Conditional assembly of the full-module alternative. The source-action
sieve and the marked parabolic order are separate remaining inputs. -/
theorem smallAction_of_movedAlternative (hZI : d.Z ≤ I) (hYL : d.Yplus ≤ c.L)
    (h : MovedSmallAlternative (d.thompsonStarAction I hZI)
      ((d.starImage I c.L).subgroupOf (d.thompsonStar I)))
    (horder : Nat.card (d.starImage I c.L) = 168 →
      Nat.card ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)) = 24) :
    SmallActionAlternative (componentAction d c hn hI hf P hP)
      (d.starImage I c.L)
      ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)) := by
  cases h with
  | single h =>
    exact .single (component_isIrrPlus_of_source d c hn hI hf P hP hZI hYL h)
  | double W hW e =>
    let e' := component_double_of_source d c hn hI hf P hP hZI hYL W hW e
    exact .double e' (horder
      ((Nat.card_congr e'.groupEquiv.toEquiv).trans Matrix.PSL3Two.card_SL))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents.SourceReduction
