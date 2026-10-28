module
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerSource.DoubleThree
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.AlternatingSixMoved
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient

/-!
# Excluding the alternating-six fixed-layer component

For the literal component J and best offender D, restrict to E = J ∨ D.
The faithful whole Irr⁺ plus action kills O₂(E), and E/J is a two-group.
Thus J is self-centralizing in E. The original SQTK quotient presentation
supplies SQTK for this actual component through the proved semisimple-section
theorem. Complete B.5.1 then forces the moved space of its faithful FF action
to be Irr⁺: the order-360 component admits none of the reducible linear rows.
This contradicts the two noncentral layers in the original tilde action.

The second theorem applies this argument to the literal invariant moved
subspace and its faithful action image, preserving the source's actor and
subgroup inclusions. No rank-one assumption is made on A₆.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.7.16(2), printed p.944, using B.5.1 and B.5.6.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07
open ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- A component of order 360 cannot have a non-Irr⁺ whole moved FF module
alongside the faithful whole Irr⁺ plus action. -/
theorem alternatingSix_of_component_overgroup
    {V₀ : Type*} [AddCommGroup V₀] [Module (ZMod 2) V₀]
    [FiniteDimensional (ZMod 2) V₀]
    (σ : Representation (ZMod 2) G V) (hf : Function.Injective σ)
    (σ₀ : Representation (ZMod 2) G V₀) (hf₀ : Function.Injective σ₀)
    (cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple G)
    {J D : Subgroup G} [J.Normal] [IsSimpleGroup J]
    (hi : IsIrrPlus σ₀ J ⊤) (hJ : IsComponent G J)
    (hc : Nat.card J = 360) (hD2 : IsPGroup 2 D)
    (hD : IsBestOffender σ D)
    (hm : moved σ J = ⊤) (hn : ¬ IsIrrPlus σ J ⊤) : False := by
  let E := J ⊔ D
  let C := J.subgroupOf E
  have hJE : J ≤ E := le_sup_left
  have hDE : D ≤ E := le_sup_right
  let : C.Normal := inferInstance
  let : IsQuasisimple J := hJ.2
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hJE).symm
  let : IsSimpleGroup C := (subgroupOfEquivOfLe hJE).isSimpleGroup
  have hcore := component_overgroup_twoCore_eq_bot σ₀ hf₀ hi hJ E hJE
  have hD' := hD.subgroupOf σ hDE
  have hquot : IsPGroup 2 (E ⧸ C) := by
    apply isPGroup_quotient_of_sup_eq_top C (D.subgroupOf E) hD2.comap_subtype
    rw [← Subgroup.subgroupOf_sup hJE hDE, Subgroup.subgroupOf_self]
  have hcentral : centralizer (C : Set E) = ⊥ :=
    centralizer_eq_bot_of_simple_two_quotient C
      (Group.IsPerfect.not_isMulCommutative C) hquot hcore
  have hc' : Nat.card C = 360 :=
    (Nat.card_congr (subgroupOfEquivOfLe hJE).toEquiv).trans hc
  let cov := cover.subgroup E
  let f : cov.Cover →* E := cov.equiv.toMonoidHom.comp (QuotientGroup.mk' cov.kernel)
  have hfq : Function.Surjective f :=
    cov.equiv.surjective.comp (QuotientGroup.mk'_surjective cov.kernel)
  have hsq : IsSQTK KnownSimple.IsKnownSimple C :=
    ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.quasisimple_section_sqtk
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple) cov.sqtk
      ((ChapterA.Section02.IsSectionOf.subgroup C).ambient_surjective f hfq)
  have hi' := SourceCompletion.ff_card360_moved_irrPlus
    (σ.comp E.subtype) C hc' hcentral hsq (hf.comp E.subtype_injective) ⟨_,hD'.isOffender _⟩
  rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hJE] at hi'
  rw [show subspaceCommutator σ ⊤ J = ⊤ from hm] at hi'
  exact hn ((IsIrrPlus.subgroupOf_iff σ J E hJE ⊤).mp hi')


/-- The literal faithful action on the tilde component's moved space excludes
the A₆ row of the original fixed-layer movement alternative. -/
theorem component_tilde_alternatingSix_false
    {V₀ : Type*} [AddCommGroup V₀] [Module (ZMod 2) V₀]
    [FiniteDimensional (ZMod 2) V₀]
    (ρ : Representation (ZMod 2) G V)
    (σ₀ : Representation (ZMod 2) G V₀) (hf₀ : Function.Injective σ₀)
    (cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple G)
    {J D : Subgroup G} [J.Normal] [IsSimpleGroup J]
    (hi : IsIrrPlus σ₀ J ⊤) (hJ : IsComponent G J) (hc : Nat.card J = 360)
    (hp : ∀ k : G, (∀ v ∈ subspaceCommutator ρ ⊤ J,ρ k v = v) → k = 1)
    (hn : ¬ IsIrrPlus ρ J (subspaceCommutator ρ ⊤ J))
    (hD : IsBestOffender (subspaceImageRepresentation ρ (subspaceCommutator ρ ⊤ J))
      (restrictedSubgroup ρ (subspaceCommutator ρ ⊤ J) D))
    (hD2 : IsPGroup 2 D) : False := by
  let I := subspaceCommutator ρ ⊤ J
  have hs : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ I :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) (by rw [J.normalizer_eq_top])
  let τ := wholeSubspaceAction ρ I hs
  have hf := wholeSubspaceAction_faithful ρ I hs hp
  have hDτ := wholeSubspaceAction_bestOffender ρ I hs hp hD
  let : IsQuasisimple J := hJ.2
  let : Group.IsPerfect J := inferInstance
  have hm : moved τ J = ⊤ := by
    apply Submodule.map_injective_of_injective I.subtype_injective
    have hh := subspaceCommutator_map_embedding ρ τ (MonoidHom.id G)
      I.subtype (fun g v => (wholeSubspaceAction_apply ρ I hs g v).symm) J ⊤
    simpa only [Subgroup.map_id,Submodule.map_top,Submodule.range_subtype, I,
      subspaceCommutator_idempotent_of_perfect] using hh.symm
  have hnτ : ¬ IsIrrPlus τ J ⊤ := by
    intro hι
    apply hn
    have hι' : IsIrrPlus τ (J.map (MonoidHom.id G)) ⊤ := by
      simpa only [Subgroup.map_id] using hι
    have hh := IsIrrPlus.map_embedding ρ τ (MonoidHom.id G) I.subtype
      I.subtype_injective (fun g v => (wholeSubspaceAction_apply ρ I hs g v).symm) J ⊤ hι'
    simpa only [Submodule.map_top,Submodule.range_subtype] using hh
  exact alternatingSix_of_component_overgroup τ hf σ₀ hf₀ cover hi hJ hc hD2 hDτ hm hnτ

end CFSG.Quasithin.Chapter13.Section07
