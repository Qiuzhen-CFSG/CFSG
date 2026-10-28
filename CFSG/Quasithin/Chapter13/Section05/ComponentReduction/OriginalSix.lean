module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.PlanePairs
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.Restriction
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.Conclusion
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction.Commutator
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction.ConjugatePairs
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.Displacement

/-!
# Original ordinary-A₆ component selection after13.5.20

The genuine normal-branch contradiction is applied just to N_H(L₁).
The selected F.9 application restricts to this subgroup; the original
maximal-local hypothesis supplies the required kernel argument. The
natural point-residual action and the actual G.2 plane application supply
the local conjugate-pair condition. These facts instantiate the Fitting
obstruction and select a moved C-component with its actual star image
and intrinsic two-core quotient.

Only the original maximal-local choice and earlier ambient seed-centralizer
containment remain explicit alongside the selected source application.
Source: Aschbacher–Smith13.5.18–20, printed pp.922–923.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
open Section08.SourceCompletion Fitting.SourceAction
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz) (h : D.Hypothesis)
  (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
include d h e

omit e in
/-- Natural point-residual generation recovers the original seed identity. -/
theorem seed_identity : D.Vplus = ⁅D.V,D.L₁⁆ := by
  apply le_antisymm
  · have he := Section07.ModelExclusions.seed_commutator_point_residual d
    rw [←residual_eq_sourceOne d h] at he
    exact he.symm.le.trans (commutator_mono d.seed_le le_rfl)
  · exact Section07.commutator_le_seed_of_centralizes_line d D.L₁
      (((map_subtype_le _).trans inf_le_left).trans le_sup_left)
      ((le_sup_left.trans h.local_le).trans h.H_centralizes)

omit e in
/-- The point normalizer supplies the full local SQTK hypothesis. -/
theorem local_sqtk : IsSQTK KnownSimple.IsKnownSimple D.H := by
  have hp : IsPGroup 2 D.V₁ := IsPGroup.of_card (n := 1) (by simpa using d.line_card)
  have hn : D.V₁ ≠ ⊥ := by
    intro he
    have hc := d.line_card
    rw [he,card_bot] at hc
    contradiction
  have hl : IsTwoLocal (normalizer (D.V₁ : Set G)) := ⟨D.V₁,hn,hp,rfl⟩
  have hHN : D.H ≤ normalizer (D.V₁ : Set G) :=
    h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
    ((d.counterexample.qtke.twoLocal_sqtk hl).subgroup
      (D.H.subgroupOf (normalizer (D.V₁ : Set G))))

/-- Original13.5.19 on the actual normalizer intersection. The selected
F.9 hypothesis restricts to this subgroup, so no universal F.9 family is
required. -/
theorem normalizer_conclusions
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hc : centralizer (D.Vplus : Set G) ≤ M ⊓ normalizer (D.V : Set G)) :
    Section08.Source.starImage D.H (D.H ⊓ normalizer (D.L₁ : Set G)) =
      normalizer (Section08.Source.starImage D.H D.L₁ : Set (Section08.Source.Hstar D.H)) ∧
    D.V ≤ (D.H ⊓ normalizer (D.L₁ : Set G)).pCoreIn 2 := by
  refine ⟨local_normalizer_image D h,?_⟩
  let J := D.H ⊓ normalizer (D.L₁ : Set G)
  have hVJ : D.V ≤ J := le_inf h.V_le_H
    (h.V_le_T.trans (local_residual_normalized D h))
  by_contra hnot
  have hout : ¬ J ≤ M := fun hJM => hnot
    ((le_inf hVJ (NormalBranch.SourceElimination.original_module_le_maximal_core d)).trans
      (inf_pCoreIn_le_of_le 2 hJM))
  have hJ := local_normalizer_mem_Hz D h M hout
  have h' := restricted_hypothesis d h e h1221 J hJ inf_le_left
  have hc' : ⁅D.V,(J ⊓ centralizer (D.Vplus : Set G)) ⊓
      (J ⊓ normalizer (D.V : Set G))⁆ ≤ D.V₁ :=
    (commutator_mono le_rfl (inf_le_left.trans inf_le_right)).trans
      (AmbientSource.source_seed_centralizer_displacement d hc)
  have hnab : ¬IsMulCommutative ({D with H := J} : ChapterF.Section09.Setup G).UH := by
    intro hab
    let : IsMulCommutative ({D with H := J} : ChapterF.Section09.Setup G).UH := hab
    exact hnot (h'.V_le_QH_of_UH_abelian hc')
  exact NormalBranch.SourceElimination.original_normal_a6_false (D := {D with H := J}) d h' e
    (seed_identity (D := D) d h) (normal_subgroupOf_of_le_normalizer inf_le_right) hnab

/-- Original13.5.20 on the actual local two-core quotient. The source
normal-A₆ contradiction supplies13.5.18–19. Plane-normalizer control from
the genuine G.2 application supplies the local pair condition. -/
theorem centralizes_fitting
    (hU : ¬IsMulCommutative D.UH)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hc : centralizer (D.Vplus : Set G) ≤ M ⊓ normalizer (D.V : Set G)) :
    Section08.Source.starImage D.H D.V ≤
      centralizer (fittingSubgroup (Section08.Source.Hstar D.H) : Set _) := by
  obtain ⟨himage,hcore⟩ := normalizer_conclusions d h e h1221 hc
  have hi := NormalBranch.SourceOrthogonal.seed_index d
  have hcard := NormalBranch.ReturningPlane.module_card d
  have hcentral : ⁅D.V,D.H ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁ :=
    (commutator_mono le_rfl inf_le_right).trans
      (AmbientSource.source_seed_centralizer_displacement d hc)
  have hpair : ∀ g ∈ D.H,
      D.V₁ < D.V ⊓ ChapterG.Section02.Setup.conjugate D.V g →
      IsPGroup 2 (D.V ⊔ ChapterG.Section02.Setup.conjugate D.V g : Subgroup G) := by
    intro g hg hgI
    exact twoGroup_pairs d h hU (D.H.inv_mem hg) hgI
  have hne : Section08.Source.starImage D.H D.V ≠ ⊥ := by
    intro he
    have hn := LocalGeometry.star_V_card_two h hi hU
    rw [he,card_bot] at hn
    contradiction
  have hpairs : ∀ x : Section08.Source.Hstar D.H,
      ¬IsPGroup 2 (Section08.Source.starImage D.H D.V ⊔
        (Section08.Source.starImage D.H D.V).conjBy x : Subgroup _) →
      Nat.card (Section08.Source.starImage D.H D.V ⊔
        (Section08.Source.starImage D.H D.V).conjBy x : Subgroup _) = 6 := by
    intro x hx
    obtain ⟨g,hg,_,he⟩ := lift_pair D.H D.V h.V_le_H x
    have hs := source_F95Six D h hi hne hpair hcentral hcard g hg (he.symm ▸ hx)
    exact pair_card_of_symmetric_three (he ▸ hs)
  have hYV : D.L₁ ≤ normalizer (D.V : Set G) :=
    (((map_subtype_le _).trans inf_le_left).trans le_sup_left).trans d.normalizes_V
  let : (D.V₁.subgroupOf D.UH).Normal := point_normal_in_UH h
  let : IsElementaryAbelian 2 (Quotient (D := D)) := quotient_elementary h
  by_contra hfit
  exact Fitting.false_of_fitting_failure_of_binary_action KnownSimple.IsKnownSimple D h
    (local_sqtk d h) hi hU D.L₁ (le_sup_left.trans h.local_le)
    (isPPerfect_embedded_pResidual 2 _) (NormalBranch.SourceStar.original_residual_quotient_card d h e)
    hYV himage hcore hpairs (representation h) (representation_injective h)
    (source_fixedCodim_two h hi hU hcard) hfit

/-- The actual moved C-component required after13.5.20. Its quotient and
star image are retained under the literal source quotient map. -/
theorem exists_component
    (hU : ¬IsMulCommutative D.UH)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hc : centralizer (D.Vplus : Set G) ≤ M ⊓ normalizer (D.V : Set G)) :
    ∃ C : Subgroup G, C ≤ D.H ∧ (C.subgroupOf D.H).IsCComponent ∧
      IsQuasisimple (Section08.Source.starImage D.H C) ∧
      Nonempty ((C ⧸ pCore 2 C) ≃* Section08.Source.starImage D.H C) ∧
      ⁅Section08.Source.starImage D.H C,Section08.Source.starImage D.H D.V⁆ ≠ ⊥ := by
  exact exists_component_of_fitting_centralized D h hU
    (centralizes_fitting d h e hU h1221 hc)
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
