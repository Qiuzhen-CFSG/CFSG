module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Complete
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction

/-!
# Assembly of the linear-shadow contradiction

The common-core construction and the compatible-Cartan construction meet on
the same original groups, flag and quotient maps. The former supplies the
independent orthogonal marking, odd degree and Sylow placement; the latter
constructs compatible fields, invariant complements and the nonzero bilinear
commutator, whose primitive Cartan eigenvalues are inconsistent.

The Hall subgroup required by the common-core construction is chosen in the
proved solvable intersection H ∩ N_G(L). No field compatibility, complement,
pairing or terminal scalar action is assumed here. The field-four cover
obstruction is discharged inside the common-core construction before using
the odd-degree argument.

`proposition1132_of_preceding1137` still requires the actual outside residual
component and its quotient model in `Preceding1137`. The parameter-component
owner qt-d-1222-shadow-parameter-component supplies those conclusions; this
module does not treat them as preceding §§11.0--11.2 hypotheses. Final source
discharge remains with qt-d-1222-shadow-linear-geometry and the parent
qt-d-1222-natural-shadow-reduction.

Source: Aschbacher--Smith, refs/quasithin.pdf, Proposition 11.3.2 and
11.3.7--9, printed pp.770--775. The natural sections are V₂ and P/V₂,
and the two residuals are respectively O²(H) and O^{2′}(N_G(P)).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
open CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- Apply the compatible-field contradiction to the literal common-core state,
discharging every geometric and action premise of its terminal consumer. -/
theorem CommonCore.OrthogonalInput.false
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {X A : Subgroup G} {h : G}
    (d : OrthogonalInput D S m f H X A h) : False := by
  let := D.elementary
  let := pairCore_elementary d.source d.conjugator_mem d.conjugates_disjoint
  obtain ⟨o⟩ := source_orthogonal_marking d
  have hT : (T : Subgroup G) ≤ orthogonalJoin (f.Li 1) V h := by
    rw [(source_factorJoin_and_residual d).1]
    exact source_sylow_le_factorJoin_of_components d
      (source_residual_normal_component d).1 (source_local_normal_component d).1
  exact CompatibleCartan.false_of_ordered_source_geometry D S m f d.seed_fixed
    d.pair_field o (by rw [d.pair_field.card_eq, d.pair_degree, S.field.card_eq])
    d.local_core.symm d.seed_core d.intersection_eq_plane le_sup_left d.cartan
    ((source_orthogonal_cartan d).1.trans inf_le_left) (source_degree_odd d)
    d.residual_core.symm (source_pairCore_le_sylow d) hT
    (source_original_sylow_placement d).2.1

/-- All four clauses of 11.3.2 after the parameter-component output is supplied.
The Hall subgroup and all later shadow geometry are constructed internally. -/
theorem proposition1132_of_preceding1137
    (c : Coordinates D S.field) (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1137 c f H) :
    Proposition1132At D S (c.binarySubspace (f.space 0)) H := by
  classical
  by_contra hc
  obtain ⟨_, ⟨cK⟩, _⟩ := exists_selected_natural_action f s p.preceding hc
    p.global_s p.residual_model
  obtain ⟨A, _, hA, hHall⟩ := OddHall.exists_hall_containing_odd
    (H ⊓ normalizer (L : Set G)) ⊥ (Hall.source_common_solvable s cK) bot_le
    (by simp)
  obtain ⟨d⟩ := assemble_orthogonal_input c f hu s p hc A hA hHall
  exact d.orthogonal.false

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
