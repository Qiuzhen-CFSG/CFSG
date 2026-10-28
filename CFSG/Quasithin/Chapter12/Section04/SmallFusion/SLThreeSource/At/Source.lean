module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.At.Residuals

/-!
# Original L₃ fusion from the guarded inputs at G,T

The local module classification recovers the actual marked extension. Thompson
movement constructs the omega supplement and plane. The independent MS and
fixed-action calculations eliminate the fixed-residual escape, while the
centralizing line and Sylow inverter eliminate the moving-residual escape.
The resulting literal Sylow witness separates the fixed involution from the
other vectors and supplies L-controlled fusion on the original V.

The only earlier source inputs are Structural1222At and Theorem1222ModulesAt
at this G,T, with the original multiple-overgroup guard. No universal source
classifier or local geometry/residual callback is assumed. Their earlier
source producers and final discharge owners remain the Section 12.2 and
Section 13.3/14.3 source tasks.

Source: Aschbacher–Smith, 12.4.5–7, printed pp.813–814.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.At
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal two-member elementary family in the fixed-residual escape. -/
theorem fixed_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) (d : LocalGeometry D)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hline : normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G)) :
    ∃ A : Subgroup G, V ∈ Stellmacher.elementaryAbelianMaxSubgroups d.R ∧
      Stellmacher.elementaryAbelianMaxSubgroups d.R ⊆ {V, A} := by
  have marked := alternative_of_modules modules
  have b := d.fixedBlockIdentities_without_binary_at h structural marked hmodel hne hescape
  have hself := (fixedBlock_selfCentralizing_at h structural marked hmodel hne d
    hescape hline b.product b.residual_centralizer).1
  have a := fixedBlockActionCalculation_at structural marked h D hmodel hne d hself
  exact fixedBlock_pair_of_plane_at h structural marked hmodel hne d hescape hself
    a.module_card a.actor_index a.fixed_plane

/-- The moving-residual escape is impossible, with both actual actions supplied. -/
theorem false_of_moving_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) (d : LocalGeometry D)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G)) : False := by
  have marked := alternative_of_modules modules
  exact d.false_of_moving_without_binary_at h structural marked hmodel hne hescape hmoves
    (d.centralizingLine_card_at h structural marked hmodel hne hescape hmoves)
    (d.movingLineInverter_at h structural marked hmodel hne hescape)

/-- The original moving-residual contract follows from its source contradiction. -/
theorem moving_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) (d : LocalGeometry D)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G)) :
    Nonempty (FourResidualGeometry d) :=
  (false_of_moving_residual h D structural modules hmodel hne d hescape hmoves).elim

/-- Promote the actual local Sylow to the whole vector centralizer. -/
theorem sylow_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) (d : LocalGeometry D) :
    Chapter1.IsSylowIn 2 d.R (centralizer ({d.v} : Set G)) := by
  apply sylow_centralizer_of_normalizer_le d.v d.local_sylow
  by_contra hescape
  by_cases hline : normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G)
  · obtain ⟨A, hV, hpair⟩ := fixed_residual h D structural modules hmodel hne d hescape hline
    have marked := alternative_of_modules modules
    obtain ⟨_, _, _, _, hi⟩ := d.escape_geometry_at h structural marked hmodel hne hescape
    obtain ⟨_, _, _, _, _, hM, _, _⟩ := exists_slThree_fixed_involution_setup_at
      h D structural marked uniquenessEarlier_knownSimple hmodel hne
    exact not_index_three_of_maxFamily_pair d.R V A (normalizer (L : Set G))
      hM hV hpair hi
  · exact false_of_moving_residual h D structural modules hmodel hne d hescape hline

/-- Source 12.4.6, including the literal index-two witness in the original T. -/
theorem sylow_witness_of_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ∃ (E : Subgroup G) (v : G), E ≤ V ∧ Nat.card E = 4 ∧ v ∈ E ∧
      v ∉ fixedSubgroup L V ∧
      ((T : Subgroup G) ⊓ centralizer (E : Set G)).relIndex T = 2 ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (E : Set G))
        (centralizer ({v} : Set G)) := by
  obtain ⟨d⟩ := local_geometry h D hmany structural modules hmodel hne
  exact ⟨d.E, d.v, d.le_module, d.card_plane, d.mem_plane, d.nonfixed, d.index,
    sylow_centralizer h D structural modules hmodel hne d⟩

/-- Source 12.4.7: fixed involution, weak closure in V, and L-controlled fusion. -/
theorem fusion_of_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ∃ z : G, orderOf z = 2 ∧ fixedSubgroup L V = zpowers z ∧
      centralizer ({z} : Set G) ≤ normalizer (V : Set G) ∧
      (∀ g : G, MulAut.conj g z ∈ V → MulAut.conj g z = z) ∧
      ∀ x ∈ V, ∀ y ∈ V, IsConj x y → ∃ l ∈ L, MulAut.conj l x = y := by
  obtain ⟨E, v, hEV, _, hvE, hv, hi, hR⟩ :=
    sylow_witness_of_source h D hmany structural modules hmodel hne
  exact source_slThree_fusion_at h D structural (alternative_of_modules modules)
    uniquenessEarlier_knownSimple hmodel hne v (hEV hvE) hv
    ((T : Subgroup G) ⊓ centralizer (E : Set G)) inf_le_left hi hR

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.At
