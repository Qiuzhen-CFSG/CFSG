module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableNoncommuting
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.CommutingCoreDerived

/-!
# The original nonsolvable branch with cyclic derived two-core

In the original commuting pair, both cores have noncyclic derived subgroups.
Thus a cyclic derived subgroup of O₂(H) forces the original natural modules
to fail to commute. The proved noncommuting construction supplies a separate
elementary subgroup of O²(H) with image four under the literal H → H/O₂(H),
and gives n(H)=2. The original 5.2.3 application therefore excludes every
cyclic-derived outside core, without a bound on its order.

The universal application retains the original SourceHypothesis after every
S,I rechoice and transports the multiple-overgroup guard. This strengthens
the abelian-core exclusion. General commuting cores with noncyclic derived
subgroups, the earlier source discharge, full 13.2.7/13.6.7 assembly and the
literal nonsingular hCv remain open.
Source: Aschbacher--Smith 13.2.8(1), p.880, and 5.2.3.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section02.A5Outside
open Section02.A5Outside.OriginalCentralization
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
open TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A cyclic derived outside core gives an actual residual lift and parameter two. -/
theorem original_nonsolvable_cyclic_derived_core_parameter
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃) (hc : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) (hcyclic : IsCyclic (_root_.commutator (pCore 2 H))) :
    (∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ A ≤ pResidual 2 H ∧
      Nat.card (A.map (QuotientGroup.mk' (pCore 2 H))) = 4) ∧
      ChapterE.generationParameter H = 2 := by
  obtain ⟨W,W₁,W₂,W₃,e,q,_,hq,hk,_,hr,he⟩ :=
    original_nonsolvable_marked_action d hc hmany h1332 hcontexts hH hZ hs
  have hjoin : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change (pResidual 2 H).map H.subtype ⊔
      ((T : Subgroup G).subgroupOf H).map H.subtype = H at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hm : ¬ V ≤ centralizer (W : Set G) := by
    intro hv
    apply (original_commuting_pair_noncyclic_cores d e hjoin hH
      (localActor_surjective_of_omega_movement d hH hZ) q hq hk he hv).1
    have ha := ((_root_.commutator (pCore 2 H)).equivMapOfInjective
      (pCore 2 H).subtype (pCore 2 H).subtype_injective).isCyclic.mp hcyclic
    rw [map_subtype_commutator] at ha
    have hb := ((⁅pCore 2 H,pCore 2 H⁆ : Subgroup H).equivMapOfInjective
      H.subtype H.subtype_injective).isCyclic.mp ha
    rwa [map_commutator] at hb
  exact original_nonsolvable_noncommuting_parameter d h1332 hH hZ hs e q hq hk hr he hm

/-- Apply the original 5.2.3 to the same H, with its generation premise discharged. -/
theorem original_nonsolvable_cyclic_derived_core_model
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃) (hc : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) (hcyclic : IsCyclic (_root_.commutator (pCore 2 H))) :
    ClassificationModels.IsQTKEModel G := by
  have hn := (original_nonsolvable_cyclic_derived_core_parameter d hc hmany h1332 hcontexts
    hH hZ hs hcyclic).2
  exact main_model_of_source523_omega_movement d h523 hH hZ (by omega)

/-- Every guarded original rechoice in a counterexample has noncyclic derived core. -/
theorem universal_original_nonsolvable_noncyclic_core
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : IsA5Counterexample G) (hno : ¬ ClassificationModels.IsQTKEModel G)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (S : Sylow 2 G) (I : Subgroup G) (standing : SourceHypothesis S I)
    (H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) : ¬ IsCyclic (_root_.commutator (pCore 2 H)) := by
  obtain ⟨V,V₁,V₂,V₃,⟨d⟩⟩ := hcontexts S I standing
  have hmanyS : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  exact fun hcyclic => hno (original_nonsolvable_cyclic_derived_core_model
    d hc hmanyS h1332 hcontexts h523 hH hZ hs hcyclic)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
