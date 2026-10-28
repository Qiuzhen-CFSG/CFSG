module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableAction
public import CFSG.Quasithin.Chapter13.Section05.A5Source.CrossModule

/-!
# Comparing both original natural modules in the nonsolvable outside branch

Construct the Context on the same embedded O²(H) and retain its full marked
S₅ action, omega orbit and two-core kernel. The original module V is either
inside O₂(H), or its action on the residual's natural module is an outer
four-group. Consequently, if V lies in O²(H), it already lies in O₂(H).
This proves that V itself cannot be the missing elementary residual lift.

The universal application constructs both Contexts after every original S,I
rechoice, retaining SourceHypothesis and transporting the multiple-overgroup
guard. No generation conclusion is added as a premise or inferred from the
quotient. Constructing a different elementary residual lift, or excluding the
remaining ambient configuration, stays with the original assembly owner.
Earlier Context/13.3.2 inputs retain their existing producers.

Source: Aschbacher--Smith 13.2.8(1), printed p.880; the hyperplane input is
13.2.3(1), pp.878--879. This is not unconditional 13.2.7 or 13.6.7.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
open Section05.A5Source Section02.A5Outside
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Comparison with the original natural module, retaining the same residual,
whole omega orbit, quotient map and natural-module marking. -/
theorem original_nonsolvable_cross_module
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
    (hs : ¬ Group.IsSolvable H) :
    ∃ (W W₁ W₂ W₃ : Subgroup G)
      (e : Context T ((pResidual 2 H).map H.subtype) W W₁ W₂ W₃)
      (q : H →* Equiv.Perm (Fin 5)),
      W ≤ omegaOrbit T H ∧ Function.Surjective q ∧ q.ker = pCore 2 H ∧
        q.ker = centralizer ((omegaOrbit T H).subgroupOf H : Set H) ∧
        (pResidual 2 H).map q = alternatingGroup (Fin 5) ∧
        (∀ h : H, ∀ w : BinaryPermutation.core (Fin 5),
          h.val * e.flag.module.map (Multiplicative.ofAdd w) * h.val⁻¹ =
            e.flag.module.map (Multiplicative.ofAdd
              (BinaryPermutation.coreRepresentation (Fin 5) (q h) w))) ∧
        (V ≤ H.pCoreIn 2 ∨
          (Nat.card ((V.subgroupOf H).map q) = 4 ∧
            ¬ (V.subgroupOf H).map q ≤ alternatingGroup (Fin 5))) ∧
        (V.subgroupOf H ≤ pResidual 2 H → V ≤ H.pCoreIn 2) := by
  obtain ⟨W,W₁,W₂,W₃,e,q,hW,hq,hk,hU,hr,he⟩ :=
    original_nonsolvable_marked_action d hc hmany h1332 hcontexts hH hZ hs
  have hVH : V ≤ H := d.chosen.le_sylow.trans hH.1.1.2
  have hWH : W ≤ H := e.chosen.le_sylow.trans hH.1.1.2
  have hjoin : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change (pResidual 2 H).map H.subtype ⊔
      ((T : Subgroup G).subgroupOf H).map H.subtype = H at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hC := (e.local_centralizers e.normalizes_L).1
  rw [hjoin] at hC
  have hkW : q.ker = centralizer (W.subgroupOf H : Set H) := by
    rw [hk]
    apply map_injective H.subtype_injective
    change H.pCoreIn 2 = _
    rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hWH]
    exact hC.symm
  have halternative : V ≤ H.pCoreIn 2 ∨
      (Nat.card ((V.subgroupOf H).map q) = 4 ∧
        ¬ (V.subgroupOf H).map q ≤ alternatingGroup (Fin 5)) := by
    by_cases hm : V ≤ centralizer (W : Set G)
    · exact Or.inl ((le_inf hVH hm).trans hC.le)
    · exact Or.inr (d.cross_action_outer_four e hVH hWH q hkW he hm)
  refine ⟨W,W₁,W₂,W₃,e,q,hW,hq,hk,hU,hr,he,halternative,?_⟩
  intro hVR
  rcases halternative with hc | hc
  · exact hc
  · exact (hc.2 ((map_mono hVR).trans_eq hr)).elim

/-- Every original rechoice supplies both actual contexts before comparison.
The multiple-overgroup hypothesis is transported to that same Sylow. -/
theorem universal_original_nonsolvable_cross_module
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : IsA5Counterexample G)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (S : Sylow 2 G) (I : Subgroup G) (standing : SourceHypothesis S I)
    (H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    ∃ (V V₁ V₂ V₃ : Subgroup G) (_ : Context S I V V₁ V₂ V₃)
      (W W₁ W₂ W₃ : Subgroup G)
      (e : Context S ((pResidual 2 H).map H.subtype) W W₁ W₂ W₃)
      (q : H →* Equiv.Perm (Fin 5)),
      W ≤ omegaOrbit S H ∧ Function.Surjective q ∧ q.ker = pCore 2 H ∧
        q.ker = centralizer ((omegaOrbit S H).subgroupOf H : Set H) ∧
        (pResidual 2 H).map q = alternatingGroup (Fin 5) ∧
        (∀ h : H, ∀ w : BinaryPermutation.core (Fin 5),
          h.val * e.flag.module.map (Multiplicative.ofAdd w) * h.val⁻¹ =
            e.flag.module.map (Multiplicative.ofAdd
              (BinaryPermutation.coreRepresentation (Fin 5) (q h) w))) ∧
        (V ≤ H.pCoreIn 2 ∨
          (Nat.card ((V.subgroupOf H).map q) = 4 ∧
            ¬ (V.subgroupOf H).map q ≤ alternatingGroup (Fin 5))) ∧
        (V.subgroupOf H ≤ pResidual 2 H → V ≤ H.pCoreIn 2) := by
  obtain ⟨V,V₁,V₂,V₃,⟨d⟩⟩ := hcontexts S I standing
  have hmanyS : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  exact ⟨V,V₁,V₂,V₃,d,
    original_nonsolvable_cross_module d hc hmanyS h1332 hcontexts hH hZ hs⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
