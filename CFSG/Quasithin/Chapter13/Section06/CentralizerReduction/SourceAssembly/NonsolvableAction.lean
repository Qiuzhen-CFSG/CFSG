module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NonsolvableAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableGeneration

/-!
# The marked nonsolvable obstruction after every original rechoice

The original earlier Context constructor applies to the very same embedded
O²(H), retaining its faithful placement, uniform A5 hypothesis and all
ambient exclusions. Independent Baumann control then gives the S5 action
on H constructed in OriginalCentralization/NonsolvableAction. Its chosen
natural module lies inside the whole original omega orbit, and both
centralizer and two-core kernels are retained under one actor marking.

Transporting the multiple-overgroup guard through Sylow conjugacy applies
this construction after every original S,I rechoice. The preceding 5.2.3
reduction forces parameter one in a putative catalogue counterexample.
Every elementary subgroup of the actual residual then has image at most
two under this very S5 action. An elementary lift with image four, or an
ambient exclusion of this remaining case, is still required; the marked
natural module itself lies in the kernel and is not such a lift.

Earlier Context, 13.3.2 and 5.2.3 retain their original producers. This does
not assert unconditional 13.2.7, 13.6.7 or nonsingular-centralizer containment.
Source: Aschbacher--Smith 13.2.8(1), printed p.880, and the terminal
13.6.7 application, pp.928--934.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open ComponentSelection ComponentElimination.SourceContainment.RankTwo.LocalApplication
open Section05.A5Source Section02.A5Outside
open TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original earlier constructor applies to the very same embedded
residual; its full standing hypotheses and uniform A5 clause are retained. -/
theorem original_nonsolvable_residual_context
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃) (hc : IsA5Counterexample G)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    ∃ W W₁ W₂ W₃ : Subgroup G,
      Nonempty (Context T ((pResidual 2 H).map H.subtype) W W₁ W₂ W₃) := by
  have hf := (OriginalCentralization.nonsolvable_residual_faithful_A5 d
    (normalizes_faithful_of_source1332 d h1332) hH hZ hs).1
  exact hcontexts T _ { standing d hc with
    local_component := hf
    a5 := d.uniform_A5 _ hf
    five_minimal := fun _ => d.uniform_A5 }

/-- The actual H action, the whole omega orbit, and the residual's marked
natural module are simultaneous outputs of the original earlier inputs. -/
theorem original_nonsolvable_marked_action
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
              (BinaryPermutation.coreRepresentation (Fin 5) (q h) w))) := by
  obtain ⟨W,W₁,W₂,W₃,⟨e⟩⟩ := original_nonsolvable_residual_context d hc h1332 hcontexts hH hZ hs
  obtain ⟨hW,q,hq,hk,hU,hr,he⟩ := OriginalCentralization.nonsolvable_residual_action d
    (normalizes_faithful_of_source1332 d h1332) hH
    (OriginalCentralization.baumann_normalizer_of_many d hmany) hZ hs e
  exact ⟨W,W₁,W₂,W₃,e,q,hW,hq,hk,hU,hr,he⟩

/-- After every original rechoice, the parameter-one obstruction occurs
inside this same marked S5 action, with the complete omega orbit retained. -/
theorem universal_original_low_parameter_marked_action
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
    (hs : ¬ Group.IsSolvable H) :
    ChapterE.generationParameter H = 1 ∧
      ∃ (W W₁ W₂ W₃ : Subgroup G)
        (e : Context S ((pResidual 2 H).map H.subtype) W W₁ W₂ W₃)
        (q : H →* Equiv.Perm (Fin 5)),
        W ≤ omegaOrbit S H ∧ Function.Surjective q ∧ q.ker = pCore 2 H ∧
          q.ker = centralizer ((omegaOrbit S H).subgroupOf H : Set H) ∧
          (pResidual 2 H).map q = alternatingGroup (Fin 5) ∧
          (∀ h : H, ∀ w : BinaryPermutation.core (Fin 5),
            h.val * e.flag.module.map (Multiplicative.ofAdd w) * h.val⁻¹ =
              e.flag.module.map (Multiplicative.ofAdd
                (BinaryPermutation.coreRepresentation (Fin 5) (q h) w))) ∧
          (∀ A : Subgroup H, IsElementaryAbelian 2 A → A ≤ pResidual 2 H →
            Nat.card (A.map q) ≤ 2) := by
  obtain ⟨W,W₁,W₂,W₃,⟨d⟩⟩ := hcontexts S I standing
  have hmanyS : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  obtain ⟨X,X₁,X₂,X₃,e,q,hX,hq,hk,hU,hr,he⟩ :=
    original_nonsolvable_marked_action d hc hmanyS h1332 hcontexts hH hZ hs
  obtain ⟨hn,hbound⟩ := universal_original_low_parameter_residual_images
    hno h1332 hcontexts h523 S I standing H hH hZ hs
  refine ⟨hn,X,X₁,X₂,X₃,e,q,hX,hq,hk,hU,hr,he,?_⟩
  intro A hA hAR
  let a : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5) :=
    QuotientGroup.liftEquiv (pCore 2 H) hq hk.symm
  have ha : a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H)) = q := by
    ext h
    rfl
  rw [←ha,←Subgroup.map_map,card_map_of_injective (f := a.toMonoidHom) a.injective]
  exact hbound A hA hAR

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
