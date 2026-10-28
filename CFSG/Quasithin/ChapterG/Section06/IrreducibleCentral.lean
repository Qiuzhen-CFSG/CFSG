module
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.Complete

/-!
# The irreducible central-involution application of G.6.4

A nonidentity actor in a faithful irreducible binary representation has a
nonzero displacement span. Its orbit span is an invariant subspace, hence
the whole module. This verifies the generation clause of the original G.6.1
hypotheses on the given representation and quotient map. G.6.4(4) then
forces the normal closure of a Sylow-central rank-one involution to be the
entire group.

Source: Aschbacher--Smith G.6.1 and G.6.4(4), printed pp.345--346;
application to the partner chief action in 15.2.27(2), printed p.1119.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06
universe u v
variable {G Cover : Type u} {V : Type v} [Group G] [Finite G]
  [Group Cover] [Finite Cover] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Irreducibility supplies the actual orbit-span generation in G.6.1. -/
theorem hypotheses_of_irreducible
    (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
    (q : Cover →* G) (hsq : IsSQTK KnownSimple.IsKnownSimple Cover)
    (hq : Function.Surjective q) (hcore : pCore 2 G = ⊥)
    (hf : Function.Injective ρ) (a : G) (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) ≤ 2) :
    Hypotheses KnownSimple.IsKnownSimple ρ a q := by
  refine ⟨inferInstance,inferInstance,inferInstance,hsq,hq,hcore,hf,ha,hne,hr,?_⟩
  let K := normalClosure ({a} : Set G)
  let W := subspaceCommutator ρ ⊤ K
  have hstable : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ W :=
    subspaceCommutator_invariant_normalizer ρ (le_subspaceStabilizer ρ ⊤ (by simp))
      le_normalizer_of_normal
  let U : Subrepresentation ρ := ⟨W, fun g v hv => (hstable (mem_top g) v).2 hv⟩
  have hu : U ≠ ⊥ := by
    intro he
    have hW : W = ⊥ := congrArg Subrepresentation.toSubmodule he
    apply hne
    apply hf
    apply LinearMap.ext
    intro v
    have hm : ρ a v - v ∈ W := Submodule.subset_span
      ⟨a,subset_normalClosure (Set.mem_singleton a),v,Submodule.mem_top,rfl⟩
    have hz : ρ a v-v=0 := by simpa only [hW,Submodule.mem_bot] using hm
    simpa only [map_one,Module.End.one_apply] using sub_eq_zero.mp hz
  have ht := (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hu
  have hw : W = ⊤ := congrArg Subrepresentation.toSubmodule ht
  rw [← commutator_conjugateSpanBy_zpowers,conjugateSpanBy_zpowers_top]
  exact hw

/-- A central rank-one involution normally generates the original quotient actor. -/
theorem normalClosure_eq_top_of_irreducible_central_rank_one
    (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
    (q : Cover →* G) (hsq : IsSQTK KnownSimple.IsKnownSimple Cover)
    (hq : Function.Surjective q) (hcore : pCore 2 G = ⊥)
    (hf : Function.Injective ρ) (a : G) (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) = 1)
    (S : Sylow 2 G) (haS : a ∈ S) (hc : ∀ s ∈ S, Commute a s) :
    normalClosure ({a} : Set G) = ⊤ := by
  have h := hypotheses_of_irreducible ρ q hsq hq hcore hf a ha hne (by omega)
  apply ((lemma_G_6_4 h hr).2 S ?_).1
  refine ⟨⟨a,haS⟩,?_,rfl⟩
  apply mem_center_iff.mpr
  intro s
  exact Subtype.ext (hc s s.property).eq.symm
end CFSG.Quasithin.ChapterG.Section06
