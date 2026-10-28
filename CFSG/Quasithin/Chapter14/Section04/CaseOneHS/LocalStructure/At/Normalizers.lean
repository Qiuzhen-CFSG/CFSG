module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.Geometry

/-!
# Original normalizer control and tilded kernel at G,T

The local structural theorem gives TI and the unique maximal two-local
normalizer. TI controls every nonzero normalized subspace, while the actual
natural L-action gives its centralizer kernel. Applying the Chapter12 local
kernel theorem then identifies the original action on U/V₁ with O₂(H).
The genuine known-simple uniqueness result is already supplied by the
ambient-local Chapter12 API; no universal uniqueness or structure premise
is manufactured here.

These are the normalization and action inputs used in the faithful-family
exclusion of 14.3.25. Source: Aschbacher--Smith 14.3.3(6), 14.3.7,
12.8.4(4) and 14.3.25, printed pp.991--992,851,1001.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.CaseOneSource
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
include d earlier hq chosen structural

/-- The full original normalizer and TI conclusions use the local structure. -/
theorem source_normalizers_at :
    (L.subgroupOf (normalizer (L : Set G))).Normal ∧
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
    IsMaximalTwoLocal (normalizer (L : Set G)) ∧
    {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} =
      {normalizer (L : Set G)} ∧
    (∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V) ∧
    normalizer (V : Set G) ≤ normalizer (L : Set G) ∧
    seedNormalizer (normalizer (L : Set G)) V = normalizer (V : Set G) := by
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  have hm := h.maximal_unique_at structural
  have hn := h.seed_normalizer_le_at structural
  exact ⟨(normal_subgroupOf_iff_le_normalizer L.le_normalizer).mpr le_rfl,
    h.sylow_normalizes_at structural, hm.1, hm.2,
    ((structural L h.source).2.2 V chosen).2.2.1, hn, inf_eq_right.mpr hn⟩

/-- Original 14.3.3(6) for an arbitrary normalized nonzero seed subspace. -/
theorem intersection_normalizer_at (A J : Subgroup G) (hA : A ≠ ⊥) (hAV : A ≤ V)
    (hJ : J ≤ normalizer (A : Set G)) :
    J ⊓ normalizer (L : Set G) = J ⊓ normalizer (V : Set G) := by
  have hn := source_normalizers_at d earlier hq chosen structural
  exact inf_eq_inf_normalizer_of_trivial_intersections hn.2.2.2.2.1
    hn.2.2.2.2.2.1 hA hAV hJ

/-- Both literal centralizer kernels and the full L-action. -/
theorem source_actions_at :
    L ⊓ centralizer (V : Set G) = L.pCoreIn 2 ∧
    (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
    ∀ a : MulAut V, ∃ l ∈ L, ∀ v : V, l * (v : G) * l⁻¹ = (a v : G) := by
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  exact ⟨h.centralizer_L, h.centralizer_LT_at structural, h.full_L_action⟩

/-- The actual tilded kernel is O₂(H), using escape only at this G,T. -/
theorem source_action_kernel_at (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) :
    letI := chosen.elementary
    (F.localTildeAction F.H le_rfl).ker = pCore 2 F.H := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  exact F.localKernel_eq_pCore d.qtke L (normalizer (L : Set G)) F.H
    (by decide) chosen.le_sylow chosen.normalizes (h.sylow_normalizes_at structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) rfl
    (h.maximal_unique_at structural).2
    ((Subgroup.centralizer_le_normalizer _).trans (h.seed_normalizer_le_at structural))
    h.centralizer_L (h.point_mem_Hz_at F alternatives)

end CFSG.Quasithin.Chapter14.Section03.CaseOneSource
