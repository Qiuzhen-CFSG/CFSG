module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalPairSourceComplete
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NonsolvableAction
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.Baumann

/-!
# Proved normalization in the original nonsolvable A5 source

Every faithful component in the actual Context has its original A5 quotient
mark. The genuine tensor exclusion therefore normalizes every such component
and chooses its actual module. In the nonsolvable outside branch this proves
the faithful residual, maximal placement and whole omega-action kernel with
no universal normalization input. The original earlier A5 module clause then
constructs the residual Context and the marked action on H itself.

The module classification remains an explicit earlier source duty. No
generation-parameter bound or nonsingular-centralizer conclusion is inferred
from the quotient action alone.
Source: Aschbacher--Smith 13.2.8(1),13.3.2, pp.880,884--885.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section02.A5Outside
open Section03.A5Setup Section03.A5Setup.OriginalMaximality
open Section03.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)

include d

/-- Normalization and actual module choice on every faithful component of
the same original Context. Only its genuine multiple-overgroup guard is used. -/
theorem original_faithful_normalization_from_source
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
        ∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T K W) := by
  intro K hK
  obtain ⟨e⟩ := d.uniform_A5 K hK
  exact original_a5_normalizes_from_source_of_many
    { d.hypothesis with local_component := hK
                        five_minimal := fun _ => d.uniform_A5 } e hmany

/-- The original nonsolvable residual and its full omega-action kernel need
no separately supplied normalization theorem. -/
theorem original_nonsolvable_structure_from_source
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    (pResidual 2 H).map H.subtype ∈ MainForward.faithfulLocalComponents T ∧
      (pResidual 2 H).map H.subtype ∈ Chapter1.LStar G (T : Subgroup G) ∧
      Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃*
        alternatingGroup (Fin 5)) ∧
      centralizer ((omegaOrbit T H).subgroupOf H : Set H) = pCore 2 H := by
  have hn := fun K hK => (original_faithful_normalization_from_source d hmany K hK).1
  obtain ⟨hf,hq⟩ := OriginalCentralization.nonsolvable_residual_faithful_A5 d hn hH hZ hs
  exact ⟨hf,OriginalCentralization.nonsolvable_residual_mem_LStar d hn hH hZ hs,hq,
    OriginalCentralization.nonsolvable_omega_centralizer_eq_twoCore d hn hH hZ hs⟩

/-- The earlier original module clause, applied at the original Context,
constructs the actual residual Context without an external Context producer. -/
theorem original_nonsolvable_context_from_modules
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : OriginalAlternatingFiveModules1332At T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    ∃ W W₁ W₂ W₃ : Subgroup G, W₂ ≤ W₃ ∧
      Nonempty (Context T ((pResidual 2 H).map H.subtype) W W₁ W₂ W₃) := by
  have hf := (original_nonsolvable_structure_from_source d hmany hH hZ hs).1
  obtain ⟨_,W,⟨D⟩⟩ := original_faithful_normalization_from_source d hmany _ hf
  have hm := hmodules d.hypothesis _ hf (d.uniform_A5 _ hf) W D
  obtain ⟨W₁,W₂,W₃,h23,he⟩ := exists_context_of_one_or_two_modules
    { d.hypothesis with local_component := hf
                        five_minimal := fun _ => d.uniform_A5 } D (Or.inl hm)
  exact ⟨W,W₁,W₂,W₃,h23,he⟩

/-- The same earlier module clause supplies the literal marked S5 action,
with the actual residual and both whole omega/two-core kernels retained. -/
theorem original_nonsolvable_action_from_modules
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : OriginalAlternatingFiveModules1332At T L)
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
  obtain ⟨W,W₁,W₂,W₃,_,⟨e⟩⟩ :=
    original_nonsolvable_context_from_modules d hmany hmodules hH hZ hs
  have hn := fun K hK => (original_faithful_normalization_from_source d hmany K hK).1
  obtain ⟨hW,q,hq,hk,hU,hr,he⟩ := OriginalCentralization.nonsolvable_residual_action d
    hn hH (OriginalCentralization.baumann_normalizer_of_many d hmany) hZ hs e
  exact ⟨W,W₁,W₂,W₃,e,q,hW,hq,hk,hU,hr,he⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
