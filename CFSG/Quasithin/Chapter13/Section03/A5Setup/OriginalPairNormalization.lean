module

public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OriginalDGSAssembly
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalNormalization
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.Source
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.EarlierModules

/-!
# Original A₅ normalization and context after the mixed DGS bound

The tensor argument now retains only genuine A₅/A₅ pair containment. The
original Chapter 10 normalization theorem selects a chosen module at the
same G,T,L. The earlier A₅ module clause then constructs its invariant flag
and Context. No size, Cartan, symplectic-plane or tensor-exclusion callback
is requested. Pair containment and the original module clause remain genuine
source obligations; nonsingular-centralizer control is separate.
Source: Aschbacher--Smith 10.2.13,13.3.2, pp.755,884--885.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter10 Chapter10.SourceA5TensorModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Normalization and the actual chosen module from the original pair source. -/
theorem original_a5_normalizes_of_pair_containment_of_many
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcontain : A5PairContainment G) :
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      ∃ V : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T L V) :=
  original_a5_normalizes_after_tensor_exclusion_of_many h e hmany
    (fun D hD hn => sourceA5TensorExclusionAt_of_pair_containment hcontain T L D e hD hmany hn)

/-- Construct the same original Context after normalization; the natural
module marking is retained as its genuine earlier 13.3.2 source duty. -/
theorem exists_context_of_pair_containment_and_original_modules
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcontain : A5PairContainment G)
    (hmodules : SourceCompletion.OriginalAlternatingFiveModules1332At T L) :
    ∃ V V₁ V₂ V₃ : Subgroup G, V₂ ≤ V₃ ∧
      Nonempty (Section05.A5Source.Context T L V V₁ V₂ V₃) := by
  obtain ⟨_,V,⟨D⟩⟩ := original_a5_normalizes_of_pair_containment_of_many h e hmany hcontain
  have hmodel := hmodules h L h.local_component ⟨e⟩ V D
  obtain ⟨V₁,V₂,V₃,h23,hd⟩ := exists_context_of_one_or_two_modules h D (Or.inl hmodel)
  exact ⟨V,V₁,V₂,V₃,h23,hd⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
