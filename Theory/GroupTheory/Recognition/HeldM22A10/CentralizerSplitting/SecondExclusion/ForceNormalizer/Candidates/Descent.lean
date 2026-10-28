module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Generators
public import Theory.GroupTheory.SubgroupEnumerationDescending

/-!
# Valid pruning conditions for the second Held subgroup census

Centricity and noncontainment in the transfer kernel are upward closed and
invariant under conjugation in the Sylow group. Thus exhaustive maximal
subgroup descent may discard any entry failing either condition. Intrinsic
radicality is not used to prune the descent.

The theorem here reduces coverage to the actual maximal subgroups of the
45 displayed representatives; that finite maximal-subgroup calculation
remains an explicit input. Source: the elementary finite subgroup-lattice
descent in `SubgroupEnumerationDescending`, applied to the proposed
Huppert--Blackburn III, XII.1.18(b) calculation.
-/

namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates
open Subgroup SubgroupEnumeration

/-- Eligibility for the census, independent of intrinsic radicality. -/
@[expose] public def Eligible (U : Subgroup Model.sylowSubgroup) : Prop :=
  centralizer (U : Set Model.sylowSubgroup) ≤ U ∧ ¬ U ≤ kernel

public theorem eligible_mono : Monotone Eligible := by
  intro U V hUV hU
  exact ⟨centralizer_le_of_le hUV hU.1, fun hV => hU.2 (hUV.trans hV)⟩

public theorem eligible_conjugate (U : Subgroup Model.sylowSubgroup)
    (g : Model.sylowSubgroup) (hU : Eligible U) :
    Eligible (U.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨centralizer_le_map U (MulAut.conj g) hU.1, ?_⟩
  intro hmap
  apply hU.2
  have hk : kernel.map (MulAut.conj g).toMonoidHom = kernel :=
    normal_iff_map_conj_eq.mp kernel_normal g
  rw [← hk] at hmap
  exact (map_le_map_iff_of_injective (MulAut.conj g).injective).mp hmap

/-- Exhausting every eligible maximal subgroup of each representative
suffices for coverage of all actual eligible subgroups. -/
public theorem coverage_of_maximal_descent
    (hstep : ∀ (i : Fin 45) (U : Subgroup Model.sylowSubgroup),
      U ⋖ representative i → Eligible U → Represented representative U) : Coverage := by
  intro U hc hk
  exact represented_of_maximal_descent representative Eligible eligible_mono
    eligible_conjugate ⟨44, representative_top⟩ hstep U ⟨hc, hk⟩

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates
