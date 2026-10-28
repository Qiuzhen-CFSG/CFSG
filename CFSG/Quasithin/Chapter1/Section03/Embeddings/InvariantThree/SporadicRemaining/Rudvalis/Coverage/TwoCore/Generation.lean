module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Covers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.DoubleCosetCover
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.RepresentativeChecks
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.Words

/-!
# Rudvalis generator recovery from concrete word certificates

The intrinsic Sylow subgroup `Generation.fixedSylow` has ambient image equal
to the fourteen-generator subgroup already certified in `SylowCertificate`.
For this fixed subgroup, a double-coset cover reduces generation to one
check per representative. A representative either normalizes the intrinsic
max4 two-core, normalizes the Sylow center, or recovers both standard ATLAS
generators by explicit words in itself and the fixed Sylow generators.

The 847 published representatives exhaust the actual model, and every
normalization-or-recovery check is proved. Combining these results gives
`rudvalis_generatorRecovery` without additional hypotheses. The maximal
two-core and source sporadic exclusions are assembled by the consumers.

Source: Aschbacher--Smith, printed p.511 (PDF p.528), citing Aschbacher,
*Overgroups of Sylow subgroups in sporadic groups* (1986), no.343. The
intrinsic core and center are exactly those of `TwoCore.Definitions`.
-/

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining

open Subgroup Rudvalis Rudvalis.SylowOvergroups
open Rudvalis.SylowOvergroups.TwoCore
open Rudvalis.SylowOvergroups.TwoCore.Generation
open Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate
open Theory.GroupTheory.SubgroupEnumeration

/-- An exhaustive double-coset cover and checked words suffice for the
exact shared generator-recovery obligation. -/
public theorem rudvalis_generatorRecovery_of_doubleCoset_words
    {ι : Type*} (r : ι → Model)
    (hcover : DoubleCosetCover candidate r)
    (hstep : ∀ i, r i ∈ normalizer (coreImage : Set Model) ∨
      r i ∈ normalizer (centerImage fixedSylow : Set Model) ∨
      ∃ wa wb : List (Fin 30), extensionWord (r i) wa = a ∧ extensionWord (r i) wb = b) :
    GeneratorRecovery := by
  refine ⟨fixedSylow, ?_⟩
  rw [sylowImage_fixedSylow]
  apply generation_outside_two_normalizers_of_doubleCosetCover candidate
    coreImage (centerImage fixedSylow)
    (sylowImage_fixedSylow ▸ sylowImage_le_normalizer_coreImage fixedSylow)
    (sylowImage_fixedSylow ▸ sylowImage_le_normalizer_centerImage fixedSylow)
    r hcover
  intro i
  rcases hstep i with h | h | ⟨wa, wb, ha, hb⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (generation_of_words _ wa wb ha hb))

/-- For the fixed intrinsic Sylow subgroup of max4, adjoining any element
outside the normalizers of the intrinsic max4 two-core image and the Sylow
center generates the entire degree-4060 Rudvalis model. -/
public theorem rudvalis_generatorRecovery : GeneratorRecovery :=
  rudvalis_generatorRecovery_of_doubleCoset_words
    Generation.Representatives.representative
    Generation.DoubleCosetCover.doubleCosetCover
    Generation.RepresentativeChecks.all_representatives

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining
