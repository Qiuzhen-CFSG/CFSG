module

public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuFamily
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceIrreducible
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Consequences

/-!
# The partial non-Mathieu family sieve on the literal chosen module

The fixed-space theorem supplies TI under the original component normalizer.
The partial quotient sieve retains the unchanged orbit representation and
component. In the SL₃ branch the same cover and absolute tensor witness give
binary dimension 9n on the actual orbit subgroup, using its existing coordinate
isomorphism. No exponent restriction discards n = 1.

The remaining family exclusions and strict 3.1.8(2) bound belong to
`qt-d-1222-nonmathieu-source-family-sieve`; the completed family theorem will
feed `qt-d-1222-nonff-nonmathieu`. This module does not assert that final sieve.
Source: Aschbacher--Smith 3.1.8(2),3.2.9 and12.2.2, pp.576,582--583,795.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.NonMathieuAssembly
open ChapterK.Linear.Recognition ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal orbit is TI under the original component normalizer. -/
theorem sourceOrbit_ti_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (g : G) (hg : g ∈ normalizer (L : Set G)) :
    D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      D.sourceOrbit.map (MulAut.conj g).toMonoidHom = D.sourceOrbit := by
  have hc := (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1
  have ht := D.ti_of_centralizer_eq_bot h.toHypothesis1221
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hc g hg
  rwa [← hV]

/-- The tensor witness keeps the actual orbit subgroup dimension as well as
its original covering action. The positive Schur degree may equal one. -/
theorem sourceOrbit_tensor_of_linear
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {r : ℕ} (hr : 0 < r)
    (hq : ClassicalGroup.IsPSL (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ r)) :
    ∃ (B : ChapterB.QuasisimpleSource.BinaryField) (C : LinearCover B 3 D.orbitComponent),
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier)) ∧
        letI := inflated_irreducible D.orbitRepresentation C hs.irreducible
        let n := schurDegree (inflated D.orbitRepresentation C)
        0 < n ∧ B.degree = 2 * n ∧
          Module.finrank (ZMod 2) (Additive D.sourceOrbit) = 9 * n ∧
          HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n :=
  NonMathieuFamily.hermitian_of_linear_finrank hs hnon hr hq
    (Module.finrank (ZMod 2) (Additive D.sourceOrbit)) D.sourceOrbitCoordinates.finrank_eq

/-- The original chosen module gives the partial marked family sieve and
its actual TI hypothesis. The remaining families still require exclusion. -/
theorem sourceOrbit_family_reduction_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    (SourceFamilies hs ∨ NonMathieuFamily.RemainingModel D.orbitComponent) ∧
      ∀ g ∈ normalizer (L : Set G),
        D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom = ⊥ ∨
          D.sourceOrbit.map (MulAut.conj g).toMonoidHom = D.sourceOrbit :=
  ⟨NonMathieuFamily.families_or_remaining hs hnm hnon,
    D.sourceOrbit_ti_of_many h hmany hV hnon⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
