module

public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.SpecificGroups.BinaryLinear.CubicPairNormalizers.FlagCore
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.FourComponent.Flags
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.FiveFlags
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource.PairNormalizers.CoreAbsorption

/-!
# Normalizers of the full two-node parabolic residuals

The degree-four endpoint parabolic is the stabilizer of the marked
two-space. Its two-core is the actual elementary radical, whose normalizer
is that stabilizer. A nonadjacent pair in degree five leaves exactly two
cuts. The two-core of their common stabilizer recovers both spaces through
fixed vectors and displacements, so it too has precisely the parabolic as
normalizer. These equalities hold for every actual supplied basis.

The full O² residual absorbs O₂(P), by the cubic commutator and shear
calculations in `PairNormalizers.CoreAbsorption`. Relative normality then
identifies the residual's own two-core with O₂(P), so its normalizer also
equals P. The final unconditional statements retain the actual ambient
embeddings, covering the degree-four endpoints and all three nonadjacent
degree-five pairs in either order. The conditional reductions are retained
as separate interfaces.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.8.25, printed p.960 (PDF p.977), at L₁T = H ∩ M. This module concerns
the actual linear parabolics and imports no CoverSource umbrella.
-/

public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.SmallParabolicLevi BinaryLinear.CubicPairNormalizers
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

private theorem four_endpoints_eq (b : Basis 3) :
    fourParabolic b ({0,2} : Set (Fin 3)) = parabolic (cutSpace b 1) := by
  have h : ({0,2} : Set (Fin 3))ᶜ = {1} := by
    ext k
    fin_cases k <;> simp
  simp only [fourParabolic, h, cutStabilizer, Set.mem_singleton_iff, iInf_iInf_eq_left]

/-- The actual endpoint-pair parabolic has a self-normalizing embedded two-core. -/
theorem fourPair_twoCore_normalizer (b : Basis 3) :
    normalizer ((pCore 2 (fourParabolic b ({0,2} : Set (Fin 3)))).map
      (fourParabolic b ({0,2} : Set (Fin 3))).subtype : Set (LinearGroup 4)) =
        fourParabolic b ({0,2} : Set (Fin 3)) := by
  rw [four_endpoints_eq, map_twoCore_eq_radical]
  apply normalizer_radical
  intro he
  have hv := (basis_mem_cutSpace b 1 0).mpr (by decide)
  rw [he, Submodule.mem_bot] at hv
  exact b.ne_zero 0 hv

private theorem five_twoCut_core_normalizer (b : FiveBasis) (a c : Fin 4) (hac : a ≤ c) :
    normalizer ((flagStabilizer b {a,c}).pCoreIn 2 : Set (LinearGroup 5)) =
      flagStabilizer b {a,c} := by
  have he : flagStabilizer b {a,c} = parabolic (flagSpace b a) ⊓ parabolic (flagSpace b c) := by
    ext g
    simp [flagStabilizer, or_imp, forall_and]
  rw [he]
  apply normalizer_twoCore_nested
  · apply Submodule.span_mono
    exact Set.image_mono (fun _ hk => Nat.le_trans hk hac)
  · exact flagSpace_ne_bot b a
  · exact flagSpace_ne_top b c

/-- Both remaining cuts are recovered for every nonadjacent node pair in degree five. -/
theorem fivePair_twoCore_normalizer (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    normalizer ((pCore 2 (fiveParabolic b {i,j})).map
      (fiveParabolic b {i,j}).subtype : Set (LinearGroup 5)) = fiveParabolic b {i,j} := by
  have hc : ∀ i j : Fin 4, (i.val + 1 < j.val ∨ j.val + 1 < i.val) →
      ∃ a c : Fin 4, a ≤ c ∧ ∀ k : Fin 4, (k ≠ i ∧ k ≠ j) ↔ (k = a ∨ k = c) := by
    decide +kernel
  obtain ⟨a, c, hac, hk⟩ := hc i j h
  have he : ({i,j} : Set (Fin 4))ᶜ = {a,c} := by
    ext k
    simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hk k
  change normalizer ((flagStabilizer b {i,j}ᶜ).pCoreIn 2 : Set (LinearGroup 5)) =
    flagStabilizer b {i,j}ᶜ
  rw [he]
  exact five_twoCut_core_normalizer b a c hac

/-- Core absorption suffices for the degree-four endpoint residual normalizer.
The absorption premise is a separate concrete calculation. -/
theorem fourPair_residual_normalizer_of_twoCore_le (b : Basis 3)
    (hcore : (pCore 2 (fourParabolic b ({0,2} : Set (Fin 3)))).map
      (fourParabolic b ({0,2} : Set (Fin 3))).subtype ≤
        (pResidual 2 (fourParabolic b ({0,2} : Set (Fin 3)))).map
          (fourParabolic b ({0,2} : Set (Fin 3))).subtype) :
    normalizer ((pResidual 2 (fourParabolic b ({0,2} : Set (Fin 3)))).map
      (fourParabolic b ({0,2} : Set (Fin 3))).subtype : Set (LinearGroup 4)) =
        fourParabolic b ({0,2} : Set (Fin 3)) :=
  normalizer_embedded_pResidual_eq_of_core_le 2 _ hcore (fourPair_twoCore_normalizer b)

/-- Core absorption suffices for the full degree-five two-node residual normalizer.
The absorption premise is a separate concrete calculation. -/
theorem fivePair_residual_normalizer_of_twoCore_le (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val)
    (hcore : (pCore 2 (fiveParabolic b {i,j})).map (fiveParabolic b {i,j}).subtype ≤
      (pResidual 2 (fiveParabolic b {i,j})).map (fiveParabolic b {i,j}).subtype) :
    normalizer ((pResidual 2 (fiveParabolic b {i,j})).map
      (fiveParabolic b {i,j}).subtype : Set (LinearGroup 5)) = fiveParabolic b {i,j} :=
  normalizer_embedded_pResidual_eq_of_core_le 2 _ hcore (fivePair_twoCore_normalizer b i j h)

/-- The full two-residual of the degree-four endpoint parabolic has normalizer
exactly that parabolic, for every supplied basis. -/
theorem fourPair_residual_normalizer (b : Basis 3) :
    normalizer ((pResidual 2 (fourParabolic b ({0,2} : Set (Fin 3)))).map
      (fourParabolic b ({0,2} : Set (Fin 3))).subtype : Set (LinearGroup 4)) =
        fourParabolic b ({0,2} : Set (Fin 3)) :=
  fourPair_residual_normalizer_of_twoCore_le b (fourPair_twoCore_le_residual b)

/-- The degree-four calculation accepts either order of the nonadjacent nodes. -/
theorem fourPair_residual_normalizer_of_nonadjacent (b : Basis 3) (i j : Fin 3)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    normalizer ((pResidual 2 (fourParabolic b {i,j})).map
      (fourParabolic b {i,j}).subtype : Set (LinearGroup 4)) = fourParabolic b {i,j} := by
  have he : ({i,j} : Set (Fin 3)) = {0,2} := by
    have hc : (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) := by
      revert i j
      decide +kernel
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Set.pair_comm _ _
  rw [he]
  exact fourPair_residual_normalizer b

/-- The full two-residual of every nonadjacent degree-five two-node parabolic
has normalizer exactly that parabolic, in the actual ambient linear group. -/
theorem fivePair_residual_normalizer (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    normalizer ((pResidual 2 (fiveParabolic b {i,j})).map
      (fiveParabolic b {i,j}).subtype : Set (LinearGroup 5)) = fiveParabolic b {i,j} :=
  fivePair_residual_normalizer_of_twoCore_le b i j h (fivePair_twoCore_le_residual b i j h)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

end
