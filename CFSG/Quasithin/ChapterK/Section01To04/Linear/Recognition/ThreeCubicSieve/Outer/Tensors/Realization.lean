module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Model
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization.Paired
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization.Character
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization.Actors
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization.Words
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Estimate

/-!
# Assembly of the natural-containing SL₃ tensor exchange

Actor lifting and selection, together with the paired component coordinates,
produce the literal exchange realization on the original Schur scalar extension.
The proved exchange estimate then applies to the original actor's common fixed
space, including the size-three and rank-at-most-two endpoints.

The automorphism and word-geometric inputs remain explicit. The central-kernel
hypothesis discharges both inputs in `natural_swap_models` below.
Source: GM, Classification of 2F-modules II, Proposition 4.8 steps 2–5,
manuscript pp.26–28; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

public section
noncomputable section
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization

variable {B : BinaryField} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) SL(3,B.Carrier) V} [IsIrreducible σ]

/-- Operator comparison assembles the two independent geometric producers. -/
theorem naturalSwapModels_of_lifts_and_coordinates
    (hl : LiftedOuterActors B σ) (hp : NaturalPairedCoordinates B σ) :
    NaturalSwapModels B σ := by
  intro M hn hsmall A hA _ _ ho hs
  obtain ⟨t, ht, L, hc⟩ := hl A hA ho
  obtain ⟨P⟩ := hp M hn hsmall t.val ht (hs _ t.property) L
  exact ⟨swapRealization_of_pairedCoordinates hs t L P hc⟩

/-- The actor and word constructions give the exchange model for every
natural-containing repeated word. -/
theorem natural_swap_models (hk : σ.ker ≤ Subgroup.center SL(3,B.Carrier)) :
    NaturalSwapModels B σ :=
  naturalSwapModels_of_lifts_and_coordinates
    (lifted_outer_actors B σ hk) (natural_paired_coordinates B σ hk)

/-- Application to the literal common fixed space. The natural factor excludes
the separate single-adjoint branch; all numerical estimates are already proved. -/
theorem natural_estimate_of_lifts_and_coordinates
    (hl : LiftedOuterActors B σ) (hp : NaturalPairedCoordinates B σ)
    (M : RepeatedModel B σ) (hn : 0 < naturalCount M.block) (hsmall : ¬ M.Small)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hc : IsCubic (normalizerRepresentation σ) A) (hr : rank A ≤ 2 * B.degree)
    (ho : ¬ A.map (linearNormalizer σ).subtype ≤ actionImage σ)
    (hs : ∀ t ∈ A, IsSchurLinear σ t) :
    2 * rank A < fixedCodim (normalizerRepresentation σ) A := by
  obtain ⟨R⟩ := naturalSwapModels_of_lifts_and_coordinates hl hp M hn hsmall A hA hc hr ho hs
  exact R.estimate M (by omega) hsmall (fun h => (by omega : naturalCount M.block ≠ 0) h.1) hr

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization
