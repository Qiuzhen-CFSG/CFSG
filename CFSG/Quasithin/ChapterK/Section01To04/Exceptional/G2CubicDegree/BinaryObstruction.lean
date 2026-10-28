module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Inputs
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Degrees
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Intersection
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.CubicConjugateBound
public import Theory.SpecificGroups.G2Even.BinaryDerivedAutomorphismRank
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity

/-!
# The binary G₂ cubic fixed-space obstruction

The actual derived binary G₂ carrier has irreducible binary degrees 1, 6,
14 and 32, by its checked permutation filtration. Its faithful irreducible
linear normalizer has elementary two-rank at most three, by the genuine
PSU₃(3) comparison and automorphism-rank theorem.

Individual involution displacement bounds exclude actors of rank at most
two. For rank three, an involution supplement generating over the component
forces dim V ≤ 2 codim C_V(A). The degree gap then excludes codimension at
most six, including the adjoint common-fixed-space equality case.

The checked inner and outer inversion/displacement calculations and the
rank-three generation certificates discharge `InvolutionBounds` and
`RankThreeGeneration`. Thus `fixed_space_obstruction` has no extra model
premises. The final consumer extracts the actual cubic actor at ratio two
and derives the degree-at-most-eight input used by
`Exceptional.SourceAssembly.g2_binary_natural_of_normalizer_degree_bound`.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.3,
pp.10--11, cited by GM04 Lemma 8.5.
-/

public noncomputable section

namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction
open Subgroup Representation Representation.BinaryOffender

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Faithfulness identifies the actual action image, so the automorphism-rank
bound applies to the full linear normalizer, retaining all outer actors. -/
theorem binary_derived_normalizer_rank_le_three
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hf : Function.Injective σ) :
    primeRank 2 (linearNormalizer σ) ≤ 3 := by
  let e : Derived ≃* actionImage σ :=
    MonoidHom.ofInjective (fun _ _ h => hf (congrArg Units.val h))
  have himage : primeRank 2 (MulAut (actionImage σ)) ≤ 3 := by
    rw [Theory.GroupTheory.primeRank_equiv 2 (MulAut.congr e.symm)]
    exact Atlas.G2.binary_derived_automorphism_two_rank_le_three
  exact (primeRank_linearNormalizer_le σ inferInstance).trans himage

private theorem fixedCodim_zpowers_le_fixedCodim_actor
    (σ : Representation (ZMod 2) Derived V) {A : Subgroup (linearNormalizer σ)}
    {t : linearNormalizer σ} (ht : t ∈ A) :
    fixedCodim (normalizerRepresentation σ) (zpowers t) ≤
      fixedCodim (normalizerRepresentation σ) A := by
  have hle : fixedSpace (normalizerRepresentation σ) A ≤
      fixedSpace (normalizerRepresentation σ) (zpowers t) :=
    (normalizerRepresentation σ).invariants_comp_subtype_antitone (zpowers_le.mpr ht)
  have hdim := Submodule.finrank_mono hle
  have hA := fixedCodim_add_finrank (normalizerRepresentation σ) A
  have ht := fixedCodim_add_finrank (normalizerRepresentation σ) (zpowers t)
  omega

/-- The rank-three equality case is ruled out by actual generation and the
checked degree gap, with no assumed fixed-space exclusion. -/
theorem rank_three_fixedCodim_gt_six_of_generation
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hf : Function.Injective σ) (hd : 8 < Module.finrank (ZMod 2) V)
    (hgen : RankThreeGeneration σ) (A : Subgroup (linearNormalizer σ))
    (hA : IsElementaryTwo A) (hr : rank A = 3) :
    6 < fixedCodim (normalizerRepresentation σ) A := by
  let : IsSimpleGroup Derived := Atlas.G2.isSimple_commutator_binary
  obtain ⟨t, ht, hAt⟩ := hgen A hA hr
  have hdim := finrank_le_twice_fixedCodim_of_involution_supplement
    (normalizerRepresentation σ) A (normalizerActor σ)
    (fixedSpace_normalizerActor_eq_bot σ hf inferInstance) t ht hAt
  have hlarge := fourteen_le_binary_derived_degree σ hd
  omega

/-- Conditional GM binary obstruction. The premises are individual-involution
calculations and a group-generation witness, rather than the asserted bound. -/
theorem fixed_space_obstruction_of_model_inputs
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hf : Function.Injective σ) (hd : 8 < Module.finrank (ZMod 2) V)
    (bounds : InvolutionBounds σ) (hgen : RankThreeGeneration σ)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim (normalizerRepresentation σ) A := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  have hr : rank A ≤ 3 := rank_le_of_primeRank_le hA
    (binary_derived_normalizer_rank_le_three σ hf)
  by_cases hthree : rank A = 3
  · have := rank_three_fixedCodim_gt_six_of_generation σ hf hd hgen A hA hthree
    omega
  · obtain ⟨t, ht, htne⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
    have ht2 : t ^ 2 = 1 := by
      let : IsElementaryAbelian 2 A := hA.2
      exact elemPow_eq_one_of_isElementaryAbelian t ht
    have hcodim := fixedCodim_zpowers_le_fixedCodim_actor σ ht
    by_cases hinner : innerInvolution σ t
    · have := bounds.inner_fixedCodim_ge_five t htne ht2 hinner
      omega
    · have := bounds.outer_fixedCodim_ge_six t htne ht2 hinner
      omega

/-- Actual threshold-two consumer: extracting the cubic-ratio witness gives
the precise degree input to binary natural-module recognition. -/
theorem binary_degree_le_eight_of_model_inputs
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hf : Function.Injective σ)
    (bounds : 8 < Module.finrank (ZMod 2) V → InvolutionBounds σ)
    (hgen : RankThreeGeneration σ)
    (hc : cubicRatio (normalizerRepresentation σ) ≤ 2) :
    Module.finrank (ZMod 2) V ≤ 8 := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  by_contra! hd
  obtain ⟨A, hA, _, hcodim⟩ :=
    (cubicRatio_le_nat_iff (normalizerRepresentation σ) 2).mp hc
  exact (not_lt_of_ge hcodim)
    (fixed_space_obstruction_of_model_inputs σ hf hd (bounds hd) hgen A hA)

/-- The binary endpoint of GM I, Proposition 4.3: every elementary cubic actor
in the full linear normalizer violates the threshold-two offender inequality
above degree eight. The inner, outer and rank-three common-fixed-space cases
are all discharged on the actual derived G₂ carrier. -/
theorem fixed_space_obstruction
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hf : Function.Injective σ) (hd : 8 < Module.finrank (ZMod 2) V)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (_hcubic : IsCubic (normalizerRepresentation σ) A) :
    2 * rank A < fixedCodim (normalizerRepresentation σ) A :=
  fixed_space_obstruction_of_model_inputs σ hf hd
    (involutionBounds σ hf hd) (rankThreeGeneration σ hf) A hA

/-- The actual threshold-two cubic-ratio witness forces degree at most eight,
with every concrete model premise discharged. This is the numerical input to
the existing marked binary natural-module recognition theorem. -/
theorem binary_degree_le_eight
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hf : Function.Injective σ)
    (hc : cubicRatio (normalizerRepresentation σ) ≤ 2) :
    Module.finrank (ZMod 2) V ≤ 8 :=
  binary_degree_le_eight_of_model_inputs σ hf
    (involutionBounds σ hf) (rankThreeGeneration σ hf) hc

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction
