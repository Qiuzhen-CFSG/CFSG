module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.DegreeGap
public import Theory.Representation.BinaryOffender.NormalizerRank
public import Theory.Representation.BinaryOffender.SchurNormalizerDisplacement
public import Theory.Representation.BinaryOffender.CubicConjugateBound

/-!
# Schur descent reduction for the G₂ cubic tensor window

The explicit automorphism two-rank bound controls the rank of the actual
linear-normalizer actor. Every one of its involutions therefore moves at
most `6*r` binary dimensions. A nontrivial action on the Schur field forces
degree at most `12*r`. Consequently a putative degree at least `18*r` makes
the entire actor linear over the actual Schur field.

The source cardinality argument, still an explicit input, gives degree below
`34*r`. The proved Frobenius degree gap then leaves only degree `18*r`, the
natural tensor over a field of half the defining degree. Its remaining
Schur-linear involution estimate is displacement at least `5/12` of the
module; this includes both inner actors and outer factor swaps.

The final theorem assembles these two explicit estimates into the literal
`hwindow` premise of `G2CubicDegree.degree_lt_of_cubic_estimates`. They remain
unproved here, so this is not yet the unconditional tensor window. The rank
input remains explicitly supplied by the parent. Cubicity is retained at its
actual threshold two; these reductions only need the codimension inequality.

Source: Guralnick–Malle, Classification of 2F-modules II, §3.5 equations
(3.3)–(3.5), manuscript p.20, and Lemma 8.5, pp.55–56; used in
Aschbacher–Smith K.3, printed p.457. See `G2CubicDegree/Source.md`.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open Subgroup Theory.GroupTheory

variable {F V : Type*} [Field F] [Finite F]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) (Atlas.G2.Model F) V) [IsIrreducible σ]

/-- Schur's lemma transfers the explicit automorphism bound to the literal normalizer. -/
theorem normalizer_rank_le {r : ℕ} (hf : Function.Injective σ)
    (hAut : primeRank 2 (MulAut (Atlas.G2.Model F)) ≤ 3 * r) :
    primeRank 2 (linearNormalizer σ) ≤ 3 * r := by
  have hfaith : Function.Injective σ.asGroupHom := by
    intro g h he
    exact hf (congrArg Units.val he)
  let e : Atlas.G2.Model F ≃* actionImage σ := MonoidHom.ofInjective hfaith
  have hb := primeRank_linearNormalizer_le σ inferInstance
  rw [← primeRank_equiv 2 (MulAut.congr e)] at hb
  exact hb.trans hAut

/-- Every element of the given threshold-two actor has displacement at most `6*r`. -/
theorem actor_displacement_le {r : ℕ} (hf : Function.Injective σ)
    (hAut : primeRank 2 (MulAut (Atlas.G2.Model F)) ≤ 3 * r)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A)
    (t : linearNormalizer σ) (ht : t ∈ A) :
    t ^ 2 = 1 ∧ fixedCodim (normalizerRepresentation σ) (zpowers t) ≤ 6 * r := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  obtain ⟨ht2, hd⟩ := involution_fixedCodim_le_of_mem_small_actor
    (normalizerRepresentation σ) hA (normalizer_rank_le σ hf hAut) hsmall ht
  exact ⟨ht2, by omega⟩

/-- A nontrivial Schur-field action already gives the stronger degree bound `12*r`. -/
theorem degree_le_twelve_of_not_schurLinear {r : ℕ} (hf : Function.Injective σ)
    (hAut : primeRank 2 (MulAut (Atlas.G2.Model F)) ≤ 3 * r)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A)
    (t : linearNormalizer σ) (ht : t ∈ A) (hs : ¬ IsSchurLinear σ t) :
    Module.finrank (ZMod 2) V ≤ 12 * r := by
  have hd := (actor_displacement_le σ hf hAut A hA hsmall t ht).2
  have hb := finrank_le_twice_fixedCodim σ t hs
  omega

/-- At or above the disputed threshold, every element of the actor is Schur-linear. -/
theorem large_actor_isSchurLinear {r : ℕ} (hr : 0 < r) (hf : Function.Injective σ)
    (hAut : primeRank 2 (MulAut (Atlas.G2.Model F)) ≤ 3 * r)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A)
    (hlarge : 18 * r ≤ Module.finrank (ZMod 2) V) :
    ∀ t ∈ A, IsSchurLinear σ t := by
  intro t ht
  by_contra hs
  have hd := degree_le_twelve_of_not_schurLinear σ hf hAut A hA hsmall t ht hs
  omega

/-- The coarse cardinality bound and the single remaining tensor calculation
supply the exact source consumer's `hwindow` input. -/
theorem window_of_coarse_and_half_tensor_estimates [CharP F 2]
    {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (hf : Function.Injective σ)
    (hAut : primeRank 2 (MulAut (Atlas.G2.Model F)) ≤ 3 * r)
    (hcoarse : ∀ A : Subgroup (linearNormalizer σ), IsElementaryTwo A →
      fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A →
        Module.finrank (ZMod 2) V < 34 * r)
    (hhalf : Module.finrank (ZMod 2) V = 18 * r →
      ∀ t : linearNormalizer σ, t ≠ 1 → t ^ 2 = 1 → IsSchurLinear σ t →
        5 * Module.finrank (ZMod 2) V ≤
          12 * fixedCodim (normalizerRepresentation σ) (zpowers t)) :
    ∀ A : Subgroup (linearNormalizer σ),
      IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A →
      fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A →
      Module.finrank (ZMod 2) V < 18 * r := by
  intro A hA _ hsmall
  by_contra! hlarge
  have hdegree := degree_eq_eighteen_of_large_lt_thirtyFour σ hr hF hf hlarge
    (hcoarse A hA hsmall)
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  obtain ⟨ht2, hd⟩ := actor_displacement_le σ hf hAut A hA hsmall t ht
  have hs := large_actor_isSchurLinear σ (by omega) hf hAut A hA hsmall hlarge t ht
  have he := hhalf hdegree t ht1 ht2 hs
  omega

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow
