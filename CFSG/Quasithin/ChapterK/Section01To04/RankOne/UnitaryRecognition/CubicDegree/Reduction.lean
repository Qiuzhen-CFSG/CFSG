module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.Preparation
public import Theory.Representation.SU3.CubicDegree.SchurReduction

/-!
# The source actor over its Schur field

Inflation along the specified central SU₃ cover has exactly the covering
kernel. The original cubic bound supplies an actual actor in the full
normalizer of that inflated action. If an actor moves the Schur field,
the bound dim V ≤ 4(s+1), together with the lower bound 6s ≤ dim V,
forces s=2 and dim V=12. This proves the requested upper bound in that branch.

The remaining actor is linear over the Schur field. Both its inner and
outer possibilities remain to be proved; the final disjunction records
this obligation and does not assert the complete degree bound of K.3.3.

Source: Aschbacher--Smith K.3.3, printed p.456, under the standing
hypotheses on p.451; Guralnick--Malle II, Theorem 4.10, Proposition 4.11,
and Table 7, internal pp.29--32.
-/

public section
open BenderSuzuki.MatrixGroups Representation Representation.BinaryOffender
open Subgroup
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree
variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (J : HermitianForm 3 F) {s : ℕ} (hs : 2 ≤ s)
  (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
variable {G : Type*} [Group G] [Finite G]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  (h : SourceHypotheses ρ L) (π : J.specialSubgroup →* L)
  (hπ : Function.Surjective π)
  (hker : π.ker ≤ center J.specialSubgroup)

include hs hcard hconj h hπ hker

omit hs hcard hconj hπ hker [Finite F] [FiniteDimensional (ZMod 2) V] [Finite G] in
/-- Inflation introduces exactly the specified covering kernel. -/
theorem pullback_ker_eq : ((ρ.comp L.subtype).comp π).ker = π.ker := by
  ext g
  change ρ (π g : G) = 1 ↔ π g = 1
  constructor
  · intro hg
    apply Subtype.ext
    apply h.faithful
    simpa only [Subgroup.coe_one, map_one] using hg
  · intro hg
    simp only [hg, Subgroup.coe_one, map_one]

omit [Finite G] in
/-- Any source actor which moves the Schur field already gives the required
upper degree bound. Cubicity is unnecessary for this particular branch. -/
theorem source_degree_le_of_not_schurLinear
    (A : Subgroup (linearNormalizer ((ρ.comp L.subtype).comp π)))
    (hA : IsElementaryTwo A)
    (hc : fixedCodim (normalizerRepresentation ((ρ.comp L.subtype).comp π)) A ≤
      2 * rank A)
    (t : linearNormalizer ((ρ.comp L.subtype).comp π)) (ht : t ∈ A)
    (hnl : ¬ SchurNormalizer.IsSchurLinear ((ρ.comp L.subtype).comp π) t) :
    Module.finrank (ZMod 2) V ≤ 6 * s := by
  have hk' : ((ρ.comp L.subtype).comp π).ker ≤ center J.specialSubgroup := by
    rw [pullback_ker_eq J h π]
    exact hker
  have hd := Representation.SU3.CubicDegree.finrank_le_four_mul_of_not_schurLinear J hs hcard hconj
    ((ρ.comp L.subtype).comp π) (pullback_irreducible J h π hπ) hk' A hA hc t ht hnl
  omega

omit [Finite G] in
/-- The small-field endpoint is explicit: the same branch can occur only
at `s = 2`, where the source degree is exactly twelve. -/
theorem source_not_schurLinear_forces_two
    (A : Subgroup (linearNormalizer ((ρ.comp L.subtype).comp π)))
    (hA : IsElementaryTwo A)
    (hc : fixedCodim (normalizerRepresentation ((ρ.comp L.subtype).comp π)) A ≤
      2 * rank A)
    (t : linearNormalizer ((ρ.comp L.subtype).comp π)) (ht : t ∈ A)
    (hnl : ¬ SchurNormalizer.IsSchurLinear ((ρ.comp L.subtype).comp π) t) :
    s = 2 ∧ Module.finrank (ZMod 2) V = 12 := by
  have hk' : ((ρ.comp L.subtype).comp π).ker ≤ center J.specialSubgroup := by
    rw [pullback_ker_eq J h π]
    exact hker
  have hu := Representation.SU3.CubicDegree.finrank_le_four_mul_of_not_schurLinear J hs hcard hconj
    ((ρ.comp L.subtype).comp π) (pullback_irreducible J h π hπ) hk' A hA hc t ht hnl
  have hl := source_degree_lower J h π hπ hs hcard hconj
  omega

/-- An actual source actor either proves the degree bound, or acts linearly
over the Schur field. Both inner and outer actors remain in the second branch;
no assertion about the generalized Fitting subgroup of the normalizer is used. -/
theorem source_degree_le_or_schurLinear_actor :
    Module.finrank (ZMod 2) V ≤ 6 * s ∨
      ∃ A : Subgroup (linearNormalizer ((ρ.comp L.subtype).comp π)),
        IsElementaryTwo A ∧
        IsCubic (normalizerRepresentation ((ρ.comp L.subtype).comp π)) A ∧
        fixedCodim (normalizerRepresentation ((ρ.comp L.subtype).comp π)) A ≤
          2 * rank A ∧
        ∀ t ∈ A, SchurNormalizer.IsSchurLinear ((ρ.comp L.subtype).comp π) t := by
  classical
  let σ := (ρ.comp L.subtype).comp π
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  obtain ⟨A, hA, hc, hd⟩ := (cubicRatio_le_nat_iff (normalizerRepresentation σ) 2).mp
    (pullback_normalizer_cubic_le_two J h π hπ)
  by_cases hl : ∀ t ∈ A, SchurNormalizer.IsSchurLinear σ t
  · exact Or.inr ⟨A, hA, hc, hd, hl⟩
  · push Not at hl
    obtain ⟨t, ht, hnl⟩ := hl
    exact Or.inl (source_degree_le_of_not_schurLinear J hs hcard hconj h π hπ hker
      A hA hd t ht hnl)
end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree
