module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates

/-!
# Solvable FF structure and cyclic-three conjugates

This module assembles B.1.8(1)–(4), the first assertion of B.1.8(5), and
B.1.12 from their original hypotheses. Glauberman's solvable factorization
constructs the concrete internal group and module factors. The classification
of offenders then supplies the universal structure theorem used by the
cyclic-three calculation. In particular, the B.1.12 theorem below has no
factorization, coordinate-recognition or quotient-kernel premise.

`source_lemma_B_1_8_corrected` includes the equal-weight minimal offender
classification and the corrected stable-family assertion: saturation preserves
the generated subgroup. The original definition of stability is retained.
The false printed equality of an arbitrary stable family with its saturation
is excluded; its independent counterexample is exported by the parent module.

The factor records contain multiplicative and linear equivalences compatible
with the actual inclusions, and equivariant identifications of the supports
with the natural binary planes. Their internal-coordinate API also supplies
commutation, independence and the support dimensions. In B.1.12 the conjugates
are indexed without repetition, subnormality is inside H = ⟨K,T⟩, the quotient
is literally M/O₂(M), and its T-action comes from conjugation on M. The
projective-model conversion uses the canonical SL₂(2) → PSL₂(2) quotient.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.1.8 and B.1.12, printed pp. 70 and 73 (PDF pp. 81 and 84).
-/

public section

open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Construct all valid B.1.8 structure data from the source hypotheses.
The offender-product field is a join of independent commuting Sylow choices;
`SolvableFFFactors.subproductEquiv` identifies it with their internal product. -/
theorem solvableFFStructure_nonempty
    (hsolv : Group.IsSolvable G) (hcore : pCore 2 G = ⊥)
    (hρ : Function.Injective ρ) (hff : IsFFModule ρ) :
    Nonempty (ThreeConjugates.SolvableFFStructure ρ) := by
  obtain ⟨⟨d⟩, hq, hn⟩ := Glauberman.source_lemma_B_1_8_1_3 hsolv hcore hρ hff
  refine ⟨{
    toSolvableFFFactors := d
    ratio_one := hq
    best_rank_eq := ?_
    offender_product := ?_
    stable_product := ?_ }⟩
  · intro A hA
    exact ((isBestOffender_iff_of_not_strong ρ (by rintro ⟨B, hB⟩; exact hn B hB) A).mp hA).2
  · intro A
    rw [d.isBestOffender_iff_sylowProduct hρ hq A]
    constructor
    · intro hA
      refine ⟨hA.ne_bot d, ?_⟩
      obtain ⟨B, hB, _, he⟩ := hA
      refine ⟨B, fun i => ?_, he⟩
      rcases hB i with hb | ⟨S, hs⟩
      · exact Or.inl hb
      · exact Or.inr ⟨S, hs.symm⟩
    · rintro ⟨hne, B, hB, he⟩
      refine ⟨B, fun i => ?_, ?_, he⟩
      · rcases hB i with hb | ⟨S, hs⟩
        · exact Or.inl hb
        · exact Or.inr ⟨S, hs.symm⟩
      · by_contra h
        push Not at h
        exact hne (by simp [he, h])
  · intro P hP
    exact ⟨d.stableFactorSet P, d.stable_generatedBy_eq hρ hq hP⟩

/-- The universal valid B.1.8 theorem required by the B.1.12 reduction.
Its existence and classification premises are discharged by the construction. -/
theorem solvableFFTheorem : ThreeConjugates.SolvableFFTheorem.{u, v} := by
  intro G V _ _ _ _ _ ρ hsolv hcore hρ hff
  exact solvableFFStructure_nonempty ρ hsolv hcore hρ hff

/-- B.1.8 with the valid generated-factor assertion and the corrected family
formulation. The witness contains (1)–(4); no equality P = saturation(P)
is asserted or added to the source hypotheses. -/
theorem source_lemma_B_1_8_corrected
    (hsolv : Group.IsSolvable G) (hcore : pCore 2 G = ⊥)
    (hρ : Function.Injective ρ) (hff : IsFFModule ρ) :
    ∃ d : ThreeConjugates.SolvableFFStructure ρ,
      (∀ A, ¬ IsStrongOffender ρ A) ∧
      (∀ A, IsMinimalBestOffender ρ A ↔
        ∃ (i : Fin d.count) (S : Sylow 2 (d.factor i)),
          A = d.toSolvableFFFactors.factorSylow i S) ∧
      (∀ P, IsStable ρ P →
        (d.toSolvableFFFactors.stableFactorSet P).Nonempty ∧
        generatedBy P ⊤ = ⨆ i ∈ d.toSolvableFFFactors.stableFactorSet P, d.factor i ∧
        P ⊆ saturation ρ P ∧ IsStable ρ (saturation ρ P) ∧
        generatedBy (saturation ρ P) ⊤ = generatedBy P ⊤) := by
  obtain ⟨d⟩ := solvableFFStructure_nonempty ρ hsolv hcore hρ hff
  refine ⟨d, (Glauberman.numerical_conclusions hsolv hcore hρ hff).2,
    d.toSolvableFFFactors.minimal_iff_factorSylow hρ d.ratio_one, ?_⟩
  intro P hP
  exact ⟨d.toSolvableFFFactors.stableFactorSet_nonempty hρ d.ratio_one hP,
    d.toSolvableFFFactors.stable_generatedBy_eq hρ d.ratio_one hP,
    hP.saturation_spec ρ⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Each quotient factor in B.1.12 is the actual projective group L₂(2). -/
@[expose] noncomputable def ThreeConjugates.ThreeConjugatesConclusion.factorProjectiveModel
    {K T : Subgroup G} (d : ThreeConjugates.ThreeConjugatesConclusion ρ K T)
    (i : ThreeConjugates.conjugateFamily K T) :
    d.quotientFactor i ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2) :=
  (d.factorModel i).trans Matrix.SpecialLinearGroup.sl2TwoEquivPSL2Two

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- The projective model agrees with the canonical central quotient map. -/
theorem ThreeConjugates.ThreeConjugatesConclusion.factorProjectiveModel_apply
    {K T : Subgroup G} (d : ThreeConjugates.ThreeConjugatesConclusion ρ K T)
    (i : ThreeConjugates.conjugateFamily K T) (g : d.quotientFactor i) :
    d.factorProjectiveModel ρ i g = QuotientGroup.mk (d.factorModel i g) := rfl

/-- B.1.12 from its original source hypotheses. This constructs both internal
products, the marked odd cores and the transitive induced T-action, with the
two-core taken inside M. The universal B.1.8 input is fully discharged. -/
theorem source_lemma_B_1_12 (hρ : Function.Injective ρ) (K : Subgroup G) (T : Sylow 2 G)
    (hcard : Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal)
    (hcomm : K = ⁅K, ThreeConjugates.localOffenderSubgroup ρ (T : Subgroup G)⁆) :
    Nonempty (ThreeConjugates.ThreeConjugatesConclusion ρ K (T : Subgroup G)) :=
  ThreeConjugates.threeConjugates_of_solvableFF ρ hρ K T hK hcard hcomm solvableFFTheorem

end CFSG.Quasithin.ChapterB
