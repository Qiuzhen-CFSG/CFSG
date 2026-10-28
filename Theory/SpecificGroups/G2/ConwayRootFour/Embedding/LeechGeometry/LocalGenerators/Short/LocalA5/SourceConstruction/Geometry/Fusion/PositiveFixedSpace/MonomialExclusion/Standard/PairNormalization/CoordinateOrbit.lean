module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.PairNormalization.Reduction

/-!
# The orbit of pointwise independent hexacode translation pairs

Every full-support word in the existing hexacode has one of eighteen encoder
parameters. For each such word exactly the two displayed partner parameters
can satisfy pointwise independence. The finite coverage checks use the six
binary encoder coordinates, avoiding enumeration of function-valued parameters.
A table of products of the existing adjacent-coordinate automorphisms sends
each of the thirty-six pairs to `(referenceHexA, referenceHexB)`.

All coverage and action identities are checked by kernel reduction. The table
entries already belong to `HexAutomorphisms`, so their products preserve the
literal code with its destination-indexed monomial action. The final application
uses the structural quaternion-pair reduction and the actual Golay monomial
lift to normalize both coordinate pullbacks.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
and the root-four conventions on p.269. This is the coordinate-orbit ingredient
of the Leech-model normalization, not the remaining sign calculation or the
whole book lemma. The encoder and generators are the existing attributed ATLAS
ports; the finite orbit certificate and its verification are new here.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.PairNormalization

/-- The full-support parameters, in increasing order of the six-bit encoding. -/
private def fullParameters : Fin 18 → HexParameters :=
  ![(![1,1,1], ![0,0], 0),
    (![1,0,1], ![1,0], 0),
    (![0,1,1], ![1,0], 0),
    (![1,1,1], ![1,0], 0),
    (![1,1,0], ![0,1], 0),
    (![0,1,1], ![0,1], 0),
    (![1,1,1], ![0,1], 0),
    (![1,1,0], ![1,1], 0),
    (![1,0,1], ![1,1], 0),
    (![1,1,1], ![1,1], 0),
    (![1,1,0], ![0,0], 1),
    (![0,0,0], ![1,0], 1),
    (![1,0,0], ![1,0], 1),
    (![0,1,0], ![1,0], 1),
    (![0,0,1], ![1,0], 1),
    (![1,1,1], ![1,0], 1),
    (![0,1,1], ![0,1], 1),
    (![1,0,1], ![1,1], 1)]

/-- The two pointwise independent partners for each full-support parameter. -/
private def partnerParameters : Fin 18 → Fin 2 → HexParameters :=
  ![![(![0,0,0], ![1,0], 1), (![1,1,1], ![1,0], 1)],
    ![(![0,1,1], ![0,1], 0), (![1,1,0], ![1,1], 0)],
    ![(![1,1,0], ![0,1], 0), (![1,0,1], ![1,1], 0)],
    ![(![1,1,0], ![0,0], 1), (![0,0,1], ![1,0], 1)],
    ![(![0,1,1], ![1,0], 0), (![1,0,1], ![1,1], 0)],
    ![(![1,0,1], ![1,0], 0), (![1,1,0], ![1,1], 0)],
    ![(![0,1,0], ![1,0], 1), (![1,0,1], ![1,1], 1)],
    ![(![1,0,1], ![1,0], 0), (![0,1,1], ![0,1], 0)],
    ![(![0,1,1], ![1,0], 0), (![1,1,0], ![0,1], 0)],
    ![(![1,0,0], ![1,0], 1), (![0,1,1], ![0,1], 1)],
    ![(![1,1,1], ![1,0], 0), (![0,0,1], ![1,0], 1)],
    ![(![1,1,1], ![0,0], 0), (![1,1,1], ![1,0], 1)],
    ![(![1,1,1], ![1,1], 0), (![0,1,1], ![0,1], 1)],
    ![(![1,1,1], ![0,1], 0), (![1,0,1], ![1,1], 1)],
    ![(![1,1,1], ![1,0], 0), (![1,1,0], ![0,0], 1)],
    ![(![1,1,1], ![0,0], 0), (![0,0,0], ![1,0], 1)],
    ![(![1,1,1], ![1,1], 0), (![1,0,0], ![1,0], 1)],
    ![(![1,1,1], ![0,1], 0), (![0,1,0], ![1,0], 1)]]

/-- Products act right to left, with the existing destination-indexed convention. -/
private def pairNormalizer : Fin 18 → Fin 2 → HexAutomorphisms :=
  ![![1, hexLift 0 * hexLift 1 * hexLift 2],
    ![hexLift 0 * hexLift 3 * hexLift 0, hexLift 2 * hexLift 1 * hexLift 3 * hexLift 0],
    ![hexLift 4 * hexLift 3 * hexLift 0 * hexLift 1, hexLift 0 * hexLift 2 * hexLift 3 * hexLift 0 * hexLift 1],
    ![hexLift 0 * hexLift 2, hexLift 4],
    ![hexLift 0 * hexLift 2 * hexLift 1, hexLift 1 * hexLift 0],
    ![hexLift 0 * hexLift 1 * hexLift 3 * hexLift 0 * hexLift 2 * hexLift 1, hexLift 1 * hexLift 0 * hexLift 3 * hexLift 0 * hexLift 1],
    ![hexLift 2, hexLift 0 * hexLift 1],
    ![hexLift 1, hexLift 0 * hexLift 1 * hexLift 2 * hexLift 1],
    ![hexLift 0 * hexLift 3, hexLift 2 * hexLift 1 * hexLift 3],
    ![hexLift 0, hexLift 2 * hexLift 1],
    ![hexLift 4 * hexLift 3 * hexLift 0, hexLift 0 * hexLift 2 * hexLift 3 * hexLift 0],
    ![hexLift 2 * hexLift 3 * hexLift 4, hexLift 0 * hexLift 1 * hexLift 3 * hexLift 4],
    ![hexLift 2 * hexLift 3 * hexLift 0 * hexLift 1, hexLift 0 * hexLift 1 * hexLift 3 * hexLift 0 * hexLift 1],
    ![hexLift 4 * hexLift 3, hexLift 0 * hexLift 2 * hexLift 3],
    ![hexLift 2 * hexLift 3, hexLift 0 * hexLift 1 * hexLift 3],
    ![hexLift 1 * hexLift 0 * hexLift 3 * hexLift 0, hexLift 0 * hexLift 1 * hexLift 3 * hexLift 0 * hexLift 2],
    ![hexLift 1 * hexLift 0 * hexLift 3, hexLift 0 * hexLift 1 * hexLift 3 * hexLift 2],
    ![hexLift 2 * hexLift 3 * hexLift 0, hexLift 0 * hexLift 1 * hexLift 3 * hexLift 0]]

-- Keeping the six bits explicit makes the kernel certificate small.
private theorem full_coverage_bits : ∀ x₀ x₁ x₂ r₀ r₁ t : Bit,
    let x : HexParameters := (![x₀,x₁,x₂], ![r₀,r₁], t)
    (∀ j, hexEncoder x j ≠ 0) → ∃ i : Fin 18, x = fullParameters i := by
  decide +kernel

private theorem partner_coverage_bits : ∀ (i : Fin 18) (x₀ x₁ x₂ r₀ r₁ t : Bit),
    let y : HexParameters := (![x₀,x₁,x₂], ![r₀,r₁], t)
    (∀ j, hexEncoder y j ≠ 0) →
    (∀ j, hexEncoder (fullParameters i) j ≠ hexEncoder y j) →
    ∃ e : Fin 2, y = partnerParameters i e := by
  decide +kernel

private theorem pair_normalizes : ∀ (i : Fin 18) (e : Fin 2),
    Monomial.act (pairNormalizer i e).val (hexEncoder (fullParameters i)) = referenceHexA ∧
    Monomial.act (pairNormalizer i e).val (hexEncoder (partnerParameters i e)) = referenceHexB := by
  decide +kernel

private theorem parameters_eta (x : HexParameters) :
    (![x.1 0,x.1 1,x.1 2], ![x.2.1 0,x.2.1 1], x.2.2) = x := by
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl

private theorem full_coverage (x : HexParameters) :
    (∀ j, hexEncoder x j ≠ 0) → ∃ i : Fin 18, x = fullParameters i := by
  simpa only [parameters_eta] using
    full_coverage_bits (x.1 0) (x.1 1) (x.1 2) (x.2.1 0) (x.2.1 1) x.2.2

private theorem partner_coverage (i : Fin 18) (y : HexParameters) :
    (∀ j, hexEncoder y j ≠ 0) →
    (∀ j, hexEncoder (fullParameters i) j ≠ hexEncoder y j) →
    ∃ e : Fin 2, y = partnerParameters i e := by
  simpa only [parameters_eta] using
    partner_coverage_bits i (y.1 0) (y.1 1) (y.1 2) (y.2.1 0) (y.2.1 1) y.2.2

/-- Every ordered pair of pointwise independent, full-support hexacode words
is sent to the reference pair by an actual hexacode monomial automorphism. -/
public theorem translationPairOrbit : TranslationPairOrbit := by
  intro h k hh hk hne
  obtain ⟨x,hx⟩ := h.prop
  obtain ⟨y,hy⟩ := k.prop
  obtain ⟨i,rfl⟩ := full_coverage x (by simpa only [hx] using hh)
  obtain ⟨e,rfl⟩ := partner_coverage i y (by simpa only [hy] using hk)
    (by simpa only [hx,hy] using hne)
  exact ⟨pairNormalizer i e, by simpa only [hx,hy] using pair_normalizes i e⟩

/-- Applying the orbit theorem to the structural translation reduction gives
an actual Golay monomial conjugator for both coordinate pullbacks. This
discharges the coordinate-orbit premise of standard pair normalization; the
independent sign calculation remains with the normalization assembly. -/
public theorem standard_pair_coordinate_conjugator
    (a b : GolayMonomialGroup)
    (hstd : quaternionParts a b = distinguishedUnorderedSextet.val)
    (ha : (monomialEmbedding a) ^ 2 = negationIsometry)
    (hb : (monomialEmbedding b) ^ 2 = negationIsometry)
    (hab : (monomialEmbedding a * monomialEmbedding b) ^ 2 =
      negationIsometry) :
    ∃ g : HexAutomorphisms,
      (∀ i, monomialPull (hexMonomialLift g * a * (hexMonomialLift g)⁻¹) i =
        referencePullA i) ∧
      (∀ i, monomialPull (hexMonomialLift g * b * (hexMonomialLift g)⁻¹) i =
        referencePullB i) := by
  obtain ⟨h,k,hh,hk,hne,hap,hbp⟩ := standard_pair_translations a b hstd ha hb hab
  obtain ⟨g,hga,hgb⟩ := translationPairOrbit h k hh hk hne
  refine ⟨g,?_,?_⟩
  · intro i
    rw [pull_conjugate_hexMonomialLift g a h.val hap,hga]
    rfl
  · intro i
    rw [pull_conjugate_hexMonomialLift g b k.val hbp,hgb]
    rfl

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.PairNormalization
