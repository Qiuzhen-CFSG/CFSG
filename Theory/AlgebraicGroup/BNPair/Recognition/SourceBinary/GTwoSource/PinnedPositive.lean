module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.RankOnePinning
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.PositiveCoordinates
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.WeylCoefficient

/-!
# The constructed short rank-one map in the G₂ positive calculation

The faithful panel comparison and whole SL₂ extension replace the assumed
homomorphism in ShortRankOneData. If its Weyl image is the chosen source
lift, the two required root interchanges follow directly from the canonical
right-conjugate root coordinates and the proved involution relation. The
orthogonal-root centralizer supplies the remaining fixed highest root.

The coefficient argument then gives the literal positive presentation in
every finite characteristic-two field. The Cartan/Weyl alignment, the
orthogonal centralizer and PartialPositiveData remain explicit obligations;
this is not a proof of (6E)(a) → (9A). In particular no natural/tensor module
identification or binary source commutator has been assumed under a model tag.

Source: Fong--Seitz II §7, (9.6), and (9.12)--(9.21), printed pp.192,
212, 215--217. The actual marked-quotient application is PinningApplication.
-/

@[expose] public noncomputable section
open Subgroup Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure Atlas.G2.RootPresentationRecognition
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)
  (hs : pinnedReflection Q split short (hK short) (μ short) = (n short).val)
  (hc : rankOne Q split short ≤ centralizer (positiveCarrier Q split short 0 : Set (X ⧸ Q.D)))

/-- The actual short SL₂ map supplies the two transported root orbits.
Only alignment with the chosen source lift and the orthogonal centralizer remain. -/
def sourceShortRankOne : ShortRankOneData (sourceRoots Q split hK μ n short) where
  hom := sourcePinningHom Q split short (hK short) (μ short)
  root a := sourcePinningHom_root Q split short (hK short) (μ short) a
  fixes_highest a := by
    have ha : (sourceRoots Q split hK μ n short).x 0 a ∈ positiveCarrier Q split short 0 := by
      rw [← sourceRoots_range Q split hK μ n short 0]
      exact ⟨.ofAdd a,rfl⟩
    have hcomm := mem_centralizer_iff.mp
      (hc (pinnedReflection_mem Q split short (hK short) (μ short))) _ ha
    change pinnedReflection Q split short (hK short) (μ short) *
      (sourceRoots Q split hK μ n short).x 0 a *
        (pinnedReflection Q split short (hK short) (μ short))⁻¹ = _
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  long_orbit a := by
    have hinv : (pinnedReflection Q split short (hK short) (μ short))⁻¹ =
        pinnedReflection Q split short (hK short) (μ short) :=
      inv_eq_of_mul_eq_one_right (pinnedReflection_sq Q split short (hK short) (μ short))
    change MulAut.conj (pinnedReflection Q split short (hK short) (μ short))
      (simpleParameter Q split (1-short) (hK (1-short)) (μ (1-short)) (.ofAdd a)) =
      MulAut.conj ((n short).val : X ⧸ Q.D)⁻¹
        (simpleParameter Q split (1-short) (hK (1-short)) (μ (1-short)) (.ofAdd a))
    rw [← hs, hinv]

  middle_orbit a := by
    have hinv : (pinnedReflection Q split short (hK short) (μ short))⁻¹ =
        pinnedReflection Q split short (hK short) (μ short) :=
      inv_eq_of_mul_eq_one_right (pinnedReflection_sq Q split short (hK short) (μ short))
    change MulAut.conj (pinnedReflection Q split short (hK short) (μ short))
      (MulAut.conj ((n (1-short)).val : X ⧸ Q.D)⁻¹
        (simpleParameter Q split short (hK short) (μ short) (.ofAdd a))) =
      MulAut.conj (((n (1-short)).val : X ⧸ Q.D) * (n short).val)⁻¹
        (simpleParameter Q split short (hK short) (μ short) (.ofAdd a))
    simp only [MulAut.conj_apply, mul_inv_rev, inv_inv, ← hs, hinv]
    group

include hs hc in
/-- The remaining lower positive equations now imply the full positive table
using the constructed same-source rank-one map, including over F₂ and F₄. -/
theorem source_positive_relations
    (d : PartialPositiveData (sourceRoots Q split hK μ n short)) :
    (sourceRoots Q split hK μ n short).CharTwoRelations :=
  d.relations_of_short_rankOne (sourceShortRankOne Q split hK μ n short hs hc)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
