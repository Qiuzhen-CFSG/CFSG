module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationStrictRank
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictCentralCover

/-!
# The ambient central cover on the whole reduced layer

The literal lift U/⟨z⟩ covers U/Z(U) for K/O₂(K), where K is the
H-normal closure of the whole reduced layer. The original strict source
hypotheses supply both binary structures and full commutator generation.
A nontrivial crossed-center image therefore forces nonzero dual first
cohomology. In particular this retains information absent from the abstract
G.11 action when its exceptional exchanged row has |X₀| = 2.

Source: Aschbacher–Smith 6.2.16–17, printed pp.689–690, and I.1.5,
printed p.408; application to the original 12.2.2(3d) reduction. The
exceptional model comparison and the final strict contradiction remain
separate proof obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The original ambient lift is a central cover, with its literal quotient projection. -/
theorem strict_reduced_central_cover
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L (wholeReduced T L) <
      sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L) :
    let := A.sourceEqualityVectorQuotient_elementary h611 hz
    ∃ he : IsElementaryAbelian 2
        (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z),
      let := he
      Representation.OneCohomology.IsCover
        (strictLiftProjection A h611 hnatural hz horder hstrict) := by
  let := A.sourceEqualityVectorQuotient_elementary h611 hz
  obtain ⟨he, _⟩ := A.strict_symplectic_geometry h611 hnatural hz horder hstrict
  let := he
  exact ⟨he, A.strictLiftProjection_isCover h611 hnatural hz horder hstrict⟩

/-- A nontrivial marked crossed-center image forces dual cohomology on the
actual layer-closure quotient; no model or cohomology hypothesis is assumed. -/
theorem strict_reduced_crossing_dual_H1_pos
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L (wholeReduced T L) <
      sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L (wholeReduced T L))
    (hdH : d ∉ centralizer ({z} : Set G))
    (hX0 : 1 < Nat.card (strictCrossingCenterImage (T : Subgroup G) L (wholeReduced T L) z d)) :
    let := A.sourceEqualityVectorQuotient_elementary h611 hz
    ∃ he : IsElementaryAbelian 2
        (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z),
      let := he
      0 < Module.finrank (ZMod 2) (Representation.OneCohomology.H1
        (strictLayerRepresentation A h611 hnatural hz horder hstrict).dual) := by
  let := A.sourceEqualityVectorQuotient_elementary h611 hz
  obtain ⟨he, _⟩ := A.strict_symplectic_geometry h611 hnatural hz horder hstrict
  let := he
  exact ⟨he, A.strict_crossing_dual_H1_pos h611 hnatural hz horder hTH hstrict hdres hdH hX0⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
