module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable.Displacement.Inputs
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable.Displacement.Conjugation
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.FrobeniusCounts

/-!
# Outer displacement on adjoint-only unitary tensor words

The tensor calculation applies to any number and positions of adjoint factors.
The scalar-rigidity lemma identifies the actual square-one actor once a model
operator is proved to induce the same conjugation on the absolute component.
Its single-operator estimate then bounds the literal common invariant quotient
from `SchurOuter.Scalars`. An outer actor excludes the all-trivial word.

The geometric construction in `Displacement.Conjugation` supplies coordinates
from the genuine outer involution through the perfect image and its central
quotient. Combining it with scalar rigidity and the tensor estimate proves
`OuterWordDisplacement` under the source field and central-kernel hypotheses.
Natural-label absence remains the explicit premise of that contract; no
single-factor, Schur-degree, or displacement premise is used. Arbitrary
Hermitian forms and the endpoint s=2 are retained.

Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.11,
internal pp.31--32, with the tensor estimates of §2.2 and §3.5.
-/

public section
set_option backward.isDefEq.respectTransparency false
open BenderSuzuki.MatrixGroups Representation Representation.FrobeniusTensor
open Representation.SL3.BinaryDefiningFactors Representation.BinaryOffender
open Representation.SU3.CubicDegree.SchurOuter
open Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable

variable {F V : Type*} [Field F] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (J : HermitianForm 3 F)
  (σ : Representation (ZMod 2) J.specialSubgroup V) [σ.IsIrreducible]

omit [FiniteDimensional (ZMod 2) V] [σ.IsIrreducible] in
private theorem exists_nonidentity_of_outer
    (t : linearNormalizer σ)
    (hout : (actionImage σ).normalizerMonoidHom t ∉
      MulAut.innerSubgroup (actionImage σ)) : ∃ g, σ g ≠ 1 := by
  by_contra h
  push Not at h
  have hall (x : actionImage σ) : x = 1 := by
    obtain ⟨g, hg⟩ := x.property
    apply Subtype.ext
    rw [← hg]
    apply Units.ext
    exact h g
  apply hout
  refine ⟨1, ?_⟩
  apply MulEquiv.ext
  intro x
  exact (hall _).trans (hall _).symm

/-- Conditional assembly of the exact published displacement contract. The geometric
conjugation premise remains an obligation of the source theorem's assembly owner. -/
theorem outerWordDisplacement_of_tensor_conjugation {s : ℕ}
    (hc : OuterTensorConjugation J σ s) : OuterWordDisplacement J σ s := by
  intro ι w hw he hn A hA hl t ht ho
  have hp := MinimalDegree.counts_pos_of_schur_word J σ ι w
    (exists_nonidentity_of_outer J σ t ho) he
  have ha : 0 < adjointCount w := by omega
  obtain ⟨e, heq⟩ := hc ι w hw he hn A hA hl t ht ho
  have ht2 : t ^ 2 = 1 := by
    let : IsElementaryAbelian 2 A := hA.2
    exact elemPow_eq_one_of_isElementaryAbelian t ht
  have ha2 : (⟨t, ht⟩ : A) * ⟨t, ht⟩ = 1 := by
    apply Subtype.ext
    change t * t = 1
    simpa only [pow_two] using ht2
  have hop : absoluteActorRepresentation σ A hl ⟨t, ht⟩ *
      absoluteActorRepresentation σ A hl ⟨t, ht⟩ = 1 := by
    rw [← map_mul, ha2, map_one]
  have hd := wordDegree_le_three_invariants_quotient_of_conjugation
    (absoluteRep σ) (absoluteActorRepresentation σ A hl) ⟨t, ht⟩ hop w hn ha e heq
  omega

/-- The literal common invariant quotient of an outer elementary-two actor
has dimension at least one sixth of any adjoint-only tensor word realizing
the absolute representation. The tensor conjugation premise is discharged
from the source field and central-kernel hypotheses. -/
theorem outerWordDisplacement [Finite F] {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (hk : σ.ker ≤ Subgroup.center J.specialSubgroup) :
    OuterWordDisplacement J σ s :=
  outerWordDisplacement_of_tensor_conjugation J σ
    (outerTensorConjugation J σ hs hcard hconj hk)

end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable
