module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.BinarySixObstruction.Basic

/-!
# Primitivity on the 27 binary singular points

Assuming the Siegel-generated subgroup lies in the orthogonal commutator,
we prove primitivity of the literal action on `Point`. No simplicity or
recognition theorem is used.

The point with first coordinate one is the base point. Explicit Siegel
transformations take it to every singular point. Further transformations fix
the base point and take one of two representatives to each other point. Each
representative has ten distinct points in its stabilizer orbit. Consequently,
a nonsingleton block through the base point contains at least ten points.
Its cardinality divides 27, so it must be the whole point set.

The short coordinate tables are witnesses, with validity and action identities
checked by kernel reduction. The integer codes store the six binary coordinates
from low bit to high bit, in the order of the two hyperbolic pairs and the
anisotropic pair. The checked injection of 27 points is surjective by
`card_point`; no enumeration of the orthogonal group is needed.

This supplies the geometric input for the Iwasawa argument in
`BinarySixObstruction.Iwasawa`, using the unhalved polar convention of
`SplitOdd.Siegel` and its attributed ATLAS construction. Source context:
GLS3 §2.7 (especially Lemma 2.7.2), Table 5.3o, and Aschbacher--Smith
A.2.15(2), A.2.19. The elementary-subgroup inclusion is deliberately explicit;
its producer is independent of this geometric argument.
-/

public section

open ClassicalOrthogonal
open ClassicalOrthogonal.Minus
namespace ClassicalOrthogonal.Minus.BinarySixObstruction

private def binaryVector (n : ℕ) : NaturalSpace :=
  (![((n % 2 : ℕ), ((n / 2) % 2 : ℕ)),
      (((n / 4) % 2 : ℕ), ((n / 8) % 2 : ℕ))],
    (((n / 16) % 2 : ℕ), ((n / 32) % 2 : ℕ)))

private def pointCodes : Fin 27 → ℕ :=
  ![1, 2, 4, 5, 6, 8, 9, 10, 15, 19, 23, 27, 28, 29,
    30, 35, 39, 43, 44, 45, 46, 51, 55, 59, 60, 61, 62]

private def indexedVector (i : Fin 27) : NaturalSpace := binaryVector (pointCodes i)

private theorem indexedVector_valid : ∀ i, indexedVector i ≠ 0 ∧ naturalForm (indexedVector i) = 0 := by
  rw [naturalForm_eq]
  decide +kernel

private def indexedPoint (i : Fin 27) : Point := ⟨indexedVector i, indexedVector_valid i⟩

private theorem indexedPoint_injective : Function.Injective indexedPoint := by
  have h : ∀ i j : Fin 27, indexedVector i = indexedVector j → i = j := by decide +kernel
  intro i j hij
  exact h i j (congrArg Subtype.val hij)

private theorem indexedPoint_surjective : Function.Surjective indexedPoint :=
  (indexedPoint_injective.bijective_of_nat_card_le (by simp [card_point])).2

/-- Direction/parameter pairs sending the base point to each indexed point. -/
private def transportCodes : Fin 27 → ℕ × ℕ :=
  ![(0, 0), (15, 3), (5, 10), (2, 4), (10, 7), (6, 9), (2, 8),
    (6, 11), (2, 12), (2, 16), (2, 20), (2, 24), (6, 27), (2, 28),
    (6, 25), (2, 32), (2, 36), (2, 40), (6, 43), (2, 44), (6, 41),
    (2, 48), (2, 52), (2, 56), (6, 59), (2, 60), (6, 57)]

private theorem transport_checked : ∀ i : Fin 27,
    naturalForm (binaryVector (transportCodes i).1) = 0 ∧
    naturalForm.polarBilin (binaryVector (transportCodes i).1)
      (binaryVector (transportCodes i).2) = 0 ∧
    Quadratic.siegel naturalForm (binaryVector (transportCodes i).1)
      (binaryVector (transportCodes i).2) (indexedVector 0) = indexedVector i := by
  rw [naturalForm_eq]
  decide +kernel

/-- Direction/parameter pairs fixing the base point and moving its two suborbit representatives. -/
private def stabilizerCodes : Fin 27 → ℕ × ℕ :=
  ![(0, 0), (0, 0), (0, 0), (1, 8), (1, 4), (28, 12), (28, 13),
    (1, 8), (1, 12), (1, 16), (1, 20), (1, 24), (8, 16), (8, 17),
    (1, 28), (1, 32), (1, 36), (1, 40), (8, 32), (8, 33), (1, 44),
    (1, 48), (1, 52), (1, 56), (8, 48), (8, 49), (1, 60)]

private def perpendicular (i : Fin 27) : Bool := (pointCodes i / 2) % 2 == 0

/-- The representatives have vector codes 4 (perpendicular) and 2 (nonperpendicular). -/
private def representative (i : Fin 27) : Fin 27 :=
  if perpendicular i then 2 else 1

private theorem stabilizer_checked : ∀ i : Fin 27,
    naturalForm (binaryVector (stabilizerCodes i).1) = 0 ∧
    naturalForm.polarBilin (binaryVector (stabilizerCodes i).1)
      (binaryVector (stabilizerCodes i).2) = 0 ∧
    Quadratic.siegel naturalForm (binaryVector (stabilizerCodes i).1)
      (binaryVector (stabilizerCodes i).2) (indexedVector 0) = indexedVector 0 ∧
    (i ≠ 0 → Quadratic.siegel naturalForm (binaryVector (stabilizerCodes i).1)
      (binaryVector (stabilizerCodes i).2) (indexedVector (representative i)) = indexedVector i) := by
  rw [naturalForm_eq]
  decide +kernel

/-- Ten distinct points in each of the two representative orbits suffice for the block bound. -/
private def tenIndices (b : Bool) : Fin 10 → Fin 27 :=
  if b then ![2, 3, 5, 6, 12, 13, 18, 19, 24, 25] else ![1, 4, 7, 8, 9, 10, 11, 14, 15, 16]

private theorem tenIndices_checked : ∀ b : Bool,
    Function.Injective (tenIndices b) ∧
    ∀ j, tenIndices b j ≠ 0 ∧ representative (tenIndices b j) = (if b then 2 else 1) := by
  decide +kernel

open scoped Pointwise

variable (hle : elementarySubgroup naturalForm ≤ commutator FullGroup)

private noncomputable def transport (i : Fin 27) : OmegaGroup :=
  ⟨siegelElement naturalForm (binaryVector (transportCodes i).1)
    (binaryVector (transportCodes i).2) (transport_checked i).1 (transport_checked i).2.1,
    hle (siegelElement_mem _ _ _ _ _)⟩

private theorem transport_smul (i : Fin 27) :
    transport hle i • indexedPoint 0 = indexedPoint i :=
  Subtype.ext (transport_checked i).2.2

include hle in
private theorem pointAction_isPretransitive : MulAction.IsPretransitive OmegaGroup Point := by
  apply (MulAction.isPretransitive_iff_base (indexedPoint 0)).mpr
  intro p
  obtain ⟨i, rfl⟩ := indexedPoint_surjective p
  exact ⟨transport hle i, transport_smul hle i⟩

private noncomputable def stabilizerTransport (i : Fin 27) : OmegaGroup :=
  ⟨siegelElement naturalForm (binaryVector (stabilizerCodes i).1)
    (binaryVector (stabilizerCodes i).2) (stabilizer_checked i).1 (stabilizer_checked i).2.1,
    hle (siegelElement_mem _ _ _ _ _)⟩

private theorem stabilizerTransport_fix (i : Fin 27) :
    stabilizerTransport hle i • indexedPoint 0 = indexedPoint 0 :=
  Subtype.ext (stabilizer_checked i).2.2.1

private theorem stabilizerTransport_smul (i : Fin 27) (hi : i ≠ 0) :
    stabilizerTransport hle i • indexedPoint (representative i) = indexedPoint i :=
  Subtype.ext ((stabilizer_checked i).2.2.2 hi)

private theorem block_mem_of_fix {B : Set Point} (hB : MulAction.IsBlock OmegaGroup B)
    (hb : indexedPoint 0 ∈ B) {g : OmegaGroup} (hg : g • indexedPoint 0 = indexedPoint 0)
    {p : Point} (hp : p ∈ B) : g • p ∈ B := by
  have he : g • B = B := MulAction.mem_stabilizer_iff.mp
    (hB.stabilizer_le hb (MulAction.mem_stabilizer_iff.mpr hg))
  rw [← he]
  exact Set.smul_mem_smul_set hp

include hle in
private theorem block_card_ge_ten {B : Set Point} (hB : MulAction.IsBlock OmegaGroup B)
    (hb : indexedPoint 0 ∈ B) (i : Fin 27) (hi : i ≠ 0) (hip : indexedPoint i ∈ B) :
    10 ≤ B.ncard := by
  have hrep : indexedPoint (representative i) ∈ B := by
    have hfix : (stabilizerTransport hle i)⁻¹ • indexedPoint 0 = indexedPoint 0 := by
      rw [inv_smul_eq_iff, stabilizerTransport_fix]
    have h := block_mem_of_fix hB hb hfix hip
    rw [← stabilizerTransport_smul hle i hi, inv_smul_smul] at h
    exact h
  have hmem (j : Fin 10) : indexedPoint (tenIndices (perpendicular i) j) ∈ B := by
    have h := block_mem_of_fix hB hb
      (stabilizerTransport_fix hle (tenIndices (perpendicular i) j)) hrep
    have he : representative (tenIndices (perpendicular i) j) = representative i :=
      ((tenIndices_checked (perpendicular i)).2 j).2
    rw [← he,
      stabilizerTransport_smul hle _ ((tenIndices_checked (perpendicular i)).2 j).1] at h
    exact h
  have hinj : Function.Injective (fun j => indexedPoint (tenIndices (perpendicular i) j)) :=
    indexedPoint_injective.comp (tenIndices_checked (perpendicular i)).1
  have hsub : Set.range (fun j => indexedPoint (tenIndices (perpendicular i) j)) ⊆ B := by
    rintro _ ⟨j, rfl⟩
    exact hmem j
  have hcard := Set.ncard_le_ncard hsub
  simpa only [Set.ncard_range_of_injective hinj, Nat.card_fin] using hcard

/-- The natural singular-point action is primitive as soon as Siegel transformations
belong to the orthogonal commutator group. This discharges the geometric premise
of `isSimpleGroup_of_geometry_and_generation`. -/
theorem pointAction_isPreprimitive_of_elementary_le
    (hle : elementarySubgroup naturalForm ≤ commutator FullGroup) :
    MulAction.IsPreprimitive OmegaGroup Point := by
  classical
  let _ := pointAction_isPretransitive hle
  apply MulAction.IsPreprimitive.of_isTrivialBlock_base (indexedPoint 0)
  intro B hb hB
  by_cases hsmall : B.Subsingleton
  · exact Or.inl hsmall
  right
  obtain ⟨p, hp, hne⟩ : ∃ p ∈ B, p ≠ indexedPoint 0 := by
    by_contra! h
    exact hsmall (fun x hx y hy => (h x hx).trans (h y hy).symm)
  obtain ⟨i, rfl⟩ := indexedPoint_surjective p
  have hi : i ≠ 0 := fun h => hne (congrArg indexedPoint h)
  have hten := block_card_ge_ten hle hB hb i hi hp
  have hdvd : B.ncard ∣ 27 := card_point ▸ hB.ncard_dvd_card ⟨_, hb⟩
  have hcard : B.ncard = 27 := by
    have hdiv : ∀ n ∈ Nat.divisors 27, 10 ≤ n → n = 27 := by decide +kernel
    exact hdiv _ (Nat.mem_divisors.mpr ⟨hdvd, by decide⟩) hten
  exact B.eq_univ_iff_ncard.mpr (hcard.trans card_point.symm)

end ClassicalOrthogonal.Minus.BinarySixObstruction
