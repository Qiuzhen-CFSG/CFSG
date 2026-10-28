module

public import Theory.Representation.BinaryQuarticMathieu.Basic
public import Theory.Mathieu.M22.Properties.Design
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# From an intrinsic binary configuration to the literal Witt design

A linear equivalence permuting the 22 marked vectors permutes their zero-sum
six-subsets. When these are the literal Witt hexads, this gives an element of
`m22DesignAut`. Spanning makes the permutation determine the linear map.
Consequently the order is at most 887040.

The finite recognition and zero-sum coverage hypotheses in the final reductions
are explicit proof obligations. These reductions alone do not establish the
order bound for the quartic stabilizer.
-/

public section

namespace BinaryQuarticMathieu

open Sporadic.Mathieu
open scoped Pointwise

attribute [local irreducible] quartic

/-- The linear map carries each marked point to a marked point. -/
@[expose] def PermutesPoints (g : U ≃ₗ[F] U) : Prop :=
  ∀ i, ∃ j, point j = g (point i)

private noncomputable def pointImage (g : U ≃ₗ[F] U) (hg : PermutesPoints g)
    (i : Fin 22) : Fin 22 := (hg i).choose

private theorem pointImage_spec (g : U ≃ₗ[F] U) (hg : PermutesPoints g) (i : Fin 22) :
    point (pointImage g hg i) = g (point i) := (hg i).choose_spec

private theorem pointImage_injective (g : U ≃ₗ[F] U) (hg : PermutesPoints g) :
    Function.Injective (pointImage g hg) := by
  intro i j hij
  apply point_injective
  apply g.injective
  rw [← pointImage_spec g hg i, ← pointImage_spec g hg j, hij]

/-- The induced permutation of the repository's 22 point labels. -/
noncomputable def pointPermutation (g : U ≃ₗ[F] U) (hg : PermutesPoints g) :
    Equiv.Perm (Fin 22) :=
  Equiv.ofBijective (pointImage g hg)
    ⟨pointImage_injective g hg, Finite.surjective_of_injective (pointImage_injective g hg)⟩

theorem pointPermutation_spec (g : U ≃ₗ[F] U) (hg : PermutesPoints g) (i : Fin 22) :
    point (pointPermutation g hg i) = g (point i) := pointImage_spec g hg i

/-- Linearity preserves exactly the zero-sum six-subsets. -/
theorem pointPermutation_hexad_iff (g : U ≃ₗ[F] U) (hg : PermutesPoints g)
    (B : Finset (Fin 22)) :
    IsHexad (pointPermutation g hg • B) ↔ IsHexad B := by
  have hc : (pointPermutation g hg • B).card = B.card := by
    exact Finset.card_image_of_injective B (pointPermutation g hg).injective
  have hs : ∑ i ∈ pointPermutation g hg • B, point i = g (∑ i ∈ B, point i) := by
    change ∑ i ∈ B.image (pointPermutation g hg), point i = _
    rw [Finset.sum_image]
    · simp_rw [pointPermutation_spec]
      exact (map_sum g _ _).symm
    · exact fun i _ j _ hij => (pointPermutation g hg).injective hij
  unfold IsHexad
  rw [hc, hs, map_eq_zero_iff g g.injective]

/-- Identifying all zero-sum hexads gives membership in the existing literal
Mathieu design automorphism group. -/
theorem pointPermutation_mem_designAut
    (hhex : ∀ B : Finset (Fin 22), B ∈ m22Blocks ↔ IsHexad B)
    (g : U ≃ₗ[F] U) (hg : PermutesPoints g) :
    pointPermutation g hg ∈ m22DesignAut := by
  rw [m22DesignAut, Theory.GroupTheory.SteinerSystem.mem_aut_iff]
  change pointPermutation g hg • (m22Blocks : Set (Finset (Fin 22))) =
    (m22Blocks : Set (Finset (Fin 22)))
  ext B
  constructor
  · rintro ⟨C, hC, rfl⟩
    exact (hhex _).mpr ((pointPermutation_hexad_iff g hg C).mpr ((hhex C).mp hC))
  · intro hB
    refine ⟨(pointPermutation g hg)⁻¹ • B, ?_, smul_inv_smul _ _⟩
    apply (hhex _).mpr
    apply (pointPermutation_hexad_iff g hg _).mp
    simpa using (hhex B).mp hB

/-- Spanning forces the action on the 22 points to be faithful. -/
theorem pointPermutation_injective
    {g h : U ≃ₗ[F] U} (hg : PermutesPoints g) (hh : PermutesPoints h)
    (heq : pointPermutation g hg = pointPermutation h hh) : g = h := by
  have hlin : g.toLinearMap = h.toLinearMap := by
    apply LinearMap.ext_on point_span
    rintro _ ⟨i, rfl⟩
    change g (point i) = h (point i)
    rw [← pointPermutation_spec g hg i, ← pointPermutation_spec h hh i, heq]
  exact LinearEquiv.toLinearMap_injective hlin

/-- Any collection of linear equivalences permuting a spanning realization of
these hexads injects into the literal full design automorphism group. -/
theorem card_le_of_configuration (S : Set (U ≃ₗ[F] U))
    (hpoints : ∀ g ∈ S, PermutesPoints g)
    (hhex : ∀ B : Finset (Fin 22), B ∈ m22Blocks ↔ IsHexad B) :
    Nat.card S ≤ 887040 := by
  let f : S → m22DesignAut := fun g =>
    ⟨pointPermutation g.val (hpoints g.val g.property),
      pointPermutation_mem_designAut hhex g.val (hpoints g.val g.property)⟩
  have hf : Function.Injective f := by
    intro g h heq
    apply Subtype.ext
    exact pointPermutation_injective (hpoints g.val g.property) (hpoints h.val h.property)
      (congrArg Subtype.val heq)
  simpa only [m22DesignAut_order] using Nat.card_le_card_of_injective f hf

/-- The intrinsic rank recognition supplies point preservation for every
quartic-preserving linear equivalence. -/
theorem permutesPoints_of_preserves
    (hrecognition : ∀ v : U, rankDistribution quartic v = pointDistribution ↔
      v ∈ Set.range point)
    {g : U ≃ₗ[F] U} (hg : Preserves quartic g) : PermutesPoints g := by
  intro i
  apply (hrecognition (g (point i))).mp
  rw [rankDistribution_invariant hg]
  exact (hrecognition (point i)).mpr ⟨i, rfl⟩

/-- Conditional assembly: both finite configuration certificates must still be
proved before this yields the unconditional full-stabilizer bound. -/
theorem quarticStabilizer_card_le_of_certificates
    (hrecognition : ∀ v : U, rankDistribution quartic v = pointDistribution ↔
      v ∈ Set.range point)
    (hhex : ∀ B : Finset (Fin 22), B ∈ m22Blocks ↔ IsHexad B) :
    Nat.card quarticStabilizer ≤ 887040 := by
  apply card_le_of_configuration (quarticStabilizer : Set (U ≃ₗ[F] U))
  · intro g hg
    exact permutesPoints_of_preserves hrecognition hg
  · exact hhex

/-- The faithful point action lands in the literal full design automorphism group. -/
noncomputable def quarticStabilizerToDesignAut
    (hrecognition : ∀ v : U, rankDistribution quartic v = pointDistribution ↔
      v ∈ Set.range point)
    (hhex : ∀ B : Finset (Fin 22), B ∈ m22Blocks ↔ IsHexad B) :
    quarticStabilizer →* m22DesignAut where
  toFun g := ⟨pointPermutation g.val (permutesPoints_of_preserves hrecognition g.property),
    pointPermutation_mem_designAut hhex g.val
      (permutesPoints_of_preserves hrecognition g.property)⟩
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply point_injective
    exact pointPermutation_spec _ _ i
  map_mul' g h := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    change pointPermutation (g * h).val _ i =
      pointPermutation g.val _ (pointPermutation h.val _ i)
    apply point_injective
    rw [pointPermutation_spec, pointPermutation_spec, pointPermutation_spec]
    rfl

theorem quarticStabilizerToDesignAut_injective
    (hrecognition : ∀ v : U, rankDistribution quartic v = pointDistribution ↔
      v ∈ Set.range point)
    (hhex : ∀ B : Finset (Fin 22), B ∈ m22Blocks ↔ IsHexad B) :
    Function.Injective (quarticStabilizerToDesignAut hrecognition hhex) := by
  intro g h heq
  apply Subtype.ext
  apply pointPermutation_injective (permutesPoints_of_preserves hrecognition g.property)
    (permutesPoints_of_preserves hrecognition h.property)
  exact congrArg Subtype.val heq

/-- Image bound for any linear-equivalence representation preserving the quartic.
No faithfulness assumption on the original group is required for an image bound. -/
theorem linearEquiv_range_card_le_of_certificates {G : Type*} [Group G]
    (ρ : G →* (U ≃ₗ[F] U)) (hρ : ∀ g, Preserves quartic (ρ g))
    (hrecognition : ∀ v : U, rankDistribution quartic v = pointDistribution ↔
      v ∈ Set.range point)
    (hhex : ∀ B : Finset (Fin 22), B ∈ m22Blocks ↔ IsHexad B) :
    Nat.card ρ.range ≤ 887040 := by
  apply card_le_of_configuration (ρ.range : Set (U ≃ₗ[F] U))
  · rintro _ ⟨g, rfl⟩
    exact permutesPoints_of_preserves hrecognition (hρ g)
  · exact hhex

/-- A basis-calibrated interface for the actual action on an intrinsic vector
space. The tensor, its calibration, and preservation by the whole acting group
are explicit; the image bound does not require the action to be faithful. -/
theorem calibrated_range_card_le_of_certificates {G V : Type*} [Group G]
    [AddCommGroup V] [Module F V]
    (ρ : G →* (Module.End F V)ˣ) (b : V ≃ₗ[F] U)
    (Q : V [⋀^Fin 4]→ₗ[F] F)
    (hcalibration : ∀ v w x y, quartic ![b v, b w, b x, b y] = Q ![v, w, x, y])
    (hρ : ∀ g v w x y,
      Q ![(ρ g).val v, (ρ g).val w, (ρ g).val x, (ρ g).val y] = Q ![v, w, x, y])
    (hrecognition : ∀ v : U, rankDistribution quartic v = pointDistribution ↔
      v ∈ Set.range point)
    (hhex : ∀ B : Finset (Fin 22), B ∈ m22Blocks ↔ IsHexad B) :
    Nat.card ρ.range ≤ 887040 := by
  let e : (Module.End F V)ˣ ≃* (U ≃ₗ[F] U) :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F U)
  let σ : G →* (U ≃ₗ[F] U) := e.toMonoidHom.comp ρ
  have hc : Nat.card ρ.range = Nat.card σ.range := by
    rw [show σ = e.toMonoidHom.comp ρ from rfl, MonoidHom.range_comp]
    exact Nat.card_congr (e.subgroupMap ρ.range).toEquiv
  rw [hc]
  apply linearEquiv_range_card_le_of_certificates σ _ hrecognition hhex
  intro g v w x y
  change quartic ![b ((ρ g).val (b.symm v)), b ((ρ g).val (b.symm w)),
    b ((ρ g).val (b.symm x)), b ((ρ g).val (b.symm y))] = quartic ![v, w, x, y]
  rw [hcalibration, hρ, ← hcalibration]
  simp only [LinearEquiv.apply_symm_apply]

end BinaryQuarticMathieu
