module
public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.JankoLocal
public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.JankoElementary.Coefficients
public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.JankoElementary.Lifts

/-!
# Elementary core preimages in the literal Mathieu local group of J4

In a central double extension, squares of lifts of the elementary core are
independent of the lifts. Collection expresses them as a binary quadratic
polynomial. The certified right-conjugation tables force every coefficient to
vanish. Thus every element over the core squares to one, without a perfectness,
splitting, or multiplier hypothesis on the local extension.

The last theorem applies this calculation to the literal restriction of a
perfect central J4 cover. It supplies precisely the elementary-preimage input
of `JankoReduction.kernel_not_two_of_local_calculations`; the independent
invariant-complement calculation remains with the final assembly owner.

Source: Aschbacher--Smith I.1.1--I.1.3, printed p.407, and GLS3 Section 6.1.
The concrete action uses the certified ATLAS `J4G1-max1W1` words and tables.
-/

public section
namespace Janko4.TwoPrimary
open Subgroup Cardinality Cardinality.KernelCount
open JankoElementary
universe u

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localX localY localKernelSeed basis

private theorem polynomial_invariant
    {L : Type*} [Group L] (q : L →* Local) (hq : Function.Surjective q)
    (hc : q.ker ≤ center L) (hk : Nat.card q.ker = 2)
    (e : Fin 11 → L) (he : ∀ i, q (e i) = basis matrixA_mul_self matrixB_pow_four i)
    (t : L) (ht : t ≠ 1) (htc : t ∈ center L)
    (s : Fin 11 → Bool) (b : Fin 11 → Fin 11 → Bool)
    (hsq : ∀ v, binaryProduct e v ^ 2 = bit t (quadratic s b v))
    (g : Local) (a : Fin 11 → ℕ)
    (hga : ∀ i, g⁻¹ * basis matrixA_mul_self matrixB_pow_four i * g =
      binaryProduct (basis matrixA_mul_self matrixB_pow_four) (mask (a i))) :
    TableInvariant (quadratic s b) a := by
  let B := basis matrixA_mul_self matrixB_pow_four
  have hmap (v : Fin 11 → Bool) : q (binaryProduct e v) = binaryProduct B v := by
    rw [map_binaryProduct]
    congr 1
    funext i
    exact he i
  have hu (i : Fin 11) : binaryProduct B (single i) = B i :=
    binaryProduct_single B i
  have hconj (v w : Fin 11 → Bool)
      (h : g⁻¹ * q (binaryProduct e v) * g = q (binaryProduct e w)) :
      quadratic s b v = quadratic s b w := by
    apply bit_injective t ht
    rw [← hsq, ← hsq]
    apply q.square_eq_of_isConj_map_of_central_binary_kernel hq hc (kernel_square q hk)
    · rw [hsq]
      cases quadratic s b v <;> simp [bit, htc]
    · exact isConj_iff.mpr ⟨g⁻¹, by simpa only [inv_inv] using h⟩
  constructor
  · intro i
    apply (hconj (single i) (mask (a i)) ?_).symm
    rw [hmap, hmap, hu]
    exact hga i
  · intro i j
    apply (hconj (add (single i) (single j)) (add (mask (a i)) (mask (a j))) ?_).symm
    rw [hmap, hmap]
    have hm (v w : Fin 11 → Bool) :
        binaryProduct B (add v w) = binaryProduct B v * binaryProduct B w :=
      (binaryProduct_mul B (basis_square _ _) (basis_commute _ _) v w).symm
    rw [hm, hm, hu, hu]
    calc
      g⁻¹ * (B i * B j) * g = (g⁻¹ * B i * g) * (g⁻¹ * B j * g) := by group
      _ = _ := by rw [hga i, hga j]

/-- Every central double extension of the actual max1 local group has elementary
preimage of its certified core. -/
theorem elementaryPreimageCalculation : ElementaryPreimageCalculation.{u} := by
  intro L _ _ q hq hc hk
  classical
  let e : Fin 11 → L := fun i => (hq (basis matrixA_mul_self matrixB_pow_four i)).choose
  have he (i : Fin 11) : q (e i) = basis matrixA_mul_self matrixB_pow_four i :=
    (hq _).choose_spec
  obtain ⟨t, s, b, ht, htc, ht2, hs, hb⟩ := exists_coefficients q hc hk e
    (fun i => by rw [he]; exact basis_square _ _ i)
    (fun i j => by rw [he, he]; exact basis_commute _ _ i j)
  have hsq := word_square e s b t htc ht2 hs hb
  have hx : TableInvariant (quadratic s b) xMasks :=
    polynomial_invariant q hq hc hk e he t ht htc s b hsq
      (localX _ _) xMasks (basis_conj_x _ _)
  have hy : TableInvariant (quadratic s b) yMasks :=
    polynomial_invariant q hq hc hk e he t ht htc s b hsq
      (localY _ _) yMasks (basis_conj_y _ _)
  intro x hxcore
  obtain ⟨v, hv⟩ :=
    (QuotientCount.Image.mem_localKernel_iff_binaryProduct _ _ (q x)).mp hxcore
  have hmap : q (binaryProduct e v) = q x := by
    rw [map_binaryProduct]
    convert hv using 1
    congr 1
    funext i
    exact he i
  calc
    x ^ 2 = binaryProduct e v ^ 2 :=
      q.square_eq_of_map_eq_of_central_binary_kernel hc (kernel_square q hk) hmap.symm
    _ = bit t (quadratic s b v) := hsq v
    _ = 1 := by rw [invariant_quadratic_zero s b hx hy v]; rfl

/-- Application to the actual local restriction of a perfect central J4 cover. -/
theorem localProjection_elementaryPreimage
    {E : Type u} [Group E] [Finite E] (f : PerfectCentralCovering.Cover E Model)
    (hk : Nat.card f.toMonoidHom.ker = 2) : ElementaryPreimage (localProjection f) := by
  apply elementaryPreimageCalculation _ (localProjection f)
  · exact f.toMonoidHom.subgroupComap_surjective_of_surjective Local f.surjective
  · intro x hx
    exact mem_center_iff.mpr fun y => Subtype.ext
      (mem_center_iff.mp (f.ker_le_center (congrArg Subtype.val hx)) y)
  · exact (localProjection_kernel_card f).trans hk

end Janko4.TwoPrimary
