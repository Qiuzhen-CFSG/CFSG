module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Outer.Witness
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The split extension and its embedded two-residual

Every outer involution in the nonsingular stabilizer complements its normal
inner subgroup. This constructs the internal semidirect product with the
actual conjugation action. Perfectness of the inner subgroup and the quotient
of order two identify the two-residual, both intrinsically and in the original
automorphism group.

Source: Aschbacher–Smith, H.9.1(4), printed pp.389–390.
-/

@[expose] public section
namespace BinaryNaturalDual.VectorStabilizers
open BinaryLinear.OuterCyclic

private theorem one_or_generator_of_sq {G : Type*} [Group G]
    (g : G) (hg : g ^ 2 = 1) {a : G} (ha : a ∈ Subgroup.zpowers g) :
    a = 1 ∨ a = g := by
  have hg' : g * g = 1 := by simpa only [pow_two] using hg
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_left hg'
  let K : Subgroup G :=
    { carrier := {a | a = 1 ∨ a = g}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl) (rfl | rfl) <;> simp [hg']
      inv_mem' := by
        rintro a (rfl | rfl) <;> simp [hgi] }
  exact (Subgroup.zpowers_le.mpr (show g ∈ K from Or.inr rfl)) ha

/-- Any outer involution complements the actual inner nonsingular stabilizer. -/
theorem outer_isComplement {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1)
    (s : fullStabilizer d (x,f)) (hout : s.val ∉ MulAut.innerSubgroup (LinearGroup n))
    (hsq : s ^ 2 = 1) : (innerInFull d (x,f)).IsComplement' (Subgroup.zpowers s) := by
  have hs : s ∉ innerInFull d (x,f) := by simpa using hout
  have hd : Disjoint (innerInFull d (x,f)) (Subgroup.zpowers s) := by
    apply Subgroup.disjoint_def.mpr
    intro a ha hpa
    rcases one_or_generator_of_sq s hsq hpa with rfl | rfl
    · rfl
    · exact False.elim (hs ha)
  refine ⟨Subgroup.mul_injective_of_disjoint hd, ?_⟩
  intro a
  by_cases ha : a ∈ innerInFull d (x,f)
  · exact ⟨(⟨a, ha⟩, 1), mul_one a⟩
  · have has : a * s ∈ innerInFull d (x,f) :=
      (Subgroup.mul_mem_iff_of_index_two (innerInFull_index hn d h)).mpr
        (iff_of_false ha hs)
    refine ⟨(⟨a * s, has⟩, ⟨s, Subgroup.mem_zpowers s⟩), ?_⟩
    change a * s * s = a
    rw [mul_assoc, ← pow_two, hsq, mul_one]

/-- The actual semidirect-product isomorphism, with its conjugation action. -/
noncomputable def outerSemidirectEquiv {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1)
    (s : fullStabilizer d (x,f)) (hout : s.val ∉ MulAut.innerSubgroup (LinearGroup n))
    (hsq : s ^ 2 = 1) :
    (innerInFull d (x,f)) ⋊[(innerInFull d (x,f)).normalizerMonoidHom.comp
      (Subgroup.inclusion ((innerInFull d (x,f)).normalizer_eq_top ▸ le_top))]
      (Subgroup.zpowers s) ≃* fullStabilizer d (x,f) :=
  SemidirectProduct.mulEquivSubgroup (outer_isComplement hn d h s hout hsq)

/-- The intrinsic two-residual of the full stabilizer is exactly its inner subgroup. -/
theorem fullStabilizer_twoResidual {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    pResidual 2 (fullStabilizer d (x,f)) = innerInFull d (x,f) := by
  apply Subgroup.pResidual_eq_of_isPPerfect
  · exact ((pResidual_eq_top_iff 2 _).mp (innerStabilizer_twoResidual hn d h)).of_surjective
      (innerInFullEquiv d (x,f)).symm.toMonoidHom (innerInFullEquiv d (x,f)).symm.surjective
  · apply IsPGroup.of_card (n := 1)
    exact innerInFull_index hn d h

/-- The embedded `O²(C_M(v))` is the published inner stabilizer in the actual `M`. -/
theorem fullStabilizer_embedded_twoResidual {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    (pResidual 2 (fullStabilizer d (x,f))).map (fullStabilizer d (x,f)).subtype =
      innerStabilizer d (x,f) := by
  rw [fullStabilizer_twoResidual hn d h]
  exact Subgroup.map_subgroupOf_eq_of_le inf_le_right

end BinaryNaturalDual.VectorStabilizers
