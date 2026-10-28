module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.SplitCore

/-!
# Representative-independent split intersections

Right conjugation is `A^n = n⁻¹ A n`, implemented by comap under `conj n`.
The torus H = B ∩ N normalizes each conjugate of U and each intersection
`U ∩ U^(n₀*n)`. These groups depend only on the two Weyl classes.

For finite split BN-pairs the normal Sylow subgroup U of B contains every
two-subgroup of B. Thus `B ∩ U^n = U ∩ U^n`, and factoring B^n gives
`B ∩ B^n = (U ∩ U^n) H`. The two factors are disjoint, so multiplication
gives unique coordinates as types and the corresponding cardinality formula.

Source: Carter, §2.5, notation preceding Proposition 2.5.1 and Proposition
2.5.9, in `refs/KGroup/GLS3/Chapter2Ca2.tex`. The finite proof uses the
normal Sylow subgroup instead of algebraic unipotence. The parameter w₀
in `rootIntersection` is arbitrary here; no longest-element assertion or
root factorization is encoded in its definition.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {X : Type*} [Group X]

/-- Right conjugation, so `(A^n)^m = A^(n*m)`. -/
@[expose] def rightConjugate (A : Subgroup X) (n : X) : Subgroup X :=
  A.comap (MulAut.conj n).toMonoidHom

/-- The order of the two conjugating factors is preserved. -/
theorem rightConjugate_mul (A : Subgroup X) (n m : X) :
    rightConjugate A (n * m) = rightConjugate (rightConjugate A n) m := by
  ext x
  change (n * m) * x * (n * m)⁻¹ ∈ A ↔ n * (m * x * m⁻¹) * n⁻¹ ∈ A
  simp only [mul_inv_rev, mul_assoc]

@[simp] theorem rightConjugate_one (A : Subgroup X) : rightConjugate A 1 = A := by
  ext x
  change 1 * x * (1 : X)⁻¹ ∈ A ↔ x ∈ A
  simp

theorem rightConjugate_eq_self (A : Subgroup X) {n : X}
    (hn : n ∈ normalizer (A : Set X)) : rightConjugate A n = A := by
  ext x
  exact (mem_normalizer_iff.mp hn x).symm

variable {T : TitsSystem (X := X)}

theorem torus_normalizes (n : T.N) :
    (n : X) ∈ normalizer ((T.B ⊓ T.N : Subgroup X) : Set X) :=
  (normal_subgroupOf_iff_le_normalizer inf_le_right).mp T.intersection_normal n.property

theorem torus_conjugate (n : T.N) :
    rightConjugate (T.B ⊓ T.N) (n : X) = T.B ⊓ T.N :=
  rightConjugate_eq_self _ (torus_normalizes n)

theorem rightConjugate_eq_of_quotient_eq (A : Subgroup X)
    (hA : T.B ⊓ T.N ≤ normalizer (A : Set X)) (n m : T.N)
    (h : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n =
      QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) m) :
    rightConjugate A (n : X) = rightConjugate A (m : X) := by
  have hh : n * m⁻¹ ∈ (T.B ⊓ T.N).subgroupOf T.N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) (n * m⁻¹) = 1
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hn : ((n : X) * (m : X)⁻¹) ∈ normalizer (A : Set X) := hA hh
  calc
    rightConjugate A (n : X) =
        rightConjugate A (((n : X) * (m : X)⁻¹) * (m : X)) := by simp
    _ = rightConjugate (rightConjugate A ((n : X) * (m : X)⁻¹)) (m : X) :=
      rightConjugate_mul _ _ _
    _ = rightConjugate A (m : X) := by rw [rightConjugate_eq_self A hn]

theorem torus_normalizes_rightConjugate (A : Subgroup X)
    (hA : T.B ⊓ T.N ≤ normalizer (A : Set X)) (n : T.N) :
    T.B ⊓ T.N ≤ normalizer (rightConjugate A (n : X) : Set X) := by
  apply le_trans ?_ (le_normalizer_comap (H := A) (MulAut.conj (n : X)).toMonoidHom)
  intro h hh
  apply hA
  exact (mem_normalizer_iff.mp (torus_normalizes n) h).mp hh

variable (split : SplitData T)

/-- A choice of lift in the actual N. All subgroup formulas are independent of it. -/
def representative (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) : T.N :=
  (QuotientGroup.mk'_surjective ((T.B ⊓ T.N).subgroupOf T.N) w).choose

@[simp] theorem representative_spec (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) :
    QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) (representative w) = w :=
  (QuotientGroup.mk'_surjective ((T.B ⊓ T.N).subgroupOf T.N) w).choose_spec

/-- The conjugate of the specified U by a Weyl class. -/
@[expose] def unipotentConjugate (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) : Subgroup X :=
  rightConjugate split.U (representative w : X)

theorem unipotentConjugate_eq (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N)
    (n : T.N) (hn : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n = w) :
    unipotentConjugate split w = rightConjugate split.U (n : X) :=
  rightConjugate_eq_of_quotient_eq split.U
    (inf_le_left.trans split.normalizes) (representative w) n
    ((representative_spec w).trans hn.symm)

theorem torus_normalizes_unipotentConjugate (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) :
    T.B ⊓ T.N ≤ normalizer (unipotentConjugate split w : Set X) :=
  torus_normalizes_rightConjugate split.U (inf_le_left.trans split.normalizes)
    (representative w)

/-- Carter’s literal intersection, with the proposed opposite class explicit. -/
@[expose] def rootIntersection
    (w₀ w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) : Subgroup X :=
  split.U ⊓ unipotentConjugate split (w₀ * w)

theorem rootIntersection_eq
    (w₀ w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) (n₀ n : T.N)
    (h₀ : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n₀ = w₀)
    (hn : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n = w) :
    rootIntersection split w₀ w = split.U ⊓
      split.U.comap (MulAut.conj ((n₀ : X) * (n : X))).toMonoidHom := by
  rw [rootIntersection, unipotentConjugate_eq split (w₀ * w) (n₀ * n)
    (by rw [map_mul, h₀, hn])]
  rfl

theorem torus_normalizes_rootIntersection
    (w₀ w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) :
    T.B ⊓ T.N ≤ normalizer (rootIntersection split w₀ w : Set X) :=
  (le_inf (inf_le_left.trans split.normalizes)
    (torus_normalizes_unipotentConjugate split (w₀ * w))).trans
      inf_normalizer_le_normalizer_inf

theorem rootIntersection_isTwo
    (w₀ w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) :
    IsPGroup 2 (rootIntersection split w₀ w) :=
  split.isTwo.of_injective (inclusion inf_le_left) (inclusion_injective _)


/-- Every two-subgroup contained in B lies in its specified normal Sylow subgroup. -/
theorem two_subgroup_le_unipotent [Finite X] (K : Subgroup X)
    (hK : IsPGroup 2 K) (hKB : K ≤ T.B) : K ≤ split.U := by
  let U := split.U.subgroupOf T.B
  let K' := K.subgroupOf T.B
  let : U.Normal := normal_subgroupOf_of_le_normalizer split.normalizes
  have hU : IsPGroup 2 U := split.isTwo.comap_subtype
  let P := hU.toSylow split.borel_index_not_two
  have hjoin : K' ⊔ U = U :=
    P.is_maximal' (hK.comap_subtype.to_sup_of_normal_right hU) le_sup_right
  have hKU : K' ≤ U := hjoin ▸ le_sup_left
  intro x hx
  exact hKU (show (⟨x, hKB hx⟩ : T.B) ∈ K' from hx)

theorem borel_inf_unipotent_conjugate [Finite X] (n : T.N) :
    T.B ⊓ rightConjugate split.U (n : X) =
      split.U ⊓ rightConjugate split.U (n : X) := by
  apply le_antisymm
  · exact le_inf
      (two_subgroup_le_unipotent split _
        (split.isTwo.comap_of_injective (MulAut.conj (n : X)).toMonoidHom
          (MulAut.conj (n : X)).injective).to_inf_right inf_le_left)
      inf_le_right
  · exact inf_le_inf_right _ split.U_le

theorem borel_conjugate_factorization (n : T.N) :
    (rightConjugate T.B (n : X) : Set X) =
      (rightConjugate split.U (n : X) : Set X) * (T.B ⊓ T.N : Subgroup X) := by
  have he : rightConjugate T.B (n : X) =
      rightConjugate split.U (n : X) ⊔ (T.B ⊓ T.N) := by
    conv_lhs => rw [← split.factorization]
    unfold rightConjugate
    rw [← comap_sup_eq (MulAut.conj (n : X)).toMonoidHom _ _
      (MulAut.conj (n : X)).surjective]
    rw [show (T.B ⊓ T.N).comap (MulAut.conj (n : X)).toMonoidHom = T.B ⊓ T.N from
      torus_conjugate n]
  rw [he]
  exact coe_mul_of_right_le_normalizer_left _ _
    (torus_normalizes_rightConjugate split.U (inf_le_left.trans split.normalizes) n)

/-- Carter 2.5.9, with an arbitrary representative in the actual N. -/
theorem borel_intersection_factorization [Finite X] (n : T.N) :
    ((T.B ⊓ rightConjugate T.B (n : X) : Subgroup X) : Set X) =
      ((split.U ⊓ rightConjugate split.U (n : X) : Subgroup X) : Set X) *
        (T.B ⊓ T.N : Subgroup X) := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, h, hh, he⟩ :=
      (borel_conjugate_factorization split n) ▸ hx.2
    have huB : u ∈ T.B := by
      have := T.B.mul_mem hx.1 (T.B.inv_mem hh.1)
      rw [← he, mul_inv_cancel_right] at this
      exact this
    have huU : u ∈ split.U :=
      ((borel_inf_unipotent_conjugate split n) ▸ (show u ∈ T.B ⊓
        rightConjugate split.U (n : X) from ⟨huB, hu⟩)).1
    exact ⟨u, ⟨huU, hu⟩, h, hh, he⟩
  · rintro ⟨u, hu, h, hh, rfl⟩
    refine ⟨T.B.mul_mem (split.U_le hu.1) hh.1, ?_⟩
    change u * h ∈ (rightConjugate T.B (n : X) : Set X)
    rw [borel_conjugate_factorization split n]
    exact ⟨u, hu.2, h, hh, rfl⟩


theorem unipotent_disjoint_torus [Finite X] : Disjoint split.U (T.B ⊓ T.N) :=
  (disjoint_iff.mpr split.unipotent_inf_N).mono_right inf_le_right

private def intersectionMul (n : T.N) :
    (split.U ⊓ rightConjugate split.U (n : X) : Subgroup X) ×
      (T.B ⊓ T.N : Subgroup X) → (T.B ⊓ rightConjugate T.B (n : X) : Subgroup X) :=
  fun x => ⟨(x.1 : X) * (x.2 : X), by
    refine ⟨T.B.mul_mem (split.U_le x.1.property.1) x.2.property.1, ?_⟩
    change (x.1 : X) * (x.2 : X) ∈ (rightConjugate T.B (n : X) : Set X)
    rw [borel_conjugate_factorization split n]
    exact ⟨x.1, x.1.property.2, x.2, x.2.property, rfl⟩⟩

private theorem intersectionMul_bijective [Finite X] (n : T.N) :
    Function.Bijective (intersectionMul split n) := by
  constructor
  · intro x y hxy
    exact mul_injective_of_disjoint ((unipotent_disjoint_torus split).mono_left
      inf_le_left) (congrArg Subtype.val hxy)
  · intro x
    have hx : (x : X) ∈
        ((split.U ⊓ rightConjugate split.U (n : X) : Subgroup X) : Set X) *
          (T.B ⊓ T.N : Subgroup X) :=
      (borel_intersection_factorization split n) ▸ x.property
    obtain ⟨u, hu, h, hh, he⟩ := hx
    exact ⟨(⟨u, hu⟩, ⟨h, hh⟩), Subtype.ext he⟩

/-- Unique multiplication coordinates as types; no commutation of factors is asserted. -/
def intersectionCoordinates [Finite X] (n : T.N) :
    (split.U ⊓ rightConjugate split.U (n : X) : Subgroup X) ×
      (T.B ⊓ T.N : Subgroup X) ≃ (T.B ⊓ rightConjugate T.B (n : X) : Subgroup X) :=
  Equiv.ofBijective (intersectionMul split n) (intersectionMul_bijective split n)

@[simp] theorem intersectionCoordinates_apply [Finite X] (n : T.N)
    (u : (split.U ⊓ rightConjugate split.U (n : X) : Subgroup X))
    (h : (T.B ⊓ T.N : Subgroup X)) :
    (intersectionCoordinates split n (u, h) : X) = (u : X) * (h : X) := by
  rfl

theorem borel_intersection_card [Finite X] (n : T.N) :
    Nat.card (T.B ⊓ rightConjugate T.B (n : X) : Subgroup X) =
      Nat.card (split.U ⊓ rightConjugate split.U (n : X) : Subgroup X) *
        Nat.card (T.B ⊓ T.N : Subgroup X) := by
  rw [← Nat.card_congr (intersectionCoordinates split n), Nat.card_prod]

/-- The split factorization counts the whole Borel, including all of H. -/
theorem borel_card [Finite X] :
    Nat.card T.B = Nat.card split.U * Nat.card (T.B ⊓ T.N : Subgroup X) := by
  simpa only [Subgroup.coe_one, rightConjugate_one, inf_idem] using
    borel_intersection_card split 1

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
