module
public import Theory.SpecificGroups.GL2.DiagonalSwap
public import ABG.ChapterII.Section1.WreathedCenter

/-!
# Wreathed structure of the shared monomial subgroup

A unit of exact order 2^n with n at least two generates, through the two
diagonal matrices and coordinate swap, the actual wreathed group of height
n. The image of its center lies in the center of the ambient GL2 group.

The raw monomial cardinality and matrix identities give the prescribed
ABG wreathed presentation. The source center theorem identifies its center
with the powers of the product of the diagonal generators; this product
is precisely the scalar matrix defined by the unit.

This is the common model for the linear and unitary Sylow constructions
in ABG II.2 Lemma1(i),(ii), article p17. It proves the exact presentation
and center statement; containment and Sylow maximality in each determinant
level are left to their separate, model-specific assemblies.
-/

namespace ABG
open Matrix.GeneralLinearGroup

public theorem diagonalSwap_wreathed_model
    (F : Type*) [Field F] (ζ : Fˣ) (n : ℕ) (hn : 2 ≤ n)
    (horder : orderOf ζ = 2 ^ n) :
    IsWreathedOfHeight (diagonalSwapSubgroup F ζ) n ∧
      (Subgroup.center (diagonalSwapSubgroup F ζ)).map (diagonalSwapSubgroup F ζ).subtype ≤
        Subgroup.center (GL (Fin 2) F) := by
  let W := diagonalSwapSubgroup F ζ
  let s : W := ⟨diagonalPair F (ζ,1), Subgroup.subset_closure (by simp)⟩
  let t : W := ⟨diagonalPair F (1,ζ), Subgroup.subset_closure (by simp)⟩
  let z : W := ⟨coordinateSwap F, Subgroup.subset_closure (by simp)⟩
  have hc : Nat.card W = 2 ^ (2 * n + 1) := by
    rw [diagonalSwapSubgroup_card, horder]
    simp only [← pow_mul, pow_add, pow_one, Nat.mul_comm]
  have hζ : ζ ^ (2 ^ n) = 1 := by rw [← horder]; exact pow_orderOf_eq_one ζ
  have hs : s ^ (2 ^ n) = 1 := by
    apply Subtype.ext
    change diagonalPair F (ζ,1) ^ (2 ^ n) = 1
    rw [← map_pow]
    rw [show (ζ, (1 : Fˣ)) ^ (2 ^ n) = 1 by ext <;> simp [hζ], map_one]
  have ht : t ^ (2 ^ n) = 1 := by
    apply Subtype.ext
    change diagonalPair F (1,ζ) ^ (2 ^ n) = 1
    rw [← map_pow]
    rw [show ((1 : Fˣ), ζ) ^ (2 ^ n) = 1 by ext <;> simp [hζ], map_one]
  have hz : z ^ 2 = 1 := Subtype.ext (coordinateSwap_sq F)
  have hzs : z⁻¹ * s * z = t := by
    apply Subtype.ext
    change (coordinateSwap F)⁻¹ * diagonalPair F (ζ,1) * coordinateSwap F = diagonalPair F (1,ζ)
    exact (by simpa only [coordinateSwap_inv] using coordinateSwap_conj_diagonalPair F ζ 1)
  have hzt : z⁻¹ * t * z = s := by
    apply Subtype.ext
    change (coordinateSwap F)⁻¹ * diagonalPair F (1,ζ) * coordinateSwap F = diagonalPair F (ζ,1)
    exact (by simpa only [coordinateSwap_inv] using coordinateSwap_conj_diagonalPair F 1 ζ)
  have hst : s * t = t * s := by
    apply Subtype.ext
    change diagonalPair F (ζ,1) * diagonalPair F (1,ζ) = diagonalPair F (1,ζ) * diagonalPair F (ζ,1)
    rw [← map_mul, ← map_mul]
    simp
  have hgen : Subgroup.closure ({s,t,z} : Set W) = ⊤ := by
    apply Subgroup.map_injective W.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, W.range_subtype]
    simp only [Set.image_insert_eq, Set.image_singleton]
    rfl
  let P : Wreathed.Presentation W n := ⟨hn, hc, s, t, z, hs, ht, hz, hzs, hzt, hst, hgen⟩
  refine ⟨⟨hn, hc, s, t, z, hs, ht, hz, hzs, hzt, hst, hgen⟩, ?_⟩
  rw [P.center_eq_zpowers, MonoidHom.map_zpowers]
  apply Subgroup.zpowers_le.mpr
  have hu : W.subtype P.u = scalar (Fin 2) ζ := by
    change diagonalPair F (ζ,1) * diagonalPair F (1,ζ) = _
    rw [← map_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonalPair, coe_scalar, Matrix.scalar_apply]
  rw [hu]
  exact Subgroup.mem_center_iff.mpr (fun A => (scalar_commute ζ A).symm)

end ABG

