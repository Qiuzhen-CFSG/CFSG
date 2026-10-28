module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Geometry.Parameters
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Geometry.SignedExterior

/-!
# Signed coordinates on the original minus-six space

The plane map (x,y) ↦ ι(x)−αι(y) preserves its anisotropic norm, hence
is injective. Cardinality makes it surjective onto the quadratic extension.
The complete signed chart is therefore injective and identifies the original
space with the fixed vectors of the signed Frobenius involution. Its image
spans all six bivectors over the extension: the four hyperbolic coordinates
are individual basis vectors up to nonzero scalars, and the plane vectors
at 1 and α separate the remaining two coordinates.

The Pfaffian restricts to the exact original quadratic form, supplying the
coordinate part of the exterior realization used in Aschbacher–Smith
A.2.17, printed pp.38–39, and GLS3 §2.7. No independently chosen minus
parameter or quadratic-form classification is used.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Minus.OddSixComparison.Geometry
open Atlas.Order20160A8.Bivectors
variable (p n : ℕ) [Fact p.Prime] [NeZero n]
variable (F : Type) [Field F] [Finite F] (hcard : Nat.card F = p ^ n)

local notation "ι" => coefficient p n F hcard
local notation "α" => root p n F hcard
local notation "σ" => conjugation p n
local notation "t" => 2 * α + 1

def planeMap : (F × F) →ₛₗ[ι] Extension p n where
  toFun v := ι v.1 - α * ι v.2
  map_add' v w := by simp; ring
  map_smul' c v := by simp [smul_eq_mul]; ring

@[simp] theorem planeMap_apply (v : F × F) : planeMap p n F hcard v = ι v.1 - α * ι v.2 := rfl

theorem planeMap_norm (v : F × F) :
    planeMap p n F hcard v * σ (planeMap p n F hcard v) = ι (plane F (parameter F) v) :=
  norm_plane_coordinates ι σ α (coefficient_fixed p n F hcard)
    (root_equation p n F hcard) (root_conjugate p n F hcard) v.1 v.2

theorem planeMap_injective : Function.Injective (planeMap p n F hcard) := by
  intro v w h
  have hz : planeMap p n F hcard (v - w) = 0 := by rw [map_sub, h, sub_self]
  apply sub_eq_zero.mp
  apply plane_anisotropic F (parameter F) (parameter_spec F)
  apply (ι).injective
  rw [← planeMap_norm, hz, map_zero, mul_zero, map_zero]

theorem planeMap_surjective : Function.Surjective (planeMap p n F hcard) := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (Extension p n) := Fintype.ofFinite _
  apply ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨planeMap_injective p n F hcard, ?_⟩).2
  simp only [← Nat.card_eq_fintype_card, Nat.card_prod, hcard, card_extension, pow_two]

def coordinates : Space F 2 →ₛₗ[ι] Six (Extension p n) where
  toFun := signedBivectors ι σ α
  map_add' v w := by
    ext i
    fin_cases i <;> simp [signedBivectors, map_sub, map_mul, map_add] <;> ring
  map_smul' c v := by
    ext i
    fin_cases i <;>
      simp [signedBivectors, smul_eq_mul, map_sub, map_mul, coefficient_fixed] <;> ring

@[simp] theorem coordinates_apply (v : Space F 2) :
    coordinates p n F hcard v = signedBivectors ι σ α v := rfl

theorem coordinates_injective : Function.Injective (coordinates p n F hcard) := by
  intro v w h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  simp only [coordinates_apply, signedBivectors, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at h0 h1 h4 h5
  apply Prod.ext
  · funext i
    fin_cases i
    · exact Prod.ext ((ι).injective h0) ((ι).injective h5)
    · exact Prod.ext ((ι).injective (mul_left_cancel₀ (skew_ne_zero p n F hcard) h1))
        ((ι).injective (mul_left_cancel₀ (inv_ne_zero (skew_ne_zero p n F hcard))
          (neg_injective h4)))
  · apply planeMap_injective p n F hcard
    exact congrFun h 2

theorem coordinates_quadratic (v : Space F 2) :
    pfaffian (coordinates p n F hcard v) = ι (quadraticForm F 3 v) :=
  pfaffian_signedBivectors ι σ α (coefficient_fixed p n F hcard)
    (root_equation p n F hcard) (root_conjugate p n F hcard) (skew_ne_zero p n F hcard) v

theorem conjugation_skew : σ t = -t := by
  simp only [map_add, map_mul, map_ofNat, map_one, root_conjugate]
  ring

theorem coordinates_fixed (v : Space F 2) :
    signedTwist p n (coordinates p n F hcard v) = coordinates p n F hcard v := by
  have hσσ (z : Extension p n) : σ (σ z) = z := conjugation_involutive p n z
  simp only [signedTwist, coordinates_apply, signedBivectors, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, map_mul, map_neg, map_inv₀,
      coefficient_fixed, conjugation_skew, hσσ,
      inv_neg, neg_mul, neg_neg]

theorem mem_range_coordinates_iff (w : Six (Extension p n)) :
    w ∈ Set.range (coordinates p n F hcard) ↔ signedTwist p n w = w := by
  constructor
  · rintro ⟨v, rfl⟩
    exact coordinates_fixed p n F hcard v
  · intro hw
    have h0 : σ (w 0) = w 0 := congrFun hw 0
    have h1 : σ (w 1) = -w 1 := neg_eq_iff_eq_neg.mp (congrFun hw 1)
    have h4 : σ (w 4) = -w 4 := neg_eq_iff_eq_neg.mp (congrFun hw 4)
    have h5 : σ (w 5) = w 5 := congrFun hw 5
    have h23 : σ (w 2) = w 3 := congrFun hw 3
    obtain ⟨a, ha⟩ := exists_coefficient p n F hcard (w 0) h0
    obtain ⟨b, hb⟩ := exists_coefficient p n F hcard (w 5) h5
    obtain ⟨c, hc⟩ := exists_coefficient p n F hcard (w 1 / t) (by
      rw [map_div₀, h1, conjugation_skew, neg_div_neg_eq])
    obtain ⟨d, hd⟩ := exists_coefficient p n F hcard (-t * w 4) (by
      rw [map_mul, map_neg, conjugation_skew, h4]; ring)
    obtain ⟨z, hz⟩ := planeMap_surjective p n F hcard (w 2)
    have hz' : ι z.1 - α * ι z.2 = w 2 := hz
    refine ⟨(![(a,b),(c,d)],z), ?_⟩
    ext i
    fin_cases i <;>
      simp [coordinates, signedBivectors, ha, hb, hc, hd, hz', h23]
    · field_simp [skew_ne_zero p n F hcard]
    · field_simp [skew_ne_zero p n F hcard]
      ring

theorem coordinates_span :
    Submodule.span (Extension p n) (Set.range (coordinates p n F hcard)) = ⊤ := by
  let S := Submodule.span (Extension p n) (Set.range (coordinates p n F hcard))
  have hv (v : Space F 2) : coordinates p n F hcard v ∈ S :=
    Submodule.subset_span ⟨v, rfl⟩
  have hz (z : Extension p n) : (![0, 0, z, σ z, 0, 0] : Six (Extension p n)) ∈ S := by
    obtain ⟨v, hv'⟩ := planeMap_surjective p n F hcard z
    have hv'' : ι v.1 - α * ι v.2 = z := hv'
    convert hv (0, v) using 1
    ext i
    fin_cases i <;> simp [coordinates, signedBivectors, hv'']
  have hden : σ α - α ≠ 0 := sub_ne_zero.mpr (root_not_fixed p n F hcard)
  have he3 : (Pi.single 3 (1 : Extension p n) : Six (Extension p n)) =
      (σ α - α)⁻¹ • ![0, 0, α, σ α, 0, 0] -
        (α / (σ α - α)) • ![0, 0, 1, 1, 0, 0] := by
    ext i
    fin_cases i <;> simp [div_eq_mul_inv]
    · ring
    · field_simp
  have h3 : (Pi.single 3 (1 : Extension p n) : Six (Extension p n)) ∈ S := by
    rw [he3]
    exact S.sub_mem (S.smul_mem _ (hz α)) (S.smul_mem _ (by simpa using hz 1))
  have he2 : (Pi.single 2 (1 : Extension p n) : Six (Extension p n)) =
      ![0, 0, 1, 1, 0, 0] - Pi.single 3 1 := by
    ext i
    fin_cases i <;> simp
  have h2 : (Pi.single 2 (1 : Extension p n) : Six (Extension p n)) ∈ S := by
    rw [he2]
    exact S.sub_mem (by simpa using hz 1) h3
  apply (Submodule.eq_top_iff_forall_basis_mem (Pi.basisFun (Extension p n) (Fin 6))).mpr
  intro i
  simp only [Pi.basisFun_apply]
  change Pi.single i 1 ∈ S
  fin_cases i
  · convert hv (![(1,0),(0,0)], 0) using 1
    ext j
    fin_cases j <;> simp [coordinates, signedBivectors]
  · have hh := S.smul_mem (t⁻¹) (hv (![(0,0),(1,0)], 0))
    convert hh using 1
    ext j
    fin_cases j <;> simp [coordinates, signedBivectors, skew_ne_zero p n F hcard]
  · exact h2
  · exact h3
  · have hh := S.smul_mem (-t) (hv (![(0,0),(0,1)], 0))
    convert hh using 1
    ext j
    fin_cases j <;> simp [coordinates, signedBivectors]
    field_simp [skew_ne_zero p n F hcard]
    ring
  · convert hv (![(0,1),(0,0)], 0) using 1
    ext j
    fin_cases j <;> simp [coordinates, signedBivectors]

end ClassicalOrthogonal.Minus.OddSixComparison.Geometry
