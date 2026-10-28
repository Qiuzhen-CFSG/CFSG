module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddTwoPrimary.LocalModel
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne

/-!
# An outer involution of the quaternion rank-one subgroup

Write the split octonions as pairs of split quaternions, using the checked
Wilson-coordinate comparison in `OrthogonalRankOne`. Conjugation by the
matrix with rows `(0,d)` and `(1,0)` preserves quaternion multiplication and
conjugation, and its square is the identity. Applying it to both quaternion
coordinates therefore gives an actual octonion automorphism. It normalizes
the two determinant-one matrix factors by the same conjugation action.

If `-d` is nonsquare, this involution is outside the image of the two factors:
an equality of the actions forces the first determinant-one matrix to be
anti-diagonal, and its determinant equation would make `-d` a square.
Consequently the extended semidirect-product map has precisely the common
scalar signs as its kernel. The finite-field specialization and odd-index
local model are assembled in `OrthogonalMap.lean`.

This is the split-quaternion orthogonal subgroup construction used in the
odd G₂ covering calculation behind Aschbacher–Smith I.1.1–I.1.4,
printed pp.407–408, and GLS III §6.1. The imported octonion coordinates use
the licensed ATLAS port of Wilson's integral table (Eq. 4.11); see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace Atlas.G2.MultiplierOrdinary.OddTwoPrimary.OrthogonalMap
open Atlas.SplitOctonion Matrix
open OddQuadraticTorus.OrthogonalRankOne
open scoped MatrixGroups
variable {F : Type*} [Field F]

/-- Conjugation by the matrix with rows `(0,d)` and `(1,0)`. -/
def twist (d : F) (a : Mat F) : Mat F :=
  !![a 1 1, d * a 1 0; d⁻¹ * a 0 1, a 0 0]

theorem twist_twist (d : F) (hd : d ≠ 0) (a : Mat F) : twist d (twist d a) = a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twist, hd]

theorem twist_mul (d : F) (hd : d ≠ 0) (a b : Mat F) :
    twist d (a*b) = twist d a * twist d b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twist, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem twist_bar (d : F) (a : Mat F) : twist d (bar a) = bar (twist d a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twist, bar]

def twistLinear (d : F) : Mat F →ₗ[F] Mat F where
  toFun := twist d
  map_add' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twist, _root_.mul_add]
  map_smul' r a := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twist] <;> ring

theorem twist_det (d : F) (hd : d ≠ 0) (a : Mat F) : (twist d a).det = a.det := by
  simp [Matrix.det_fin_two, twist]
  field_simp

def rankOneTwist (d : F) (hd : d ≠ 0) : MulAut SL(2,F) where
  toFun A := ⟨twist d A.val, (twist_det d hd A.val).trans A.property⟩
  invFun A := ⟨twist d A.val, (twist_det d hd A.val).trans A.property⟩
  left_inv A := Subtype.ext (twist_twist d hd A.val)
  right_inv A := Subtype.ext (twist_twist d hd A.val)
  map_mul' A B := Subtype.ext (twist_mul d hd A.val B.val)

def productTwist (d : F) (hd : d ≠ 0) : MulAut (SL(2,F) × SL(2,F)) :=
  (rankOneTwist d hd).prodCongr (rankOneTwist d hd)

theorem productTwist_sq (d : F) (hd : d ≠ 0) : productTwist d hd ^ 2 = 1 := by
  ext a : 1
  apply Prod.ext <;> apply Subtype.ext <;> exact twist_twist d hd _

def pairTwist (d : F) (hd : d ≠ 0) : (Mat F × Mat F) ≃ₗ[F] (Mat F × Mat F) where
  toFun x := (twist d x.1, twist d x.2)
  invFun x := (twist d x.1, twist d x.2)
  left_inv x := Prod.ext (twist_twist d hd x.1) (twist_twist d hd x.2)
  right_inv x := Prod.ext (twist_twist d hd x.1) (twist_twist d hd x.2)
  map_add' x y := Prod.ext ((twistLinear d).map_add x.1 y.1) ((twistLinear d).map_add x.2 y.2)
  map_smul' r x := Prod.ext ((twistLinear d).map_smul r x.1) ((twistLinear d).map_smul r x.2)

theorem pairTwist_preserves (d : F) (hd : d ≠ 0) (x y : Mat F × Mat F) :
    pairTwist d hd (pairMul x y) = pairMul (pairTwist d hd x) (pairTwist d hd y) := by
  apply Prod.ext
  · change twistLinear d (x.1 * y.1 - bar y.2 * x.2) = _
    rw [map_sub]
    simp only [twistLinear, LinearMap.coe_mk, AddHom.coe_mk, twist_mul d hd, twist_bar]
    rfl
  · change twistLinear d (y.2 * x.1 + x.2 * bar y.1) = _
    rw [map_add]
    simp only [twistLinear, LinearMap.coe_mk, AddHom.coe_mk, twist_mul d hd, twist_bar]
    rfl

def outerEquiv (d : F) (hd : d ≠ 0) : Carrier F ≃ₗ[F] Carrier F :=
  coordinates.trans ((pairTwist d hd).trans coordinates.symm)

theorem outerEquiv_preserves (d : F) (hd : d ≠ 0) (x y : Carrier F) :
    outerEquiv d hd (mul x y) = mul (outerEquiv d hd x) (outerEquiv d hd y) := by
  apply coordinates.injective
  simp only [outerEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    coordinates_mul]
  exact pairTwist_preserves d hd _ _

def outer (d : F) (hd : d ≠ 0) : Model F :=
  ⟨outerEquiv d hd, outerEquiv_preserves d hd⟩

theorem outer_sq (d : F) (hd : d ≠ 0) : outer d hd ^ 2 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply coordinates.injective
  change coordinates (outerEquiv d hd (outerEquiv d hd x)) = coordinates x
  simp only [outerEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  exact Prod.ext (twist_twist d hd _) (twist_twist d hd _)

theorem pairTwist_pairLinear (d : F) (hd : d ≠ 0) (A B : SL(2,F))
    (x : Mat F × Mat F) :
    pairTwist d hd (pairLinear A B x) =
      pairLinear (rankOneTwist d hd A) (rankOneTwist d hd B) (pairTwist d hd x) := by
  change (twist d (A.val * x.1 * bar A.val), twist d (B.val * x.2 * bar A.val)) =
    (twist d A.val * twist d x.1 * bar (twist d A.val),
      twist d B.val * twist d x.2 * bar (twist d A.val))
  simp only [twist_mul d hd, twist_bar]

theorem outer_productHom (d : F) (hd : d ≠ 0) (a : SL(2,F) × SL(2,F)) :
    outer d hd * productHom a = productHom (productTwist d hd a) * outer d hd := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply coordinates.injective
  change coordinates (outerEquiv d hd (octonionEquiv a.1 a.2 x)) =
    coordinates (octonionEquiv (rankOneTwist d hd a.1) (rankOneTwist d hd a.2)
      (outerEquiv d hd x))
  simp only [outerEquiv, octonionEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact pairTwist_pairLinear d hd _ _ _

/-- Nonsquare determinant prevents the outer involution from lying in the central product. -/
theorem outer_not_mem_range (d : F) (hd : d ≠ 0) (hns : ¬ IsSquare (-d)) :
    outer d hd ∉ (productHom (F := F)).range := by
  rintro ⟨⟨A,B⟩, h⟩
  have hcomm (X : Mat F) : A.val * X = twist d X * A.val := by
    have he := congrArg (fun g : Model F => coordinates (g.val (coordinates.symm (X,0)))) h
    change coordinates (octonionEquiv A B (coordinates.symm (X,0))) =
      coordinates (outerEquiv d hd (coordinates.symm (X,0))) at he
    simp only [octonionEquiv, outerEquiv, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply] at he
    have hh := congrArg (fun z : Mat F × Mat F => z.1 * A.val) he
    change (A.val * X * bar A.val) * A.val = twist d X * A.val at hh
    simpa only [mul_assoc, sl_bar_mul, mul_one] using hh
  have h00 : A.val 0 0 = 0 := by
    have he := congrArg (fun M : Mat F => M 0 0) (hcomm !![1,0;0,0])
    simpa [twist, Matrix.mul_apply, Fin.sum_univ_two] using he
  have h11 : A.val 1 1 = 0 := by
    have he := congrArg (fun M : Mat F => M 1 1) (hcomm !![1,0;0,0])
    simpa [twist, Matrix.mul_apply, Fin.sum_univ_two] using he.symm
  have h01 : A.val 0 1 = d * A.val 1 0 := by
    have he := congrArg (fun M : Mat F => M 0 0) (hcomm !![0,0;1,0])
    simpa [twist, Matrix.mul_apply, Fin.sum_univ_two] using he
  have hdet : (-d) * (A.val 1 0 * A.val 1 0) = 1 := by
    have ha := A.property
    simp only [Matrix.det_fin_two, h00, h11, h01, mul_zero, zero_sub] at ha
    linear_combination ha
  have hc : A.val 1 0 ≠ 0 := by
    intro hc
    simp [hc] at hdet
  apply hns
  refine ⟨(A.val 1 0)⁻¹, ?_⟩
  field_simp
  linear_combination hdet

private theorem c2_cases (c : C2) : c = 1 ∨ c = .ofAdd 1 := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  exact h c.toAdd

/-- The homomorphism determined by a square-one element. -/
def involutionHom {G : Type*} [Group G] (g : G) (hg : g ^ 2 = 1) : C2 →* G where
  toFun c := if c = 1 then 1 else g
  map_one' := if_pos rfl
  map_mul' a b := by
    rcases c2_cases a with rfl | rfl <;> rcases c2_cases b with rfl | rfl <;>
      simp [show (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 by decide,
        show (Multiplicative.ofAdd (1 : ZMod 2)) * .ofAdd 1 = 1 by decide,
        ← pow_two, hg]

@[simp] theorem involutionHom_generator {G : Type*} [Group G] (g : G) (hg : g ^ 2 = 1) :
    involutionHom g hg (.ofAdd 1) = g := by
  simp [involutionHom, show (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 by decide]

def action (d : F) (hd : d ≠ 0) : C2 →* MulAut (SL(2,F) × SL(2,F)) :=
  involutionHom (productTwist d hd) (productTwist_sq d hd)

def outerHom (d : F) (hd : d ≠ 0) : C2 →* Model F :=
  involutionHom (outer d hd) (outer_sq d hd)

theorem compatibility (d : F) (hd : d ≠ 0) (c : C2) :
    productHom.comp ((action d hd c).toMonoidHom) =
      (MulAut.conj (outerHom d hd c)).toMonoidHom.comp productHom := by
  rcases c2_cases c with rfl | rfl
  · ext a
    simp
  · apply MonoidHom.ext
    intro a
    change productHom (action d hd (.ofAdd 1) a) =
      outerHom d hd (.ofAdd 1) * productHom a * (outerHom d hd (.ofAdd 1))⁻¹
    simp only [action, outerHom, involutionHom_generator]
    rw [outer_productHom, mul_assoc, mul_inv_cancel, mul_one]

/-- The semidirect-product homomorphism into actual octonion automorphisms. -/
def inclusion (d : F) (hd : d ≠ 0) :
    (SL(2,F) × SL(2,F)) ⋊[action d hd] C2 →* Model F :=
  SemidirectProduct.lift productHom (outerHom d hd) (compatibility d hd)

theorem inclusion_kernel (d : F) (hd : d ≠ 0) (hns : ¬ IsSquare (-d))
    (x : (SL(2,F) × SL(2,F)) ⋊[action d hd] C2) :
    inclusion d hd x = 1 ↔ x = 1 ∨ x = SemidirectProduct.inl (-1,-1) := by
  constructor
  · intro hx
    have hxright : x.right = 1 := by
      rcases c2_cases x.right with h | h
      · exact h
      · exfalso
        have he : productHom x.left * outer d hd = 1 := by
          simpa only [inclusion, SemidirectProduct.lift, MonoidHom.coe_mk,
            OneHom.coe_mk, h, outerHom, involutionHom_generator] using hx
        apply outer_not_mem_range d hd hns
        refine ⟨x.left⁻¹, ?_⟩
        rw [map_inv]
        exact (eq_inv_of_mul_eq_one_right he).symm
    have hb : productHom x.left = 1 := by
      simpa only [inclusion, SemidirectProduct.lift, MonoidHom.coe_mk,
        OneHom.coe_mk, hxright, map_one, mul_one] using hx
    rcases (productHom_eq_one_iff x.left).mp hb with h | h
    · left
      exact SemidirectProduct.ext h hxright
    · right
      exact SemidirectProduct.ext h hxright
  · rintro (rfl | rfl)
    · exact map_one _
    · change SemidirectProduct.lift _ _ _ (SemidirectProduct.inl _) = _
      rw [SemidirectProduct.lift_inl, productHom_neg_one]

end Atlas.G2.MultiplierOrdinary.OddTwoPrimary.OrthogonalMap

end
