module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Elementary lifts detected by quotient stabilizers

Let an actor group act on W, with a central subgroup U of exponent two,
and with W/U of exponent two. If the stabilizer of every nonidentity coset
has no nonidentity fixed point in U, then W is elementary abelian.

Squaring is constant on U-cosets and equivariant. Thus the square of a lift
is fixed by its coset stabilizer and must be the identity. Exponent two
then implies commutativity. In particular no transitivity assumption is needed.

Source: the lift argument in Aschbacher–Smith, *The Classification of Quasithin
Groups*, combined manuscript (1 March 2004), C.1.35, printed pp.137–138.
The natural/dual module stabilizer calculation is a separate input.
-/

/-- A central elementary kernel and fixed-point-free coset stabilizers force
an exponent-two extension to be elementary abelian. Coset stabilization is
expressed by displacement, avoiding any choice of quotient action. -/
public theorem IsElementaryAbelian.of_central_kernel_stabilizer {A W : Type*} [Group A] [Group W] [MulDistribMulAction A W]
    (U : Subgroup W) (hcentral : U ≤ Subgroup.center W)
    (hexp : ∀ u ∈ U, u ^ 2 = 1) (hsquare : ∀ w : W, w ^ 2 ∈ U)
    (hfixed : ∀ w : W, w ∉ U → ∀ u ∈ U,
      (∀ a : A, (a • w) / w ∈ U → a • u = u) → u = 1) :
    IsElementaryAbelian 2 W := by
  have hs (w : W) : w ^ 2 = 1 := by
    by_cases hw : w ∈ U
    · exact hexp w hw
    apply hfixed w hw (w ^ 2) (hsquare w)
    intro a ha
    have hc : Commute ((a • w) / w) w :=
      (Subgroup.mem_center_iff.mp (hcentral ha) w).symm
    calc
      a • (w ^ 2) = (a • w) ^ 2 := smul_pow' a w 2
      _ = (((a • w) / w) * w) ^ 2 := by rw [div_mul_cancel]
      _ = ((a • w) / w) ^ 2 * w ^ 2 := hc.mul_pow 2
      _ = w ^ 2 := by rw [hexp _ ha, one_mul]
  have hi (w : W) : w⁻¹ = w := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hs w)
  refine {
    toIsMulCommutative := ⟨⟨?_⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  intro x y
  calc
    x * y = (x * y)⁻¹ := (hi _).symm
    _ = y * x := by rw [mul_inv_rev, hi, hi]
