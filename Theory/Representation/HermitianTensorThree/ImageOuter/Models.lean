module

public import Theory.Representation.HermitianTensorThree.ImageOuter.Kernel
public import Theory.NumberTheory.BinaryTorusParity
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The faithful Hermitian tensor image as PSL₃ or SL₃

On cube roots, the `2^n`-power Frobenius is inversion for odd n and the
identity for even n. The norm-one cubic scalar kernel is therefore the
whole center in the first case and trivial in the second. The first
isomorphism theorem constructs actual multiplicative equivalences, with
compatibility formulas for the given cover-to-image homomorphism.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.4.4(7), printed p.381.
-/

@[expose] public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter
variable (n : ℕ) [NeZero n]

omit [NeZero n] in
theorem sigma_cube_root_odd (hn : Odd n) (c : E n) (hc : c ^ 3 = 1) :
    sigma n c = c ^ 2 := by
  change iterateFrobeniusEquiv (E n) 2 n c = _
  rw [iterateFrobeniusEquiv_def, pow_eq_pow_mod _ hc,
    Nat.BinaryTorusParity.two_pow_mod_three]
  simp [Nat.odd_iff.mp hn]

omit [NeZero n] in
theorem sigma_cube_root_even (hn : Even n) (c : E n) (hc : c ^ 3 = 1) :
    sigma n c = c := by
  change iterateFrobeniusEquiv (E n) 2 n c = _
  rw [iterateFrobeniusEquiv_def, pow_eq_pow_mod _ hc,
    Nat.BinaryTorusParity.two_pow_mod_three]
  simp [Nat.even_iff.mp hn]

omit [NeZero n] in
theorem norm_cube_root_odd (hn : Odd n) (c : E n) (hc : c ^ 3 = 1) :
    c * sigma n c = 1 := by
  rw [sigma_cube_root_odd n hn c hc, ← pow_succ', hc]

omit [NeZero n] in
theorem norm_cube_root_even_iff (hn : Even n) (c : E n) (hc : c ^ 3 = 1) :
    c * sigma n c = 1 ↔ c = 1 := by
  rw [sigma_cube_root_even n hn c hc]
  constructor
  · intro hn
    have he : c ^ 3 = c := by rw [pow_succ, pow_two, hn, one_mul]
    exact he.symm.trans hc
  · rintro rfl
    exact one_mul _

/-- For odd half-degree, precisely the entire scalar center is killed. -/
theorem actionHom_ker_odd (hn : Odd n) :
    (actionHom n).ker = Subgroup.center (Cover n) := by
  ext g
  rw [mem_actionHom_ker_iff, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨c, he, hc, _⟩
    exact ⟨c, by simpa using hc, he.symm⟩
  · rintro ⟨c, hc, he⟩
    have hc' : c ^ 3 = 1 := by simpa using hc
    exact ⟨c, he.symm, hc', norm_cube_root_odd n hn c hc'⟩

/-- For even half-degree the descended action is faithful on SL₃ itself. -/
theorem actionHom_ker_even (hn : Even n) : (actionHom n).ker = ⊥ := by
  apply bot_unique
  intro g hg
  obtain ⟨c, he, hc, hnorm⟩ := (mem_actionHom_ker_iff n g).mp hg
  have hc1 := (norm_cube_root_even_iff n hn c hc).mp hnorm
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  simpa [hc1] using he

/-- The actual quotient-to-image identification for odd half-degree. -/
def imageEquivPSL (hn : Odd n) :
    Image n ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (E n) :=
  (QuotientGroup.quotientKerEquivRange (actionHom n)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (actionHom_ker_odd n hn))

/-- This equivalence uses the literal cover projection. -/
theorem imageEquivPSL_toImage (hn : Odd n) (g : Cover n) :
    imageEquivPSL n hn (toImage n g) = QuotientGroup.mk g := by
  have he : (QuotientGroup.quotientKerEquivRange (actionHom n)).symm (toImage n g) =
      QuotientGroup.mk g :=
    (QuotientGroup.quotientKerEquivRange (actionHom n)).symm_apply_apply (QuotientGroup.mk g)
  change (QuotientGroup.quotientMulEquivOfEq (actionHom_ker_odd n hn))
    ((QuotientGroup.quotientKerEquivRange (actionHom n)).symm (toImage n g)) = _
  rw [he]
  rfl

/-- The actual image is SL₃ when the half-degree is even. -/
def imageEquivSL (hn : Even n) : Image n ≃* Cover n :=
  (MonoidHom.ofInjective ((actionHom n).ker_eq_bot_iff.mp (actionHom_ker_even n hn))).symm

theorem imageEquivSL_toImage (hn : Even n) (g : Cover n) :
    imageEquivSL n hn (toImage n g) = g :=
  (MonoidHom.ofInjective ((actionHom n).ker_eq_bot_iff.mp
    (actionHom_ker_even n hn))).symm_apply_apply g
end Representation.HermitianTensorThree.ImageOuter
