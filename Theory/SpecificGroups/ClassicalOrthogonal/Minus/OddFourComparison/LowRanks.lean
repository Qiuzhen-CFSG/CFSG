module
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus
public import Theory.Representation.OrthogonalFourMinusHermitianEquiv.Transport
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Commutativity of the truncated odd minus orthogonal groups

For the plane `x² + xy - a*y²`, the determinant-one isometries preserve
both its polar form and the alternating area form. Hence they commute with
`J(x,y) = (2*a*y-x, 2*x+y)`. When two is nonzero, their second column is
determined by the first, and the resulting matrices commute. The commutator
of the full isometry group lies in this determinant kernel; no equality
with the determinant kernel is assumed.

Deleting the empty hyperbolic coordinates identifies both truncated ranks
with this plane. Their literal commutator/scalar quotients are therefore
abelian. The Chapter A adapter uses this to exclude these ranks for an
actual nonabelian minus-group witness.

Sources: GLS3 §2.7 (`refs/KGroup/GLS3/chapter2.tex`); Aschbacher–Smith,
A.2.17, printed pp.38–39 (`refs/quasithin.pdf`).
-/

public section

open scoped IsMulCommutative
open Theory.AlgebraicGroup
namespace ClassicalOrthogonal.Minus.OddFourComparison.LowRanks
variable {F : Type*} [Field F] (a : F)
private abbrev O := Orthogonal F (F × F) (plane F a)
private def area (v w : F × F) : F := v.1 * w.2 - v.2 * w.1
private def polar (v w : F × F) : F :=
  2 * v.1 * w.1 + v.1 * w.2 + v.2 * w.1 - 2 * a * v.2 * w.2
private theorem coords (g : O a) (v : F × F) :
    g.val v = v.1 • g.val (1, 0) + v.2 • g.val (0, 1) := by
  rw [← map_smul, ← map_smul, ← map_add]
  congr 1
  ext <;> simp
private theorem area_map (g : O a) (v w : F × F) :
    area (g.val v) (g.val w) =
      area (g.val (1, 0)) (g.val (0, 1)) * area v w := by
  rw [coords a g v, coords a g w]
  simp only [area, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring
private def determinant : O a →* F where
  toFun g := area (g.val (1, 0)) (g.val (0, 1))
  map_one' := by simp [area]
  map_mul' g h := area_map a g _ _
private def character : O a →* Fˣ := (determinant a).toHomUnits
private theorem area_preserve (g : O a) (hg : g ∈ (character a).ker) (v w : F × F) :
    area (g.val v) (g.val w) = area v w := by
  have h : area (g.val (1, 0)) (g.val (0, 1)) = 1 :=
    congrArg Units.val (MonoidHom.mem_ker.mp hg)
  rw [area_map, h, one_mul]
private theorem polar_preserve (g : O a) (v w : F × F) :
    polar a (g.val v) (g.val w) = polar a v w := by
  have hp (x : F × F) : plane F a (g.val x) = plane F a x :=
    (mem_quadraticIsometrySubgroup _ _).mp g.property x
  have h : (plane F a).polarBilin (g.val v) (g.val w) = (plane F a).polarBilin v w := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hp]
  simpa only [plane_polar, polar] using h
private def J (v : F × F) : F × F := (2 * a * v.2 - v.1, 2 * v.1 + v.2)
private theorem polar_eq (v w : F × F) : polar a v w = area v (J a w) := by
  simp only [polar, area, J]
  ring
private theorem area_separating {v w : F × F} (h : ∀ x, area x v = area x w) : v = w := by
  have h1 := h (1, 0)
  have h2 := h (0, 1)
  exact Prod.ext (by simpa [area] using h2) (by simpa [area] using h1)
private theorem commutes_J (g : O a) (hg : g ∈ (character a).ker) (w : F × F) :
    g.val (J a w) = J a (g.val w) := by
  apply area_separating
  intro x
  obtain ⟨v, rfl⟩ := g.val.surjective x
  rw [area_preserve a g hg, ← polar_eq, ← polar_eq, polar_preserve]
private theorem kernel_second (htwo : (2 : F) ≠ 0) (g : O a)
    (hg : g ∈ (character a).ker) :
    g.val (0, 1) = (a * (g.val (1, 0)).2, (g.val (1, 0)).1 + (g.val (1, 0)).2) := by
  have he := commutes_J a g hg (1, 0)
  rw [coords a g (J a (1, 0))] at he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  simp only [J, mul_zero, zero_sub, mul_one, add_zero,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
  apply Prod.ext
  · apply (mul_left_cancel₀ htwo)
    linear_combination h1
  · apply (mul_left_cancel₀ htwo)
    linear_combination h2
private theorem kernel_coordinates (htwo : (2 : F) ≠ 0) (g : O a)
    (hg : g ∈ (character a).ker) (v : F × F) :
    g.val v = (v.1 * (g.val (1, 0)).1 + a * v.2 * (g.val (1, 0)).2,
      v.1 * (g.val (1, 0)).2 + v.2 * ((g.val (1, 0)).1 + (g.val (1, 0)).2)) := by
  rw [coords a g v, kernel_second a htwo g hg]
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  all_goals ring
private theorem kernel_commutative (htwo : (2 : F) ≠ 0) : IsMulCommutative (character a).ker := by
  apply IsMulCommutative.of_comm
  intro g h
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change g.val.val (h.val.val v) = h.val.val (g.val.val v)
  conv_lhs => rw [kernel_coordinates a htwo g.val g.property]
  conv_rhs => rw [kernel_coordinates a htwo h.val h.property]
  rw [kernel_coordinates a htwo h.val h.property v, kernel_coordinates a htwo g.val g.property v]
  ext <;> simp only <;> ring
/-- The derived group of the full plane isometry group is abelian in odd characteristic. -/
theorem plane_commutator_commutative (htwo : (2 : F) ≠ 0) :
    IsMulCommutative (Omega F (F × F) (plane F a)) := by
  let := kernel_commutative a htwo
  apply IsMulCommutative.of_comm
  intro g h
  have hg := Abelianization.commutator_subset_ker (character a) g.property
  have hh := Abelianization.commutator_subset_ker (character a) h.property
  have he := mul_comm (⟨g.val, hg⟩ : (character a).ker) ⟨h.val, hh⟩
  exact Subtype.ext (congrArg (fun k : (character a).ker => k.val) he)
private noncomputable def dropZeroHyperbolic :
    (form F 0 a).IsometryEquiv (plane F a) where
  toFun := Prod.snd
  invFun v := (0, v)
  left_inv v := Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_app' v := by simp
private theorem omega_zero_commutative (htwo : (2 : F) ≠ 0) :
    IsMulCommutative (Omega F (Space F 0) (form F 0 a)) := by
  let e := Representation.OrthogonalFourMinus.HermitianEquiv.omegaCongr (dropZeroHyperbolic a)
  let := plane_commutator_commutative a htwo
  apply IsMulCommutative.of_comm
  intro x y
  apply e.injective
  exact (map_mul e x y).trans ((mul_comm (e x) (e y)).trans (map_mul e y x).symm)
/-- The two truncated ranks have abelian literal commutator/scalar quotients. -/
theorem pOmegaMinus_commutative_of_le_one (F : Type*) [Field F] [Finite F]
    (htwo : (2 : F) ≠ 0) (r : ℕ) (hr : r ≤ 1) :
    IsMulCommutative (ClassicalGroup.POmegaMinus r F) := by
  have hr0 : r - 1 = 0 := Nat.sub_eq_zero_of_le hr
  have hc : IsMulCommutative (Omega F (Space F (r - 1)) (quadraticForm F r)) := by
    unfold quadraticForm
    rw [hr0]
    exact omega_zero_commutative (parameter F) htwo
  let := hc
  infer_instance
/-- Odd cardinality excludes characteristic two. -/
theorem two_ne_zero_of_odd_card (F : Type*) [Field F] [Finite F]
    (ho : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  intro h
  let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h
  let : Fintype F := Fintype.ofFinite F
  have hh := FiniteField.even_card_of_char_two (ringChar.eq F 2)
  rw [← Nat.card_eq_fintype_card] at hh
  exact (Nat.not_even_iff_odd.mpr ho)
    (even_iff_two_dvd.mpr (Nat.dvd_of_mod_eq_zero hh))

/-- An odd finite coefficient field supplies the nonzero-two hypothesis automatically. -/
theorem pOmegaMinus_commutative_of_le_one_odd (F : Type*) [Field F] [Finite F]
    (ho : Odd (Nat.card F)) (r : ℕ) (hr : r ≤ 1) :
    IsMulCommutative (ClassicalGroup.POmegaMinus r F) :=
  pOmegaMinus_commutative_of_le_one F (two_ne_zero_of_odd_card F ho) r hr

end ClassicalOrthogonal.Minus.OddFourComparison.LowRanks
