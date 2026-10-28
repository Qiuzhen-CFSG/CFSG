module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.TorusCoordinates
public import Theory.AlgebraicGroup.Tori.Character.Duality
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Primitive D4 characters and equivariant polynomials

Each coordinate root has a simple-coroot pairing equal to `1` or `-1`.
Transport to the integral character lattice of an actual geometric torus
therefore shows that a coordinate-root character has no proper nonnegative
power root. If a nonzero polynomial scales by this character, comparison of
its leading coefficient identifies the character scaling its argument.

This supplies the character-theoretic step in Spin root exhaustiveness
without asserting tangent injectivity or a regular inverse of the Spin cover.
The existence of a suitable nonzero natural matrix coefficient is a separate
geometric obligation. The arguments here work in every characteristic.

Source: the D4 numbering and root pairings in GLS3 §§1.8, 1.12.1(g), and 1.14.1
(`refs/KGroup/GLS3/Chapter1.tex`). Vertex 1 is central and 0, 2, 3 are the arms.
-/

public section
noncomputable section
namespace Triality.SimplyConnected.Pinning
open Theory Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
universe u
variable (k : Type u) [Field k] [IsAlgClosed k]

local instance rootSupportCharacterAlgebraicGroup
    (T : ClosedSubgroup (groupVariety k)) : AlgebraicGroup T.carrierVariety :=
  T.carrierAlgebraicGroup

/-- Every D4 root pairs to `1` or `-1` with a numbered simple coroot. -/
theorem rootCorootExponent_has_unit_entry (r : RootIndex) :
    ∃ i : Fin 4, rootCorootExponent r i = 1 ∨ rootCorootExponent r i = -1 := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
  refine ⟨if (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) then 1 else 0, ?_⟩
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals
    unfold rootCorootExponent
    simp only [Fin.sum_univ_succ]
    by_cases hs : s.1 = 1 <;> by_cases ht : t.1 = 1 <;>
      norm_num [evenOrthogonalRootExponent, simpleRoot,
        typeDSimpleRootIndex, Pi.single_apply, Fin.ext_iff, Fin.val_last, hs, ht]

/-- A coordinate-root character is not a proper nonnegative power of any
algebraic character. The geometric torus isomorphism is essential here. -/
theorem coordinateRootWeight_power_exponent (T : ClosedSubgroup (groupVariety k))
    (e : @Iso k _ (dVariety k 4) T.carrierVariety _ T.carrierAlgebraicGroup)
    (χ : TorusWeight T) (r : RootIndex) (n : ℕ)
    (h : χ ^ n = coordinateRootWeight k T e r) : n = 1 := by
  obtain ⟨z, hz⟩ := dLaurentCharacter_surjective (k := k) 4
    (TorusCharacter.pullback e.hom χ)
  have hcoord : TorusCharacter.pullback e.hom (coordinateRootWeight k T e r) =
      dLaurentCharacter 4 (rootCorootExponent r) := by
    apply AlgebraicGroup.Morphism.ext
    funext t
    change (dLaurentCharacter 4 (rootCorootExponent r)).onPoints
        (e.inv.onPoints (e.hom.onPoints t)) = _
    rw [e.hom_inv_id]
    rfl
  have hpow : dLaurentCharacter (k := k) 4 z ^ n =
      dLaurentCharacter 4 (rootCorootExponent r) := by
    rw [hz, ← map_pow, h, hcoord]
  have hexp : n • z = rootCorootExponent r := by
    apply (dLaurentCharacterAddEquiv (k := k) 4).injective
    rw [map_nsmul]
    exact congrArg Additive.ofMul hpow
  obtain ⟨i, hi⟩ := rootCorootExponent_has_unit_entry r
  have hd : (n : ℤ) ∣ rootCorootExponent r i := ⟨z i, by
    have hh := congrFun hexp i
    simpa only [Pi.smul_apply, nsmul_eq_mul] using hh.symm⟩
  have hn : (n : ℤ) ∣ 1 := by
    rcases hi with hi | hi
    · simpa only [hi] using hd
    · simpa only [hi, dvd_neg] using hd
  have hn' : n ∣ 1 := by exact_mod_cast hn
  exact Nat.eq_one_of_dvd_one hn'

/-- A nonzero polynomial with coordinate-root scaling detects the exact
character of its parameter, even when its derivative has not been controlled. -/
theorem eq_coordinateRootWeight_of_polynomial (T : ClosedSubgroup (groupVariety k))
    (e : @Iso k _ (dVariety k 4) T.carrierVariety _ T.carrierAlgebraicGroup)
    (χ : TorusWeight T) (r : RootIndex) (P : Polynomial k) (hP : P ≠ 0)
    (hscale : ∀ (s : Variety.Point T.carrierVariety) (a : k),
      P.eval (χ.pointCharacter s * a) =
        (coordinateRootWeight k T e r).pointCharacter s * P.eval a) :
    χ = coordinateRootWeight k T e r := by
  have hp : P.coeff P.natDegree ≠ 0 := by
    simpa only [Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hP
  have hpow : χ ^ P.natDegree = coordinateRootWeight k T e r := by
    apply TorusCharacter.pointCharacter_injective
    ext s
    have hid : P.comp (Polynomial.C (χ.pointCharacter s) * Polynomial.X) =
        Polynomial.C ((coordinateRootWeight k T e r).pointCharacter s) * P := by
      apply Polynomial.funext
      intro a
      simpa only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X] using hscale s a
    have hcoeff := congrArg (fun Q : Polynomial k => Q.coeff P.natDegree) hid
    rw [Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_C_mul] at hcoeff
    have heval : χ.pointCharacter s ^ P.natDegree =
        (coordinateRootWeight k T e r).pointCharacter s := by
      apply mul_left_cancel₀ hp
      simpa only [mul_comm] using hcoeff
    calc
      (χ ^ P.natDegree).pointCharacter s = χ.pointCharacter s ^ P.natDegree := by
        change ((torusPointEval T.carrierVariety s (χ ^ P.natDegree) : k)) = _
        rw [map_pow]
        rfl
      _ = _ := heval
  have hn := coordinateRootWeight_power_exponent k T e χ r P.natDegree hpow
  simpa only [hn, pow_one] using hpow

end Triality.SimplyConnected.Pinning
