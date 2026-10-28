module

public import Theory.AtlasPort.Algebra.SplitOctonion.NormGeometry
public import Theory.AtlasPort.LinearGroups.G2.Basic
public import Mathlib.FieldTheory.ChevalleyWarning
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# A singular vector in a four-dimensional octonion subspace

Trace and norm restrict to polynomials of degrees at most one and two in four
basis coordinates. Chevalley–Warning makes the number of common zeros divisible
by the field characteristic. Since zero is one solution, there is another.
This applies to the actual fixed space of an involution in `InvolutionFusion`.

Application: Aschbacher–Smith I.1.1–I.1.4, printed pp.407–408, and GLS III §6.1.
Coordinates use Gerald Höhn and the ATLAS contributors' licensed split-octonion
port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.MultiplierOrdinary.OddTwoPrimary.InvolutionFusion
open Atlas.SplitOctonion MvPolynomial
variable {F : Type*} [Field F] [Finite F]

/-- A four-space over a finite field contains a nonzero trace-zero norm-zero octonion. -/
theorem exists_singular_of_finrank_four {p : ℕ} [Fact p.Prime] [CharP F p]
    (W : Submodule F (Carrier F)) (hW : Module.finrank F W = 4) :
    ∃ v ∈ W, trace v = 0 ∧ norm v = 0 ∧ v ≠ 0 := by
  classical
  let _ := Fintype.ofFinite F
  let b := Module.finBasisOfFinrankEq F W hW
  let L : Fin 8 → MvPolynomial (Fin 4) F := fun i =>
    ∑ j : Fin 4, C ((b j : Carrier F) i) * X j
  have hL (i : Fin 8) : (L i).totalDegree ≤ 1 := by
    apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_mul _ _).trans (by simp)
  have heval (t : Fin 4 → F) (i : Fin 8) :
      eval t (L i) = (b.equivFun.symm t : Carrier F) i := by
    rw [Module.Basis.equivFun_symm_apply]
    simp [L, map_sum, mul_comm]
  let T := L 3 + L 4
  let N := L 0 * L 7 + L 1 * L 6 + L 2 * L 5 + L 3 * L 4
  have hT : T.totalDegree ≤ 1 := (totalDegree_add _ _).trans (max_le (hL 3) (hL 4))
  have hprod (i j : Fin 8) : (L i * L j).totalDegree ≤ 2 := by
    exact (totalDegree_mul _ _).trans (by have := hL i; have := hL j; omega)
  have hN : N.totalDegree ≤ 2 := by
    exact (totalDegree_add _ _).trans (max_le
      ((totalDegree_add _ _).trans (max_le
        ((totalDegree_add _ _).trans (max_le (hprod 0 7) (hprod 1 6))) (hprod 2 5)))
      (hprod 3 4))
  have hTeval (t : Fin 4 → F) : eval t T = trace (b.equivFun.symm t) := by
    simp only [T, map_add, heval, trace]
  have hNeval (t : Fin 4 → F) : eval t N = norm (b.equivFun.symm t) := by
    simp only [N, map_add, map_mul, heval, norm]
  have hd := char_dvd_card_solutions_of_add_lt p
    (f₁ := T) (f₂ := N) (by simp only [Fintype.card_fin]; omega)
  by_contra hn
  have hz (v : W) (ht : trace (v : Carrier F) = 0) (hv : norm (v : Carrier F) = 0) :
      v = 0 := by
    apply Subtype.ext
    exact not_not.mp (fun h => hn ⟨v, v.property, ht, hv, h⟩)
  let Z := {t : Fin 4 → F // eval t T = 0 ∧ eval t N = 0}
  have hz0 : eval (0 : Fin 4 → F) T = 0 ∧ eval (0 : Fin 4 → F) N = 0 := by
    rw [hTeval, hNeval, map_zero]
    simp [trace, norm]
  have hall (t : Z) : t.val = 0 := by
    apply b.equivFun.symm.injective
    rw [map_zero]
    exact hz _ ((hTeval t).symm.trans t.property.1) ((hNeval t).symm.trans t.property.2)
  let : Unique Z := { default := ⟨0,hz0⟩, uniq := fun t => Subtype.ext (hall t) }
  have hc : Fintype.card Z = 1 := Fintype.card_unique
  have hd' : p ∣ 1 := hc ▸ hd
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hd')
end Atlas.G2.MultiplierOrdinary.OddTwoPrimary.InvolutionFusion

end
