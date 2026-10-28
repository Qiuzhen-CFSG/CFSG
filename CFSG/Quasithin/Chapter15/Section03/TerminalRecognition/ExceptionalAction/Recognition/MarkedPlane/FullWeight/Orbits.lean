module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# The three nonzero orbits of the orthogonal two-residual

Independent rotations of order three on the two definite summands lie in
`O²(O₄⁺(2))`. They are transitive on each set with prescribed zero coordinates.
The nonzero orbits have sizes three, three and nine. Hence the sum of any
invariant numerical function is the corresponding weighted sum of three
values. All calculations use the literal natural wreath-product action.

Source: Aschbacher–Smith, the definite-plane decomposition on printed
pp.1121–1122 and the residual image in 15.3.7.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Subgroup
open scoped Matrix BigOperators
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane

def cubicRotation : OrthogonalPlaneActor := ⟨!![0, 1; 1, 1], by decide⟩

def cubicActor (n : OrthogonalPlaneIndex → Fin 3) : OrthogonalActor :=
  ⟨fun i => cubicRotation ^ (n i).val, 1⟩

theorem cubicActor_cube (n : OrthogonalPlaneIndex → Fin 3) : cubicActor n ^ 3 = 1 := by
  apply RegularWreathProduct.ext
  · funext i
    apply Subtype.ext
    funext a b
    revert n i a b
    unfold cubicActor cubicRotation
    decide +kernel
  · rfl

theorem cubicActor_mem (n : OrthogonalPlaneIndex → Fin 3) :
    cubicActor n ∈ pResidual 2 OrthogonalActor := by
  apply mem_pResidual_of_orderOf_coprime
  exact Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one (cubicActor_cube n))
    (by decide : Nat.Coprime 2 3)

theorem cubic_orbit (u v : OrthogonalVector)
    (h : ∀ i, u i = 1 ↔ v i = 1) :
    letI := orthogonalAction
    ∃ n : OrthogonalPlaneIndex → Fin 3, cubicActor n • u = v := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := orthogonalAction
  have hc : ∀ (x y : OrthogonalPlaneVector), (x = 1 ↔ y = 1) →
      ∃ n : Fin 3, (cubicRotation ^ n.val) • x = y := by
    decide +kernel
  choose n hn using fun i => hc (u i) (v i) (h i)
  refine ⟨n, ?_⟩
  funext i
  change (cubicRotation ^ (n i).val) • u (1⁻¹ * i) = v i
  simpa using hn i

def supportPattern (v : OrthogonalVector) : Fin 4 :=
  if v (Multiplicative.ofAdd 0) = 1 then
    if v (Multiplicative.ofAdd 1) = 1 then 0 else 2
  else if v (Multiplicative.ofAdd 1) = 1 then 1 else 3

def patternVector (i : Fin 4) : OrthogonalVector :=
  fun j => if (i = 1 ∧ j = Multiplicative.ofAdd 0) ∨
    (i = 2 ∧ j = Multiplicative.ofAdd 1) ∨ i = 3 then
      Multiplicative.ofAdd ![1,0] else 1

theorem patternVector_support (v : OrthogonalVector) :
    ∀ i, v i = 1 ↔ patternVector (supportPattern v) i = 1 := by
  revert v
  decide +kernel

theorem patternVector_nontrivial (i : Fin 4) (hi : i ≠ 0) : patternVector i ≠ 1 := by
  revert i
  decide +kernel

theorem sum_patterns (f : OrthogonalVector → ℕ)
    (hf : ∀ u v, (∀ i, u i = 1 ↔ v i = 1) → f u = f v)
    (h0 : f 1 = 0) :
    (∑ u, f u) = 3 * f (patternVector 1) + 3 * f (patternVector 2) +
      9 * f (patternVector 3) := by
  have he (u : OrthogonalVector) : f u = f (patternVector (supportPattern u)) :=
    hf u _ (patternVector_support u)
  rw [Finset.sum_congr rfl (fun u _ => he u)]
  have hsum := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset OrthogonalVector))
    (t := (Finset.univ : Finset (Fin 4))) (g := supportPattern)
    (f := fun u => f (patternVector (supportPattern u))) (by simp)
  have hc : ∀ i : Fin 4,
      (Finset.univ.filter (fun u : OrthogonalVector => supportPattern u = i)).card =
      ![1,3,3,9] i := by decide +kernel
  rw [← hsum]
  have hinner (i : Fin 4) :
      (∑ u ∈ Finset.univ.filter (fun u : OrthogonalVector => supportPattern u = i),
        f (patternVector (supportPattern u))) = ![1,3,3,9] i * f (patternVector i) := by
    rw [Finset.sum_congr rfl (fun u hu => by rw [(Finset.mem_filter.mp hu).2]),
      Finset.sum_const, hc, nsmul_eq_mul]
    simp
  simp_rw [hinner]
  have hp0 : patternVector 0 = 1 := by decide +kernel
  simp [Fin.sum_univ_succ, hp0, h0, Nat.add_assoc]
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane
