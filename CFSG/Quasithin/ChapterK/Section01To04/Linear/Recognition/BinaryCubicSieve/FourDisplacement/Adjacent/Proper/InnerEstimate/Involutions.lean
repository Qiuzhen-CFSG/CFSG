module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.LocalData
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Transvections
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel

/-!
# Two literal involution representatives in binary SL₄

Square-zero displacement has positive rank at most two on the natural four-space.
Rank one gives a transvection, so binary transvection conjugacy applies. In rank
two, lifts of a basis of the image supply two independent length-two chains.
Their basis change conjugates the operator to the product of the disjoint roots
01 and 23. The matrix-to-linear equivalence places the conjugator in SL₄(2).

The consumer in `InnerEstimate` transfers bounds on these two cyclic fixed spaces
to common fixed spaces of elementary actors on the original representation.
No representation-theoretic displacement estimate is proved in this module.

Source application: Aschbacher–Smith K.3.2, printed pp.454–455; Guralnick–Malle,
Classification of 2F-modules II, author manuscript, Proposition 4.7, pp.25–26.
-/

public section
open Module BinaryLinear.OuterCyclic
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.InnerEstimate

private abbrev F := ZMod 2
private abbrev X := Fin 4 → F
private theorem binary_add_self (v : X) : v + v = 0 := ZModModule.add_self v

private theorem rank_two_basis (D : X →ₗ[F] X)
    (hDD : ∀ v, D (D v) = 0) (hr : finrank F D.range = 2) :
    ∃ b : Basis (Fin 4) F X,
      D (b 0) = 0 ∧ D (b 1) = b 0 ∧ D (b 2) = 0 ∧ D (b 3) = b 2 := by
  classical
  let a := Module.finBasisOfFinrankEq F D.range hr
  obtain ⟨u, hu⟩ := (a 0).property
  obtain ⟨v, hv⟩ := (a 1).property
  have ha : LinearIndependent F (fun i => ((a i : D.range) : X)) :=
    a.linearIndependent.map' D.range.subtype (Submodule.ker_subtype _)
  have hpair (c d : F) (h : c • D u + d • D v = 0) : c = 0 ∧ d = 0 := by
    have hh : ∑ i : Fin 2, (![c,d] i) • (a i : X) = 0 := by
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, ← hu, ← hv] using h
    have hz := (Fintype.linearIndependent_iff.mp ha) ![c,d] hh
    exact ⟨hz 0, hz 1⟩
  have hi : LinearIndependent F ![D u, u, D v, v] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    simp only [Fin.sum_univ_four] at hc
    change c 0 • D u + c 1 • u + c 2 • D v + c 3 • v = 0 at hc
    have hd := congrArg D hc
    simp only [map_add, map_smul, hDD, smul_zero, zero_add, add_zero, map_zero] at hd
    obtain ⟨h1,h3⟩ := hpair (c 1) (c 3) hd
    simp only [h1, h3, zero_smul, add_zero] at hc
    obtain ⟨h0,h2⟩ := hpair (c 0) (c 2) hc
    intro i
    fin_cases i <;> assumption
  let b := basisOfPiSpaceOfLinearIndependent hi
  have hb (i) : b i = (![D u, u, D v, v] : Fin 4 → X) i :=
    congrFun (coe_basisOfPiSpaceOfLinearIndependent hi) i
  refine ⟨b, ?_, ?_, ?_, ?_⟩ <;> simp [hb, hDD]

private theorem upper_action (i : Fin 3) (v : X) :
    slEquivLinear 4 (simpleUpper i) v =
      v + v i.succ • Pi.single i.castSucc 1 := by
  ext k
  simp [slEquivLinear_apply, simpleUpper, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.add_mulVec, Matrix.single_mulVec, Pi.single_apply, Function.update_apply]

private theorem rank_two_conjugate (t : X ≃ₗ[F] X) (ht : t ^ 2 = 1)
    (hr : finrank F (t.toLinearMap - LinearMap.id).range = 2) :
    ∃ c : X ≃ₗ[F] X, c * slEquivLinear 4 (simpleUpper 0 * simpleUpper 2) * c⁻¹ = t := by
  let D := t.toLinearMap - LinearMap.id
  have hact (x) : t x = x + D x := by dsimp [D]; abel
  have hDD (x) : D (D x) = 0 := by
    have ht' : t (t x) = x := by
      have he := congrArg (fun s : X ≃ₗ[F] X => s x) ht
      change (t ^ 2) x = x at he
      simpa only [pow_two, LinearEquiv.mul_apply] using he
    change t (t x - x) - (t x - x) = 0
    rw [map_sub, ht']
    calc
      x - t x - (t x - x) = (x + x) - (t x + t x) := by abel
      _ = 0 := by rw [binary_add_self, binary_add_self, sub_self]
  obtain ⟨b,h0,h1,h2,h3⟩ := rank_two_basis D hDD hr
  let c : X ≃ₗ[F] X := (Pi.basisFun F (Fin 4)).equiv b (Equiv.refl _)
  have hc (i : Fin 4) : c (Pi.single i 1) = b i := by
    simpa only [Pi.basisFun_apply, Equiv.refl_apply] using
      (Pi.basisFun F (Fin 4)).equiv_apply i b (Equiv.refl _)
  have he : t * c = c * slEquivLinear 4 (simpleUpper 0 * simpleUpper 2) := by
    apply LinearEquiv.toLinearMap_injective
    apply (Pi.basisFun F (Fin 4)).ext
    intro i
    rw [Pi.basisFun_apply]
    change t (c (Pi.single i 1)) = c (slEquivLinear 4 (simpleUpper 0 * simpleUpper 2) (Pi.single i 1))
    rw [hc, hact, map_mul, LinearEquiv.mul_apply, upper_action, upper_action]
    fin_cases i <;> simp [map_add, hc, h0, h1, h2, h3]
  refine ⟨c, ?_⟩
  calc
    c * slEquivLinear 4 (simpleUpper 0 * simpleUpper 2) * c⁻¹ = t * c * c⁻¹ := by rw [he]
    _ = t := mul_inv_cancel_right _ _

private theorem rank_one_transvection (t : X ≃ₗ[F] X)
    (hr : finrank F (t.toLinearMap - LinearMap.id).range = 1) :
    IsTransvection t := by
  obtain ⟨f, v, he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr hr.le
  have hact (w : X) : t w = w + f w • v := LinearMap.congr_fun he w
  have hne : t.toLinearMap ≠ LinearMap.id := by
    intro h
    rw [h, sub_self, LinearMap.range_zero] at hr
    have hz : finrank F (⊥ : Submodule F X) = 0 := finrank_bot _ _
    omega
  have hf : f ≠ 0 := by
    intro h
    apply hne
    apply LinearMap.ext
    intro w
    simpa [h] using hact w
  have hv : v ≠ 0 := by
    intro h
    apply hne
    apply LinearMap.ext
    intro w
    simpa [h] using hact w
  have hfv : f v = 0 := by
    rcases (by decide : ∀ x : F, x = 0 ∨ x = 1) (f v) with h | h
    · exact h
    · have htv : t v = 0 := by rw [hact, h, one_smul, binary_add_self]
      exact (hv (t.map_eq_zero_iff.mp htv)).elim
  exact ⟨v, f, hv, hf, hfv, LinearEquiv.ext hact⟩

private theorem upper_transvection : IsTransvection (slEquivLinear 4 (simpleUpper 0)) := by
  refine ⟨Pi.single 0 1, LinearMap.proj 1, ?_, ?_, by simp, ?_⟩
  · intro h
    have hh := congrFun h 0
    simp at hh
  · intro h
    have hh := LinearMap.congr_fun h (Pi.single 1 1)
    simp at hh
  · apply LinearEquiv.ext
    intro v
    exact upper_action 0 v

/-- The two explicit binary SL₄ involution classes. The conjugators remain
in SL₄(2), via the actual matrix-to-linear equivalence. -/
theorem involution_conjugacy (t : Group) (ht : t ^ 2 = 1) (hne : t ≠ 1) :
    IsConj (simpleUpper 0) t ∨ IsConj (simpleUpper 0 * simpleUpper 2) t := by
  let E := slEquivLinear 4
  let T := E t
  let D := T.toLinearMap - LinearMap.id
  have hT : T ^ 2 = 1 := by rw [← map_pow, ht, map_one]
  have hDD (x) : D (D x) = 0 := by
    have ht' : T (T x) = x := by
      have he := congrArg (fun s : X ≃ₗ[F] X => s x) hT
      change (T ^ 2) x = x at he
      simpa only [pow_two, LinearEquiv.mul_apply] using he
    change T (T x - x) - (T x - x) = 0
    rw [map_sub, ht']
    calc
      x - T x - (T x - x) = (x + x) - (T x + T x) := by abel
      _ = 0 := by rw [binary_add_self, binary_add_self, sub_self]
  have hk : D.range ≤ D.ker := by
    rintro _ ⟨v, rfl⟩
    exact hDD v
  have he : finrank F D.range + finrank F D.ker = 4 := by
    simpa using D.finrank_range_add_finrank_ker
  have hm : finrank F D.range ≤ finrank F D.ker := Submodule.finrank_mono hk
  have hD : D ≠ 0 := by
    intro h
    have hT1 : T = 1 := by
      apply LinearEquiv.toLinearMap_injective
      exact sub_eq_zero.mp h
    apply hne
    apply E.injective
    simpa only [map_one] using hT1
  have hpos : finrank F D.range ≠ 0 := by
    intro h
    exact hD (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h))
  have hr : finrank F D.range = 1 ∨ finrank F D.range = 2 := by omega
  rcases hr with hr | hr
  · obtain ⟨c, hc⟩ := transvections_conjugate upper_transvection (rank_one_transvection T hr)
    left
    apply isConj_iff.mpr
    refine ⟨E.symm c, ?_⟩
    apply E.injective
    simpa only [MulAut.conj_apply, map_mul, map_inv, E.apply_symm_apply] using hc
  · obtain ⟨c,hc⟩ := rank_two_conjugate T hT hr
    right
    apply isConj_iff.mpr
    refine ⟨E.symm c, ?_⟩
    apply E.injective
    simpa only [MulAut.conj_apply, map_mul, map_inv, E.apply_symm_apply] using hc

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.InnerEstimate
