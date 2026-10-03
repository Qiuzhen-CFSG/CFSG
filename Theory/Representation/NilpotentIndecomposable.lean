module

public import Theory.Representation.KrullSchmidt
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.Algebra.Ring.Idempotent

/-!
# Indecomposability from a nilpotent operator

A commuting idempotent that vanishes on the kernel of a nilpotent operator
vanishes everywhere, by induction on the nilpotence filtration. Consequently,
if that kernel is a line, every commuting idempotent is zero or one. This gives
indecomposability of the associated polynomial module without choosing a Jordan
basis. The application is to transitive cyclic permutation modules in defining
characteristic (Brauer--Suzuki, Section I; Fong 1967, p. 71).
-/

public section

open Polynomial

namespace LinearMap

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- A commuting idempotent is determined by its action on the kernel of a
nilpotent operator. -/
theorem eq_zero_of_isIdempotent_of_ker_nilpotent
    (N P : Module.End k V) (hN : IsNilpotent N) (hP : IsIdempotentElem P)
    (hNP : Commute N P) (hker : ∀ v, N v = 0 → P v = 0) : P = 0 := by
  have aux : ∀ n : ℕ, ∀ v : V, (N ^ n) v = 0 → P v = 0 := by
    intro n
    induction n with
    | zero =>
        intro v hv
        have : v = 0 := by simpa using hv
        simp [this]
    | succ n ih =>
        intro v hv
        have hNv : P (N v) = 0 := ih (N v) (by
          simpa only [pow_succ, Module.End.mul_apply] using hv)
        have hNPv : N (P v) = 0 := by
          rw [show N (P v) = P (N v) from DFunLike.congr_fun hNP.eq v, hNv]
        have hPPv := hker (P v) hNPv
        simpa only [← Module.End.mul_apply, hP.eq] using hPPv
  obtain ⟨n, hn⟩ := hN
  ext v
  exact aux n v (by rw [hn]; rfl)

/-- If a nilpotent operator has a one-dimensional kernel, its commuting
idempotents are trivial. -/
theorem idempotent_eq_zero_or_one_of_nilpotent_ker_line
    (N P : Module.End k V) (hN : IsNilpotent N) (hP : IsIdempotentElem P)
    (hNP : Commute N P) (v : V) (hv : v ≠ 0)
    (hNv : N v = 0) (hker : ∀ w, N w = 0 → ∃ a : k, w = a • v) :
    P = 0 ∨ P = 1 := by
  have hNPv : N (P v) = 0 := by
    rw [show N (P v) = P (N v) from DFunLike.congr_fun hNP.eq v, hNv, map_zero]
  obtain ⟨a, ha⟩ := hker (P v) hNPv
  have ha_idem : IsIdempotentElem a := by
    apply smul_left_injective k hv
    calc
      (a * a) • v = P (P v) := by rw [ha, map_smul, ha, mul_smul]
      _ = a • v := (DFunLike.congr_fun hP.eq v).trans ha
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp ha_idem with hzero | hone
  · left
    apply eq_zero_of_isIdempotent_of_ker_nilpotent N P hN hP hNP
    intro w hw
    obtain ⟨b, rfl⟩ := hker w hw
    simp [ha, hzero]
  · right
    have hQ : 1 - P = 0 := by
      apply eq_zero_of_isIdempotent_of_ker_nilpotent N (1 - P) hN hP.one_sub
        ((Commute.one_right N).sub_right hNP)
      intro w hw
      obtain ⟨b, rfl⟩ := hker w hw
      simp [ha, hone]
    exact (sub_eq_zero.mp hQ).symm

end LinearMap

namespace Module

/-- Every idempotent endomorphism of an indecomposable module is trivial. -/
theorem IsIndecomposable.idempotent_eq_zero_or_one
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (hM : IsIndecomposable R M) (P : Module.End R M) (hP : IsIdempotentElem P) :
    P = 0 ∨ P = 1 := by
  rcases hM.2 P.range P.ker (LinearMap.IsIdempotentElem.isCompl hP) with hrange | hker
  · exact Or.inl (LinearMap.range_eq_bot.mp hrange)
  · right
    have hinj := LinearMap.ker_eq_bot.mp hker
    ext v
    exact hinj (DFunLike.congr_fun hP.eq v)

/-- Triviality of all endomorphism idempotents implies indecomposability. -/
theorem isIndecomposable_of_idempotents
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M]
    (h : ∀ P : Module.End R M, IsIdempotentElem P → P = 0 ∨ P = 1) :
    IsIndecomposable R M := by
  refine ⟨inferInstance, ?_⟩
  intro p q hpq
  rcases h (p.projection q hpq) (Submodule.isIdempotentElem_projection hpq) with hp | hp
  · left
    simpa only [hp, LinearMap.range_zero] using
      (Submodule.range_projection hpq).symm
  · right
    simpa only [hp, Module.End.one_eq_id, LinearMap.ker_id] using
      (Submodule.ker_projection hpq).symm

/-- A nilpotent shift with a one-dimensional kernel gives an indecomposable
polynomial module. Here the polynomial variable acts as `T`. -/
theorem isIndecomposable_aeval_of_nilpotent_sub_one_ker_line
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (T : Module.End k V) (hT : IsNilpotent (T - 1))
    (v : V) (hv : v ≠ 0) (hTv : T v = v)
    (hfixed : ∀ w, T w = w → ∃ a : k, w = a • v) :
    IsIndecomposable k[X] (AEval' T) := by
  let e := AEval'.of T
  let : Nontrivial (AEval' T) := ⟨⟨e v, 0, fun h => hv (e.injective (by simpa using h))⟩⟩
  apply isIndecomposable_of_idempotents
  intro P hP
  let Q : Module.End k V := e.symm.toLinearMap.comp ((P.restrictScalars k).comp e.toLinearMap)
  have hQ (w : V) : Q w = e.symm (P (e w)) := rfl
  have hQidem : IsIdempotentElem Q := by
    ext w
    change e.symm (P (e (e.symm (P (e w))))) = e.symm (P (e w))
    rw [e.apply_symm_apply, show P (P (e w)) = P (e w) from DFunLike.congr_fun hP.eq (e w)]
  have hTQ : Commute T Q := by
    ext w
    change T (e.symm (P (e w))) = e.symm (P (e (T w)))
    rw [← AEval'.of_symm_X_smul, ← AEval'.X_smul_of, P.map_smul]
  have hNQ : Commute (T - 1) Q := hTQ.sub_left (Commute.one_left Q)
  rcases LinearMap.idempotent_eq_zero_or_one_of_nilpotent_ker_line
    (T - 1) Q hT hQidem hNQ v hv (by simp [hTv])
    (fun w hw => hfixed w (sub_eq_zero.mp hw)) with hzero | hone
  · left
    ext w
    apply e.symm.injective
    have h := DFunLike.congr_fun hzero (e.symm w)
    simpa [hQ] using h
  · right
    ext w
    apply e.symm.injective
    have h := DFunLike.congr_fun hone (e.symm w)
    simpa [hQ] using h

end Module
