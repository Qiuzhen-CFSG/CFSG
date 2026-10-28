module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import CFSG.Quasithin.ChapterB.Section03.Offenders.FixedTests

/-!
# Degree eight calculations for Proposition B.3.2

This file records the small structural calculations which are independent of
the global offender list.  In particular, an elementary abelian group of
order eight has binary rank three, and the fixed space of the full
disjoint-transposition group on the even core is the four-dimensional space
of pair-constant vectors.  These facts are used by the classification files.
-/

public section

namespace CFSG.Quasithin.ChapterB.Offenders

open BinaryPermutation Representation.BinaryOffender

/-! The cardinality-to-rank conversion is useful for all concrete models. -/

theorem rank_eq_of_card_eq_two_pow {A : Subgroup (Equiv.Perm (Fin 8))}
    {m : ℕ} (h : Nat.card A = 2 ^ m) : rank A = m := by
  unfold rank
  rw [h, Nat.log_pow (by decide : 1 < 2)]

theorem rank_eq_three_of_isRegularEight {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) : rank A = 3 := by
  apply rank_eq_of_card_eq_two_pow
  simpa [show (2 : ℕ) ^ 3 = 8 by decide] using hA.2.1

theorem regularEight_nontrivial {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) : A ≠ ⊥ := hA.1.1

/-- Rank-nullity in a form convenient for the degree-eight calculations. -/
theorem fixedCodim_eq_of_finrank_fixedSpace
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    {d k : ℕ} (hd : Module.finrank (ZMod 2) V = d)
    (hk : Module.finrank (ZMod 2) (fixedSpace ρ A) = k) :
    fixedCodim ρ A = d - k := by
  have h := fixedCodim_add_finrank ρ A
  rw [hd, hk] at h
  have hk_le' := Submodule.finrank_le (fixedSpace ρ A)
  have hk_le : k ≤ d := by simpa [hk, hd] using hk_le'
  unfold fixedCodim at h ⊢
  omega

/-- The rank of every regular elementary abelian eight subgroup is three. -/
theorem regularEight_rank_three {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) : rank A = 3 := rank_eq_three_of_isRegularEight hA

private theorem d8_generators_commute :
    ∀ x ∈ ({g | ∃ i : Fin 4, g = pairSwap 8 i} : Set (Equiv.Perm (Fin 8))),
      ∀ y ∈ ({g | ∃ i : Fin 4, g = pairSwap 8 i} : Set (Equiv.Perm (Fin 8))),
        x * y = y * x := by
  rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
  fin_cases i <;> fin_cases j <;> decide

private theorem d8_generator_square :
    ∀ x ∈ ({g | ∃ i : Fin 4, g = pairSwap 8 i} : Set (Equiv.Perm (Fin 8))),
      x ^ 2 = 1 := by
  rintro x ⟨i, rfl⟩
  fin_cases i <;> decide

theorem isElementaryAbelian_D8 : IsElementaryAbelian 2 (D 8) := by
  let s : Set (Equiv.Perm (Fin 8)) := {g | ∃ i : Fin 4, g = pairSwap 8 i}
  have hs : D 8 = Subgroup.closure s := by
    ext g
    simp [D, disjointTranspositions, s]
  have hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    intro x hx y hy
    exact d8_generators_commute x hx y hy
  refine { toIsMulCommutative := hs ▸ Subgroup.isMulCommutative_closure hcomm, exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro x
  have hx : x.val ∈ D 8 := x.property
  have hpow : ∀ g : Equiv.Perm (Fin 8), g ∈ Subgroup.closure s → g ^ 2 = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg => exact d8_generator_square g hg
    | one => simp
    | mul g h hg hh hgg hhh =>
        have hmc := Subgroup.isMulCommutative_closure hcomm
        have hgh : g * h = h * g := by
          exact congrArg Subtype.val
            ((IsMulCommutative.is_comm (M := Subgroup.closure s)).comm
              (⟨g, hg⟩ : Subgroup.closure s) ⟨h, hh⟩)
        calc
          (g * h) ^ 2 = g * h * (g * h) := by rw [pow_two]
          _ = g * (h * g) * h := by simp [mul_assoc]
          _ = g * (g * h) * h := by rw [hgh]
          _ = (g * g) * (h * h) := by simp [mul_assoc]
          _ = 1 := by rw [← pow_two, ← pow_two, hgg, hhh]; simp
    | inv g hg hgg =>
        rw [inv_pow, hgg]
        simp
  exact Subtype.ext (hpow x.val (hs ▸ hx))

theorem isElementaryTwo_D8 : IsElementaryTwo (D 8) := by
  refine ⟨?_, isElementaryAbelian_D8⟩
  intro h
  let i0 : Fin 4 := 0
  have hp : pairSwap 8 i0 ∈ D 8 :=
    pairSwap_mem (n := 8) (m := 4) i0 (by simp [i0])
  rw [h] at hp
  have hn : pairSwap 8 i0 ≠ 1 := by decide
  exact hn hp

private def pairValues : core (Fin 8) →ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  { toFun := fun v i => v.val ⟨2 * i.val, by omega⟩
    map_add' := by intro v w; ext i; simp
    map_smul' := by intro c v; ext i; simp }

private def pairConstant (x : Fin 4 → ZMod 2) : Full (Fin 8) :=
  fun j => x ⟨j.val / 2, by omega⟩

private theorem pairConstant_core (x : Fin 4 → ZMod 2) :
    pairConstant x ∈ core (Fin 8) := by
  rw [mem_core]
  simp only [Fin.sum_univ_succ]
  norm_num [pairConstant]
  ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, add_zero]

private theorem pairConstant_fixed (x : Fin 4 → ZMod 2) :
    (⟨pairConstant x, pairConstant_core x⟩ : core (Fin 8)) ∈
      fixedSpace (coreRepresentation (Fin 8)) (D 8) := by
  rw [core_fixed_disjointTranspositions_iff]
  intro i hi
  have hi4 : i.val < 4 := by exact i.isLt
  have hdiv : (2 * i.val + 1) / 2 = i.val := by omega
  simp [pairConstant, hdiv]

private theorem pairValues_fixed_injective :
    Function.Injective
      (pairValues.comp (fixedSpace (coreRepresentation (Fin 8)) (D 8)).subtype) := by
  intro v w h
  apply Subtype.ext
  apply Subtype.ext
  funext j
  let i : Fin 4 := ⟨j.val / 2, by omega⟩
  have hj : j = ⟨2 * i.val, by omega⟩ ∨ j = ⟨2 * i.val + 1, by omega⟩ := by
    fin_cases j <;> simp [i]
  rcases hj with hj | hj
  · rw [hj]
    simpa [pairValues] using congrFun h i
  · rw [hj]
    have hpv := (core_fixed_disjointTranspositions_iff 8 4 v.val).mp v.property
      ⟨i, by omega⟩
    have hpw := (core_fixed_disjointTranspositions_iff 8 4 w.val).mp w.property
      ⟨i, by omega⟩
    calc
      v.val.val ⟨2 * i.val + 1, by omega⟩ = v.val.val ⟨2 * i.val, by omega⟩ := (hpv (by omega)).symm
      _ = w.val.val ⟨2 * i.val, by omega⟩ := by simpa [pairValues] using congrFun h i
      _ = w.val.val ⟨2 * i.val + 1, by omega⟩ := hpw (by omega)

theorem fixedSpace_core_D8_finrank :
    Module.finrank (ZMod 2)
      (fixedSpace (coreRepresentation (Fin 8)) (D 8)) = 4 := by
  let f := pairValues.comp (fixedSpace (coreRepresentation (Fin 8)) (D 8)).subtype
  have hf : Function.Bijective f := by
    refine ⟨pairValues_fixed_injective, ?_⟩
    intro x
    let vc : core (Fin 8) := ⟨pairConstant x, pairConstant_core x⟩
    refine ⟨⟨vc, ?_⟩, ?_⟩
    · exact pairConstant_fixed x
    · ext i
      change pairConstant x ⟨2 * i.val, by omega⟩ = x i
      simp [pairConstant]
  let e : fixedSpace (coreRepresentation (Fin 8)) (D 8) ≃ₗ[ZMod 2]
      (Fin 4 → ZMod 2) := LinearEquiv.ofBijective f hf
  rw [e.finrank_eq]
  simp

theorem fixedCodim_core_D8 :
    fixedCodim (coreRepresentation (Fin 8)) (D 8) = 3 := by
  apply fixedCodim_eq_of_finrank_fixedSpace (coreRepresentation (Fin 8)) (D 8)
    (d := 7) (k := 4)
  · simpa using (finrank_core (Fin 8))
  · exact fixedSpace_core_D8_finrank

/-! Named interfaces used by the Section 03 assembly. -/

theorem rank_disjointTranspositions_eight (m : ℕ)
    (hcard : Nat.card (disjointTranspositions 8 m) = 2 ^ m) :
    rank (disjointTranspositions 8 m) = m :=
  rank_eq_of_card_eq_two_pow hcard

theorem fixedCodim_natural_D8_of_finrank
    (h : Module.finrank (ZMod 2)
      (fixedSpace (naturalRepresentation (Fin 8)) (D 8)) = 3) :
    fixedCodim (naturalRepresentation (Fin 8)) (D 8) = 3 := by
  apply fixedCodim_eq_of_finrank_fixedSpace (naturalRepresentation (Fin 8)) (D 8)
    (d := 6) (k := 3)
  · simpa using (finrank_natural_even (Fin 8) (by decide : Even 8))
  · exact h

theorem D8_strong_core (hr : rank (D 8) = 4) :
    IsStrongOffender (coreRepresentation (Fin 8)) (D 8) := by
  refine ⟨⟨by
    intro h
    let i0 : Fin 4 := 0
    have hp : pairSwap 8 i0 ∈ D 8 :=
      pairSwap_mem (n := 8) (m := 4) i0 (by simp [i0])
    rw [h] at hp
    have hn : pairSwap 8 i0 ≠ 1 := by decide
    exact hn hp, isElementaryAbelian_D8⟩, ?_⟩
  rw [fixedCodim_core_D8]
  simp [hr]

end CFSG.Quasithin.ChapterB.Offenders
