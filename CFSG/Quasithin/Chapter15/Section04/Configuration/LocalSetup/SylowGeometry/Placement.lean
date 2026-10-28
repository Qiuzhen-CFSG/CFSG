module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.Geometry
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.Transfer
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.BaumannTwoOvergroupTransport

/-!
# Placement and index restrictions in the contrary Sylow case

Aschbacher–Smith, combined manuscript (1 March 2004), 15.4.20,
printed pp.1163–1164. A two-subgroup containing `Baum(T)` has the same
Baumann subgroup and normalizes it. The genuine 15.4.16 normalizer bound
therefore places it in both maximal two-local overgroups. Uniqueness of
those overgroups prevents any member of `H(I)` from containing all of `T`.
Once a larger Sylow subgroup has been placed inside `T`, the index bound
forces both indices to be two, and at least one factor is moved.

The conjugation that places this subgroup inside `T`, including transport of
the factors, is still required by the source assembly. Containment in both
maximal locals alone is not asserted to give containment in `T`.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup
open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- Baumann weak closure places every two-overgroup of `T₀` in both maximal locals. -/
theorem two_overgroup_baumann_placement (T : Sylow 2 G) {T₀ U M₁ M₂ : Subgroup G}
    (hBU : ChapterB.baumann (T : Subgroup G) ≤ T₀)
    (hT₀U : T₀ ≤ U) (hU : IsPGroup 2 U)
    (hM₁ : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M₁)
    (hM₂ : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M₂) :
    U ≤ M₁ ⊓ M₂ ∧ ChapterB.baumann U = ChapterB.baumann (T : Subgroup G) := by
  have hUN := Stellmacher.twoSubgroup_le_normalizer_baumann T U hU (hBU.trans hT₀U)
  refine ⟨le_inf (hUN.trans hM₁) (hUN.trans hM₂), ?_⟩
  exact (Stellmacher.twoSubgroup_thompson_baumann_eq T U hU (hBU.trans hT₀U)).2

/-- Both indices in a proper two-step chain with total index at most four equal two. -/
theorem indices_two_of_intermediate {T₀ U T : Subgroup G} (h₀ : T₀ < U) (hU : U < T)
    (hindex : T₀.relIndex T ≤ 4) : U.relIndex T = 2 ∧ T₀.relIndex U = 2 := by
  have hprod := relIndex_mul_relIndex T₀ U T h₀.le hU.le
  have hpos₀ : 0 < T₀.relIndex U := Nat.card_pos
  have hposU : 0 < U.relIndex T := Nat.card_pos
  have hne₀ : T₀.relIndex U ≠ 1 := fun heq => h₀.not_ge (relIndex_eq_one.mp heq)
  have hneU : U.relIndex T ≠ 1 := fun heq => hU.not_ge (relIndex_eq_one.mp heq)
  have hge₀ : 2 ≤ T₀.relIndex U := by omega
  have hgeU : 2 ≤ U.relIndex T := by omega
  constructor <;> nlinarith

omit [Finite G] in
/-- Every larger subgroup in `T` moves at least one of the chosen factors. -/
theorem larger_subgroup_moves_factor (d : Source.Geometry G)
    (hX : ∀ i, (d.T : Subgroup G) ⊓ normalizer (d.X i : Set G) =
      (d.T : Subgroup G) ⊓ normalizer (d.X false : Set G))
    (hY : ∀ j, (d.T : Subgroup G) ⊓ normalizer (d.Y j : Set G) =
      (d.T : Subgroup G) ⊓ normalizer (d.Y false : Set G))
    {U : Subgroup G} (h₀ : d.T₀ < U) (hUT : U ≤ (d.T : Subgroup G)) (i j : Bool) :
    ¬ U ≤ normalizer (d.X i : Set G) ∨ ¬ U ≤ normalizer (d.Y j : Set G) := by
  by_contra h
  push Not at h
  apply h₀.not_ge
  rw [T₀_eq_for_choices d hX hY i j]
  exact le_inf (le_inf hUT h.1) (le_inf hUT h.2)

omit [Finite G] in
/-- A proper intersection containing a subgroup of prime index equals that subgroup. -/
theorem intersection_eq_of_prime_index {A B P L M : Subgroup G} {p : ℕ} (hp : Nat.Prime p)
    (hPA : P ≤ A) (hPB : P ≤ B) (hindex : P.relIndex A = p)
    (hLA : L ≤ A) (hBM : B ≤ M) (hLM : ¬ L ≤ M) : A ⊓ B = P := by
  have hprod := relIndex_mul_relIndex P (A ⊓ B) A (le_inf hPA hPB) inf_le_left
  rw [hindex] at hprod
  have hdvd : P.relIndex (A ⊓ B) ∣ p := ⟨(A ⊓ B).relIndex A, hprod.symm⟩
  rcases hp.eq_one_or_self_of_dvd _ hdvd with hi | hi
  · exact le_antisymm (relIndex_eq_one.mp hi) (le_inf hPA hPB)
  · have hright : (A ⊓ B).relIndex A = 1 := by
      rw [hi] at hprod
      exact (Nat.mul_left_cancel hp.pos (hprod.trans (Nat.mul_one p).symm))
    exact (hLM (hLA.trans ((relIndex_eq_one.mp hright).trans (inf_le_right.trans hBM)))).elim

omit [Finite G] in
/-- The common subgroup in the ensuing triple, uniformly over the four choices.
The index-three input is to be supplied from the factor quotient in 15.4.12. -/
theorem factor_intersections_eq_T₀ (d : Source.Geometry G)
    (hT₂ : (d.T : Subgroup G) ≤ d.M₂)
    (houtside : ∀ i, ¬ d.X i ≤ d.M₂)
    (hindex : ∀ i, d.T₀.relIndex (d.G₁ i) = 3) :
    ∀ i j, d.G₁ i ⊓ d.G₂ j = d.T₀ := by
  intro i j
  have hY : d.Y j ≤ d.wholeY := by
    cases j
    · exact le_sup_left
    · exact le_sup_right
  have hG₂ : d.G₂ j ≤ d.M₂ :=
    sup_le (hY.trans le_normalizer) (d.T₀_le_T.trans hT₂)
  exact intersection_eq_of_prime_index (by decide : Nat.Prime 3)
    le_sup_right le_sup_right (hindex i) le_sup_left hG₂ (houtside i)

/-- No member of `H(I)` can contain the whole ambient Sylow subgroup: otherwise
the distinct uniqueness overgroups would coincide. -/
theorem sylow_not_le_HOver (d : Source.Geometry G)
    (hXgen : ∀ i, d.X i ⊔ (d.T : Subgroup G) = d.wholeX ⊔ (d.T : Subgroup G))
    (hYgen : ∀ j, d.Y j ⊔ (d.T : Subgroup G) = d.wholeY ⊔ (d.T : Subgroup G))
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ M → M = d.M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      d.wholeY ⊔ (d.T : Subgroup G) ≤ M → M = d.M₂)
    (hne : d.M₁ ≠ d.M₂) {H : Subgroup G} (i j : Bool)
    (hH : H ∈ Chapter1.HOver G (d.I i j : Set G)) :
    ¬ (d.T : Subgroup G) ≤ H := by
  intro hTH
  have hlocal : IsTwoLocal (normalizer (H.pCoreIn 2 : Set G)) :=
    ⟨H.pCoreIn 2, hH.1, isPGroup_pCoreIn 2 H, rfl⟩
  obtain ⟨M, hNM, hM⟩ := Finite.exists_le_maximal hlocal
  have hHM : H ≤ M :=
    (core_normalizer_mem_HOver hH.1).2.trans hNM
  have hXH : d.wholeX ⊔ (d.T : Subgroup G) ≤ H :=
    (hXgen i) ▸ sup_le ((d.X_le_I i j).trans hH.2) hTH
  have hYH : d.wholeY ⊔ (d.T : Subgroup G) ≤ H :=
    (hYgen j) ▸ sup_le ((d.Y_le_I i j).trans hH.2) hTH
  exact hne ((huniqueX M hM (hXH.trans hHM)).symm.trans
    (huniqueY M hM (hYH.trans hHM)))

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
