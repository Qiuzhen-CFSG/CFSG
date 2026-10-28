module

public import Theory.SpecificGroups.Tits.Atlas1600Action
public import Theory.SpecificGroups.Tits.Atlas1600OrderLevel0Data
public import Theory.SpecificGroups.Tits.Atlas1600PrimitiveData
public import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Primitivity of the Atlas degree-1600 action

The level-zero representatives establish transitivity. A block containing 0 is
invariant under the certified subgroup H1 fixing 0. Four connected point sets
have sizes 1, 351, 936, and 312. Of their unions containing 0, only the singleton
and the whole space have cardinality dividing 1600, so every block is trivial.
The point witnesses originate in `refs/original/n-group-global/atlas-tits-p1600-{a,b}.g`.
-/

namespace Tits
open Atlas1600OrderCertificate Atlas1600PrimitiveCertificate Theory.GroupTheory
open scoped Pointwise

public instance atlas1600_isPretransitive :
    MulAction.IsPretransitive Atlas1600Group (Fin 1600) := by
  apply MulAction.IsPretransitive.of_orbit (x₀ := (0 : Fin 1600))
  intro x
  obtain ⟨r, rfl⟩ := (Finite.surjective_of_injective L0Point_injective) x
  exact ⟨⟨L0Rep r, H0_eq_atlas ▸ L0Rep_mem r⟩, L0Rep_point r⟩

private theorem block_gen_mem_iff {B : Set (Fin 1600)}
    (hB : MulAction.IsBlock Atlas1600Group B) (h0 : 0 ∈ B)
    (i : Fin 6) (x : Fin 1600) : L1Gen i x ∈ B ↔ x ∈ B := by
  have hi : L1Gen i ∈ H1 := by
    exact evalWord_mem_wordSubgroup L1Gen L1Inv L1Inv_spec [i]
  let g : Atlas1600Group := ⟨L1Gen i, H0_eq_atlas ▸ H1_le hi⟩
  have hg : g • (0 : Fin 1600) = 0 := H1_fix ⟨L1Gen i, hi⟩
  have he : g • B = B := hB.smul_eq_of_mem h0 (by simpa only [hg] using h0)
  change g • x ∈ B ↔ x ∈ B
  simpa only [he] using (Set.smul_mem_smul_set_iff (a := g) (x := x) (s := B))

private theorem block_mem_root {B : Set (Fin 1600)}
    (hB : MulAction.IsBlock Atlas1600Group B) (h0 : 0 ∈ B)
    (x : Fin 1600) : x ∈ B ↔ root (color x) ∈ B := by
  suffices ∀ n, ∀ x, (depth x).val = n → (x ∈ B ↔ root (color x) ∈ B) from
    this _ x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hx
    rcases tree x with he | ⟨hd, hc, he⟩
    · exact iff_of_eq (congrArg (fun y => y ∈ B) he)
    · have hp := ih (depth (parent x)).val (hx ▸ hd) (parent x) rfl
      rw [hc] at hp
      calc
        x ∈ B ↔ L1Gen (edge x) (parent x) ∈ B := by rw [he]
        _ ↔ parent x ∈ B := block_gen_mem_iff hB h0 _ _
        _ ↔ root (color x) ∈ B := hp

/-- The canonical Atlas degree-1600 permutation action is primitive. -/
public instance atlas1600_isPreprimitive :
    MulAction.IsPreprimitive Atlas1600Group (Fin 1600) := by
  apply MulAction.IsPreprimitive.of_isTrivialBlock_base (0 : Fin 1600)
  intro B h0 hB
  classical
  let a := decide (root 1 ∈ B)
  let b := decide (root 2 ∈ B)
  let c := decide (root 3 ∈ B)
  have hBc : B = (candidate a b c : Set (Fin 1600)) := by
    ext x
    have hm := block_mem_root hB h0 x
    simp only [Finset.mem_coe, candidate, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hm]
    generalize color x = i
    fin_cases i
    · simpa only [selected, root] using (iff_true_intro h0)
    · exact (decide_eq_true_iff).symm
    · exact (decide_eq_true_iff).symm
    · exact (decide_eq_true_iff).symm
  have hd : B.ncard ∣ 1600 := by
    simpa using hB.ncard_dvd_card ⟨0, h0⟩
  rw [hBc, Set.ncard_coe_finset] at hd
  rcases candidate_card a b c hd with h | h
  · left
    apply Set.ncard_le_one_iff_subsingleton.mp
    rw [hBc, Set.ncard_coe_finset, h]
  · right
    apply (Set.eq_univ_iff_ncard B).mpr
    simpa only [hBc, Set.ncard_coe_finset, Nat.card_fin] using h

end Tits
