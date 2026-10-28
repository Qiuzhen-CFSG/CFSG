module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Reduction
public import Mathlib.GroupTheory.Perm.Closure
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.Algebra.Pointwise.Stabilizer

/-!
# An actual six-point action of each Held local quotient

Each literal ATLAS local subgroup preserves six explicitly listed letters
of the fixed degree-2058 representation. The two generator restrictions are
checked against those exact permutations. Restriction gives a homomorphism
on the entire local subgroup, not just a presentation or an order match.

A six-cycle and an adjacent transposition prove that its image is S₆.
The two-core maps to a normal two-subgroup of S₆, which is trivial, so the
action factors through the actual intrinsic quotient M/O₂(M). The kernel
of this quotient action is not asserted to be trivial or to have order three.
Those facts and the stabilizers needed for the pair calculation are separate.

Sources: the unchanged ATLAS HeG1-p2058B0 permutations and max3/max4 programs;
GLS3 Table 5.3p. The six-letter sets were found by orbit exploration; every
used coordinate identity below is checked by Lean's kernel. Since the
carrier already inverts GAP permutations, the displayed coordinate maps
are the inverse GAP restrictions.
-/

public section

open Subgroup
open scoped Pointwise
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner
namespace SixPoint

/-- The six letters, numbered from zero, in the fixed Held representation. -/
@[expose] def points (i : Bool) : Fin 6 → Fin 2058 :=
  if i then ![619, 1004, 1376, 1485, 1671, 1739] else ![480, 557, 719, 892, 1016, 1444]

theorem points_injective (i : Bool) : Function.Injective (points i) := by
  cases i <;> decide

/-- Restriction of the first ATLAS generator. -/
@[expose] def first (i : Bool) : Equiv.Perm (Fin 6) :=
  if i then Equiv.swap 0 5 else Equiv.swap 2 5

/-- Restriction of the max3/max4 word in the same coordinates. -/
@[expose] def second (i : Bool) : Equiv.Perm (Fin 6) where
  toFun := if i then ![0, 4, 5, 1, 2, 3] else ![2, 4, 5, 1, 0, 3]
  invFun := if i then ![0, 3, 4, 5, 1, 2] else ![4, 3, 0, 5, 1, 2]
  left_inv := by cases i <;> decide
  right_inv := by cases i <;> decide

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
theorem first_points (i : Bool) (t : Fin 6) :
    representation Held.a (points i t) = points i (first i t) := by
  cases i <;> fin_cases t <;> decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
theorem second_points (i : Bool) (t : Fin 6) :
    representation (localWord i) (points i t) = points i (second i t) := by
  cases i <;> fin_cases t <;> decide +kernel

private theorem stabilizes_points (i : Bool) (g : Held.He) (v : Equiv.Perm (Fin 6))
    (hv : ∀ t, representation g (points i t) = points i (v t)) :
    representation g ∈ MulAction.stabilizer (Equiv.Perm (Fin 2058)) (Set.range (points i)) := by
  change representation g • Set.range (points i) = Set.range (points i)
  rw [← Set.image_smul, ← Set.range_comp]
  change Set.range (fun t => representation g (points i t)) = _
  simp_rw [hv]
  exact v.surjective.range_comp _

theorem local_preserves_points (i : Bool) :
    localOvergroup i ≤
      (MulAction.stabilizer (Equiv.Perm (Fin 2058)) (Set.range (points i))).comap representation := by
  apply (closure_le _).mpr
  intro g hg
  rcases hg with rfl | rfl
  · exact stabilizes_points i _ (first i) (first_points i)
  · exact stabilizes_points i _ (second i) (second_points i)

private theorem preserves_points_iff (i : Bool) (g : localOvergroup i) (x : Fin 2058) :
    representation g.val x ∈ Set.range (points i) ↔ x ∈ Set.range (points i) := by
  have hg : representation g.val • Set.range (points i) = Set.range (points i) :=
    local_preserves_points i g.property
  conv_lhs => rw [← hg]
  exact Set.smul_mem_smul_set_iff

private noncomputable def pointEquiv (i : Bool) : Fin 6 ≃ Set.range (points i) :=
  Equiv.ofInjective (points i) (points_injective i)

private noncomputable def perm (i : Bool) (g : localOvergroup i) : Equiv.Perm (Fin 6) :=
  (pointEquiv i).symm.permCongr ((representation g.val).subtypePerm (preserves_points_iff i g))

private theorem perm_points (i : Bool) (g : localOvergroup i) (t : Fin 6) :
    points i (perm i g t) = representation g.val (points i t) := by
  change ((pointEquiv i) (perm i g t)).val = _
  simp only [perm, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl

/-- The restriction homomorphism on the actual local subgroup. -/
noncomputable def action (i : Bool) : localOvergroup i →* Equiv.Perm (Fin 6) where
  toFun := perm i
  map_one' := by
    apply Equiv.ext
    intro t
    apply points_injective i
    rw [perm_points]
    rfl
  map_mul' g h := by
    apply Equiv.ext
    intro t
    apply points_injective i
    rw [perm_points]
    change representation (g.val * h.val) (points i t) = points i (perm i g (perm i h t))
    rw [perm_points, perm_points, map_mul]
    rfl

/-- The action agrees pointwise with the fixed faithful Held representation. -/
theorem action_points (i : Bool) (g : localOvergroup i) (t : Fin 6) :
    points i (action i g t) = representation g.val (points i t) :=
  perm_points i g t

theorem action_first (i : Bool) : action i ⟨Held.a, a_mem_localOvergroup i⟩ = first i := by
  apply Equiv.ext
  intro t
  apply points_injective i
  exact (action_points i ⟨Held.a, a_mem_localOvergroup i⟩ t).trans (first_points i t)

theorem action_second (i : Bool) : action i ⟨localWord i, localWord_mem_localOvergroup i⟩ = second i := by
  apply Equiv.ext
  intro t
  apply points_injective i
  exact (action_points i ⟨localWord i, localWord_mem_localOvergroup i⟩ t).trans (second_points i t)


/-- The two checked restrictions generate the full symmetric group. -/
theorem action_surjective (i : Bool) : Function.Surjective (action i) := by
  apply (action i).range_eq_top.mp
  have ha : first i ∈ (action i).range := ⟨_, action_first i⟩
  have hb : second i ∈ (action i).range := ⟨_, action_second i⟩
  let c := if i then first i * second i else second i
  let t : Fin 6 := if i then 0 else 2
  have hc : c ∈ (action i).range := by
    cases i
    · exact hb
    · exact (action true).range.mul_mem ha hb
  let l : List (Fin 6) := if i then [0, 5, 3, 1, 4, 2] else [0, 2, 5, 3, 1, 4]
  have hcform : c = l.formPerm := by cases i <;> decide +kernel
  have hcycle : c.IsCycle := by
    rw [hcform]
    exact List.isCycle_formPerm (by cases i <;> decide) (by cases i <;> decide)
  have hsupp : c.support = Finset.univ := by cases i <;> decide +kernel
  have hswap : Equiv.swap t (c t) = first i := by cases i <;> decide +kernel
  apply top_unique
  rw [← Equiv.Perm.closure_cycle_adjacent_swap hcycle hsupp t]
  apply (closure_le _).mpr
  intro z hz
  rcases hz with rfl | rfl
  · exact hc
  · rwa [hswap]

private theorem symmetricSix_twoCore : pCore 2 (Equiv.Perm (Fin 6)) = ⊥ := by
  by_contra hn
  have hnt : Nontrivial (pCore 2 (Equiv.Perm (Fin 6))) := (nontrivial_iff_ne_bot _).mpr hn
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 6)) hnt
  have hdiv : 360 ∣ Nat.card (pCore 2 (Equiv.Perm (Fin 6))) := by
    have hc : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    exact hc ▸ card_dvd_of_le hle
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := Equiv.Perm (Fin 6))).exists_card_eq
  have hthree : 3 ∣ 2 ^ n := hn ▸ (dvd_trans (by decide : 3 ∣ 360) hdiv)
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hthree)

/-- A surjective symmetric-six action kills the intrinsic local two-core. -/
theorem twoCore_le_ker_action (i : Bool) : pCore 2 (localOvergroup i) ≤ (action i).ker := by
  have hn : ((pCore 2 (localOvergroup i)).map (action i)).Normal :=
    Subgroup.Normal.map inferInstance (action i) (action_surjective i)
  have hm : (pCore 2 (localOvergroup i)).map (action i) ≤ pCore 2 (Equiv.Perm (Fin 6)) :=
    le_sSup ⟨hn, pCore_isPGroup.map (action i)⟩
  rw [symmetricSix_twoCore] at hm
  exact map_le_iff_le_comap.mp hm

/-- The resulting action of M/O₂(M), induced by restriction of its elements. -/
@[expose] noncomputable def quotientAction (i : Bool) : LocalQuotient i →* Equiv.Perm (Fin 6) :=
  QuotientGroup.lift (pCore 2 (localOvergroup i)) (action i) (twoCore_le_ker_action i)

theorem quotientAction_mk (i : Bool) (g : localOvergroup i) :
    quotientAction i (localQuotientMap i g) = action i g := rfl

/-- Factoring out the two-core preserves the full six-point image. -/
theorem quotientAction_surjective (i : Bool) : Function.Surjective (quotientAction i) := by
  intro p
  obtain ⟨g, rfl⟩ := action_surjective i p
  exact ⟨localQuotientMap i g, rfl⟩

end SixPoint
end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner
