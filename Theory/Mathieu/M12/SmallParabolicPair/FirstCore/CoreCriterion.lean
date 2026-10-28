module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.Sylow
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finite.Perm

/-!
# Two-cores of groups of order 192 with an S₃ quotient

The kernel has order 32. The image of the two-core is trivial since S₃ has
trivial two-core. Adapted from `Stellmacher.SectionNine.NineFiveM12CoreCriterion`.
-/

@[expose] public section

noncomputable section

namespace Sporadic.Mathieu.M12SmallPair.FirstCore

theorem local_perm_three_core_eq_bot : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
  let sylow : Sylow 2 (Equiv.Perm (Fin 3)) := default
  have hsylow : Nat.card sylow = 2 := by
    rw [sylow.card_eq_multiplicity, Nat.card_perm, Nat.card_fin]
    norm_num [Nat.factorial]
    have hfactor : Nat.factorization 6 2 = 1 := by
      change Nat.factorization (3 * 2) 2 = 1
      rw [Nat.factorization_mul (by decide) (by decide)]
      norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
    norm_num [hfactor]
  have hcoreLe : pCore 2 (Equiv.Perm (Fin 3)) ≤ sylow :=
    pCore_isPGroup.le_sylow_of_normal sylow
  have hdiv := Subgroup.card_dvd_of_le hcoreLe
  rw [hsylow] at hdiv
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
  · exact Subgroup.card_eq_one.mp hone
  · have hcentral := Subgroup.central_of_normal_card_two
      (pCore 2 (Equiv.Perm (Fin 3))) htwo
    apply (pCore 2 (Equiv.Perm (Fin 3))).eq_bot_iff_forall.mpr
    intro element hmem
    have htest : ∀ permutation : Equiv.Perm (Fin 3),
        (∀ other : Equiv.Perm (Fin 3), other * permutation = permutation * other) →
          permutation = 1 := by decide +kernel
    exact htest element (Subgroup.mem_center_iff.mp (hcentral hmem))

/-- The kernel of an S₃ quotient of a group of order 192 is its two-core. -/
theorem core_eq_ker_of_surjective_perm_three
    {G : Type*} [Group G] [Finite G]
    (hgroup : Nat.card G = 192) (action : G →* Equiv.Perm (Fin 3))
    (hsurjective : Function.Surjective action) : pCore 2 G = action.ker := by
  have hker : Nat.card action.ker = 32 := by
    have hmul := action.ker.card_mul_index
    rw [Subgroup.index_ker, action.range_eq_top_of_surjective hsurjective,
      Subgroup.card_top, Nat.card_perm, Nat.card_fin, hgroup] at hmul
    norm_num [Nat.factorial] at hmul
    change Nat.card action.ker * 6 = 192 at hmul
    omega
  have hkerLe : action.ker ≤ pCore 2 G :=
    le_sSup ⟨inferInstance, IsPGroup.of_card (n := 5) hker⟩
  have himageNormal : ((pCore 2 G).map action).Normal :=
    Subgroup.Normal.map inferInstance action hsurjective
  have himageLe : (pCore 2 G).map action ≤ pCore 2 (Equiv.Perm (Fin 3)) :=
    le_sSup ⟨himageNormal, pCore_isPGroup.map action⟩
  apply le_antisymm ?_ hkerLe
  intro element hmem
  apply MonoidHom.mem_ker.mpr
  have himage := himageLe (Subgroup.mem_map.mpr ⟨element, hmem, rfl⟩)
  simpa only [local_perm_three_core_eq_bot, Subgroup.mem_bot] using himage

end Sporadic.Mathieu.M12SmallPair.FirstCore
