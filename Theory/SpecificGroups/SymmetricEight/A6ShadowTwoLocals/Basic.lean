module

public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# The two block stabilizers in C₂ × S₈

The pair partition is `{01,23,45,67}` and the four-point partition is
`{0123,4567}`. Preserving either partition means preserving its equivalence
relation, given by integer division by two or four. These are the actual
permutation stabilizers, lifted to C₂ × S₈ by the second projection.

Adjacent transpositions, with the middle one obtained by conjugation, prove
that the two stabilizers generate S₈. The central C₂ proves that both lifted
stabilizers have nontrivial two-core. The order of a Sylow subgroup of the
whole product is 256.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 2.5.26, printed p.569. Maximality is understood
among proper overgroups, since the whole product normalizes its central C₂.
-/

@[expose] public section

namespace Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals

open Subgroup

abbrev S8 := Equiv.Perm (Fin 8)
abbrev C2 := Multiplicative (ZMod 2)
abbrev X := C2 × S8

/-- Permutations preserving the fibers of a block-index function. -/
def blockStabilizer {B : Type*} (b : Fin 8 → B) : Subgroup S8 where
  carrier := {g | ∀ i j, b (g i) = b (g j) ↔ b i = b j}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' {g h} hg hh i j := (hg (h i) (h j)).trans (hh i j)
  inv_mem' {g} hg i j := by
    simpa using (hg (g⁻¹ i) (g⁻¹ j)).symm

/-- The stabilizer of the four unordered pairs `{01,23,45,67}`. -/
def pairStabilizer : Subgroup S8 := blockStabilizer (fun i => i.val / 2)

/-- The stabilizer of the two unordered four-point blocks `{0123,4567}`. -/
def fourStabilizer : Subgroup S8 := blockStabilizer (fun i => i.val / 4)

/-- The common stabilizer of the nested pair and four-point partitions. -/
def flagStabilizer : Subgroup S8 := pairStabilizer ⊓ fourStabilizer

def pairOvergroup : Subgroup X := (⊤ : Subgroup C2).prod pairStabilizer
def fourOvergroup : Subgroup X := (⊤ : Subgroup C2).prod fourStabilizer
def flagGroup : Subgroup X := (⊤ : Subgroup C2).prod flagStabilizer

instance (g : S8) : Decidable (g ∈ pairStabilizer) :=
  inferInstanceAs (Decidable (∀ i j : Fin 8, (g i).val / 2 = (g j).val / 2 ↔ i.val / 2 = j.val / 2))
instance (g : S8) : Decidable (g ∈ fourStabilizer) :=
  inferInstanceAs (Decidable (∀ i j : Fin 8, (g i).val / 4 = (g j).val / 4 ↔ i.val / 4 = j.val / 4))
instance (g : S8) : Decidable (g ∈ flagStabilizer) :=
  inferInstanceAs (Decidable (g ∈ pairStabilizer ∧ g ∈ fourStabilizer))

@[simp] theorem mem_pairStabilizer (g : S8) : g ∈ pairStabilizer ↔
    ∀ i j : Fin 8, (g i).val / 2 = (g j).val / 2 ↔ i.val / 2 = j.val / 2 := Iff.rfl

@[simp] theorem mem_fourStabilizer (g : S8) : g ∈ fourStabilizer ↔
    ∀ i j : Fin 8, (g i).val / 4 = (g j).val / 4 ↔ i.val / 4 = j.val / 4 := Iff.rfl

@[simp] theorem mem_pairOvergroup (g : X) : g ∈ pairOvergroup ↔ g.2 ∈ pairStabilizer := by
  simp [pairOvergroup, Subgroup.mem_prod]

@[simp] theorem mem_fourOvergroup (g : X) : g ∈ fourOvergroup ↔ g.2 ∈ fourStabilizer := by
  simp [fourOvergroup, Subgroup.mem_prod]

theorem flagGroup_le_pairOvergroup : flagGroup ≤ pairOvergroup := by
  intro g hg
  exact ⟨hg.1, hg.2.1⟩

theorem flagGroup_le_fourOvergroup : flagGroup ≤ fourOvergroup := by
  intro g hg
  exact ⟨hg.1, hg.2.2⟩

theorem overgroups_inf : pairOvergroup ⊓ fourOvergroup = flagGroup := by
  ext g
  change (True ∧ g.2 ∈ pairStabilizer) ∧ (True ∧ g.2 ∈ fourStabilizer) ↔
    True ∧ g.2 ∈ pairStabilizer ∧ g.2 ∈ fourStabilizer
  tauto

theorem pairOvergroup_ne_top : pairOvergroup ≠ ⊤ := by
  intro h
  have hmem : ((1 : C2), Equiv.swap (1 : Fin 8) 2) ∈ pairOvergroup := h ▸ mem_top _
  exact (by decide : Equiv.swap (1 : Fin 8) 2 ∉ pairStabilizer) hmem.2

theorem fourOvergroup_ne_top : fourOvergroup ≠ ⊤ := by
  intro h
  have hmem : ((1 : C2), Equiv.swap (3 : Fin 8) 4) ∈ fourOvergroup := h ▸ mem_top _
  exact (by decide : Equiv.swap (3 : Fin 8) 4 ∉ fourStabilizer) hmem.2

/-- Moving two complete pairs carries an internal transposition across the
boundary of the four-point blocks. -/
private def cross : S8 := Equiv.swap 0 4 * Equiv.swap 1 5

private theorem middle_swap_mem : Equiv.swap (3 : Fin 8) 4 ∈ pairStabilizer ⊔ fourStabilizer := by
  have hc : cross ∈ pairStabilizer ⊔ fourStabilizer := Subgroup.mem_sup_left (by decide)
  have hs : Equiv.swap (3 : Fin 8) 0 ∈ pairStabilizer ⊔ fourStabilizer := Subgroup.mem_sup_right (by decide)
  have he : cross * Equiv.swap (3 : Fin 8) 0 * cross⁻¹ = Equiv.swap (3 : Fin 8) 4 := by decide
  exact he ▸ (pairStabilizer ⊔ fourStabilizer).mul_mem
    ((pairStabilizer ⊔ fourStabilizer).mul_mem hc hs)
    ((pairStabilizer ⊔ fourStabilizer).inv_mem hc)

theorem stabilizers_sup : pairStabilizer ⊔ fourStabilizer = ⊤ := by
  have hgen := Subgroup.closure_eq_top_of_mclosure_eq_top
    (Equiv.Perm.mclosure_swap_castSucc_succ 7)
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact Subgroup.mem_sup_right (show Equiv.swap (0 : Fin 8) 1 ∈ fourStabilizer from by decide)
  · exact Subgroup.mem_sup_right (show Equiv.swap (1 : Fin 8) 2 ∈ fourStabilizer from by decide)
  · exact Subgroup.mem_sup_right (show Equiv.swap (2 : Fin 8) 3 ∈ fourStabilizer from by decide)
  · exact middle_swap_mem
  · exact Subgroup.mem_sup_right (show Equiv.swap (4 : Fin 8) 5 ∈ fourStabilizer from by decide)
  · exact Subgroup.mem_sup_right (show Equiv.swap (5 : Fin 8) 6 ∈ fourStabilizer from by decide)
  · exact Subgroup.mem_sup_right (show Equiv.swap (6 : Fin 8) 7 ∈ fourStabilizer from by decide)

theorem overgroups_sup : pairOvergroup ⊔ fourOvergroup = ⊤ := by
  let H := pairOvergroup ⊔ fourOvergroup
  let f : S8 →* X := MonoidHom.inr C2 S8
  have hs : pairStabilizer ⊔ fourStabilizer ≤ H.comap f := by
    apply sup_le
    · intro g hg
      exact Subgroup.mem_sup_left ⟨mem_top _, hg⟩
    · intro g hg
      exact Subgroup.mem_sup_right ⟨mem_top _, hg⟩
  rw [stabilizers_sup] at hs
  apply top_unique
  intro g _
  have hz : (g.1, (1 : S8)) ∈ H := Subgroup.mem_sup_left ⟨mem_top _, one_mem _⟩
  have hp : ((1 : C2), g.2) ∈ H := hs (mem_top _)
  simpa using H.mul_mem hz hp

theorem card_s8 : Nat.card S8 = 40320 := by
  norm_num [S8, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

theorem card_X : Nat.card X = 80640 := by
  rw [Nat.card_prod, card_s8]
  norm_num [C2, Nat.card_eq_fintype_card]

theorem card_sylow (P : Sylow 2 X) : Nat.card P = 256 := by
  rw [P.card_eq_multiplicity, card_X]
  rw [show 80640 = 2 ^ 8 * 315 from rfl,
    Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)]

/-- The actual central C₂ factor, which is normal in the whole product. -/
def centralFactor : Subgroup X := (⊤ : Subgroup C2).prod ⊥

instance : centralFactor.Normal := by
  dsimp [centralFactor]
  infer_instance

theorem centralFactor_card : Nat.card centralFactor = 2 := by
  unfold centralFactor
  rw [Nat.card_congr ((⊤ : Subgroup C2).prodEquiv (⊥ : Subgroup S8)).toEquiv,
    Nat.card_prod, Subgroup.card_top]
  norm_num [C2, Nat.card_eq_fintype_card]

theorem centralFactor_ne_bot : centralFactor ≠ ⊥ := by
  intro h
  have hh := centralFactor_card
  rw [h] at hh
  simp at hh

theorem centralFactor_le_pairOvergroup : centralFactor ≤ pairOvergroup :=
  Subgroup.prod_mono le_rfl bot_le

theorem centralFactor_le_fourOvergroup : centralFactor ≤ fourOvergroup :=
  Subgroup.prod_mono le_rfl bot_le

/-- Any subgroup containing the central factor has a nontrivial two-core. -/
theorem pCoreIn_ne_bot_of_centralFactor_le (H : Subgroup X) (hH : centralFactor ≤ H) :
    H.pCoreIn 2 ≠ ⊥ := by
  have hp : IsPGroup 2 centralFactor :=
    IsPGroup.of_card (centralFactor_card.trans (by decide : 2 = 2 ^ 1))
  have hn : H ≤ normalizer (centralFactor : Set X) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hle := Subgroup.le_pCoreIn_of_normalizes hp hH hn
  exact fun h => centralFactor_ne_bot (bot_unique (h ▸ hle))

theorem pairOvergroup_pCoreIn_ne_bot : pairOvergroup.pCoreIn 2 ≠ ⊥ :=
  pCoreIn_ne_bot_of_centralFactor_le _ centralFactor_le_pairOvergroup

theorem fourOvergroup_pCoreIn_ne_bot : fourOvergroup.pCoreIn 2 ≠ ⊥ :=
  pCoreIn_ne_bot_of_centralFactor_le _ centralFactor_le_fourOvergroup

end Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
