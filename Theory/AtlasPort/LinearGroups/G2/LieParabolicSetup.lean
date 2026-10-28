module

public import Theory.AtlasPort.LinearGroups.G2.Parabolic
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Mathlib.GroupTheory.Sylow
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.CharP.Two
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The standard root pair in the full split G₂ model

The short and long simple Weyl generators extend the six positive root groups
to two rank-one local subgroups. Adding the split torus gives the two standard
parabolic candidates. They generate the full octonion automorphism group.
The two five-root subgroups have order q⁵, by deleting one coordinate in the
unique unipotent normal form. The order formula shows that the six-root subgroup is Sylow in characteristic
two, including the full group G₂(2).

The numbering places the five-root special radical on the first side; its
identification with the two-core and the centralization convention remain
separate local-structure calculations. No quotient or core identification is
assumed here.

Source: Aschbacher--Smith, F.1.12(I)(3), printed pp. 262--264;
root coordinates and the group order are from the licensed ATLAS port.
-/

@[expose] public section

namespace Atlas.G2.LieParabolicSetup

variable {F : Type*} [Field F]

private theorem join_rearrange {α : Type*} [SemilatticeSup α] (a b c : α) :
    (a ⊔ b) ⊔ (a ⊔ c) = (a ⊔ c) ⊔ b := by
  rw [sup_sup_sup_comm, sup_idem, sup_comm b c, ← sup_assoc]

/-- Rank-one local subgroup on the short-Weyl side, before adding the full torus. -/
def local₁ : Subgroup (Model F) := unipotent ⊔ Subgroup.closure {weylS}

/-- Rank-one local subgroup on the long-Weyl side, before adding the full torus. -/
def local₂ : Subgroup (Model F) := unipotent ⊔ Subgroup.closure {weylR}

/-- The short-Weyl standard parabolic. -/
def parabolic₁ : Subgroup (Model F) := borel ⊔ Subgroup.closure {weylS}

/-- The long-Weyl standard parabolic, already identified as a point stabilizer. -/
abbrev parabolic₂ : Subgroup (Model F) := parabolic

theorem local₁_sup_borel : local₁ (F := F) ⊔ borel = parabolic₁ := by
  exact join_rearrange _ _ _

theorem local₂_sup_borel : local₂ (F := F) ⊔ borel = parabolic₂ := by
  exact join_rearrange _ _ _

theorem unipotent_le_local₁ : unipotent (K := F) ≤ local₁ := le_sup_left

theorem unipotent_le_local₂ : unipotent (K := F) ≤ local₂ := le_sup_left

theorem borel_le_parabolic₁ : borel (K := F) ≤ parabolic₁ := le_sup_left

theorem borel_le_parabolic₂ : borel (K := F) ≤ parabolic₂ := le_sup_left

theorem parabolics_generate : parabolic₁ (F := F) ⊔ parabolic₂ = ⊤ := by
  apply top_unique
  rw [← generated_eq_top]
  apply sup_le
  · apply (Subgroup.closure_le _).mpr
    rintro g (hg | hg)
    · exact Subgroup.mem_sup_left (borel_le_parabolic₁ (Subgroup.mem_sup_left hg))
    · rcases hg with (rfl | rfl)
      · exact Subgroup.mem_sup_right weylR_mem_parabolic
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  · exact le_trans (show splitTorus ≤ borel (K := F) from le_sup_right)
      (le_trans borel_le_parabolic₁ le_sup_left)

/-- The unipotent index computed in the full group, not its derived subgroup. -/
theorem unipotent_index [Finite F] :
    (unipotent (K := F)).index = (Nat.card F ^ 6 - 1) * (Nat.card F ^ 2 - 1) := by
  have h := (unipotent (K := F)).card_mul_index
  rw [card_unipotent, card_Model, mul_assoc] at h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos Nat.card_pos 6) h

/-- Finite fields of characteristic two have positive power-of-two order. -/
theorem field_card [Finite F] [CharP F 2] :
    ∃ n : ℕ, 0 < n ∧ Nat.card F = 2 ^ n := by
  let := Fintype.ofFinite F
  obtain ⟨n, _, hn⟩ := FiniteField.card F 2
  exact ⟨n, n.property, by simpa only [Nat.card_eq_fintype_card] using hn⟩

theorem unipotent_isTwoGroup [Finite F] [CharP F 2] :
    IsPGroup 2 (unipotent (K := F)) := by
  obtain ⟨n, _, hn⟩ := field_card (F := F)
  apply IsPGroup.of_card (n := n * 6)
  rw [card_unipotent, hn, pow_mul]

theorem unipotent_index_odd [Finite F] [CharP F 2] :
    Odd (unipotent (K := F)).index := by
  rw [unipotent_index]
  obtain ⟨n, hn, hcard⟩ := field_card (F := F)
  have heven : Even (Nat.card F) := by
    rw [hcard]
    exact even_two.pow_of_ne_zero (Nat.ne_of_gt hn)
  have hpos : 0 < Nat.card F := Nat.card_pos
  exact (Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 6 (Nat.ne_of_gt hpos))) (heven.pow_of_ne_zero (by decide : 6 ≠ 0)) odd_one).mul
    (Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Nat.ne_of_gt hpos))) (heven.pow_of_ne_zero (by decide : 2 ≠ 0)) odd_one)

/-- The standard Sylow marking, with exactly the six-root subgroup as carrier. -/
def sylow [Finite F] [CharP F 2] : Sylow 2 (Model F) :=
  unipotent_isTwoGroup.toSylow unipotent_index_odd.not_two_dvd_nat

@[simp] theorem sylow_coe [Finite F] [CharP F 2] :
    (sylow (F := F) : Subgroup (Model F)) = unipotent := rfl

theorem sylow_le_borel [Finite F] [CharP F 2] :
    (sylow (F := F) : Subgroup (Model F)) ≤ borel := le_sup_left

end Atlas.G2.LieParabolicSetup

namespace Atlas.G2.LieParabolicSetup


variable {F : Type*} [Field F]

/-- Omitting either simple positive root leaves a five-root subgroup. -/
def fiveRootSubgroup (i : Fin 6) (hi : i = 4 ∨ i = 5) : Subgroup (Model F) where
  carrier := {g | ∃ t : Fin 6 → F, t i = 0 ∧ unipotentProduct t = g}
  one_mem' := ⟨0, rfl, unipotentProduct_zero⟩
  mul_mem' := by
    rintro g h ⟨t, ht, rfl⟩ ⟨u, hu, rfl⟩
    refine ⟨unipotentProductParameters t u, ?_, (unipotentProduct_mul t u).symm⟩
    rcases hi with rfl | rfl <;> simp [unipotentProductParameters, ht, hu]
  inv_mem' := by
    rintro g ⟨t, ht, rfl⟩
    refine ⟨unipotentInverseParameters t, ?_, (unipotentProduct_inv t).symm⟩
    rcases hi with rfl | rfl <;> simp [unipotentInverseParameters, ht]

theorem fiveRootSubgroup_le_unipotent (i : Fin 6) (hi : i = 4 ∨ i = 5) :
    fiveRootSubgroup (F := F) i hi ≤ unipotent := by
  rintro g ⟨t, _, rfl⟩
  exact unipotentProduct_mem t

/-- Unique five-root coordinates; this equivalence makes no claim about a product group law. -/
noncomputable def fiveRootEquiv (i : Fin 6) (hi : i = 4 ∨ i = 5) :
    ({j : Fin 6 // j ≠ i} → F) ≃ fiveRootSubgroup (F := F) i hi where
  toFun t := ⟨unipotentProduct (fun j => if h : j = i then 0 else t ⟨j, h⟩),
    ⟨_, by simp, rfl⟩⟩
  invFun g j := unipotentParameters g.val j.val
  left_inv t := by
    funext j
    simp [unipotentParameters_product, j.property]
  right_inv g := by
    obtain ⟨g, t, ht, rfl⟩ := g
    apply Subtype.ext
    change unipotentProduct (fun j => if h : j = i then 0
      else unipotentParameters (unipotentProduct t) j) = unipotentProduct t
    apply congrArg unipotentProduct
    funext j
    simp only [unipotentParameters_product]
    by_cases h : j = i
    · subst j
      simpa using ht.symm
    · simp [h]

theorem card_fiveRootSubgroup [Finite F] (i : Fin 6) (hi : i = 4 ∨ i = 5) :
    Nat.card (fiveRootSubgroup (F := F) i hi) = Nat.card F ^ 5 := by
  rw [← Nat.card_congr (fiveRootEquiv (F := F) i hi), Nat.card_fun]
  have hc : Nat.card {j : Fin 6 // j ≠ i} = 5 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp
  rw [hc]

/-- The five-root candidate for the short-Weyl parabolic radical. -/
def radical₁ : Subgroup (Model F) := fiveRootSubgroup 5 (Or.inr rfl)

/-- The five-root candidate for the long-Weyl parabolic radical. -/
def radical₂ : Subgroup (Model F) := fiveRootSubgroup 4 (Or.inl rfl)

theorem card_radical₁ [Finite F] : Nat.card (radical₁ (F := F)) = Nat.card F ^ 5 :=
  card_fiveRootSubgroup _ _

theorem card_radical₂ [Finite F] : Nat.card (radical₂ (F := F)) = Nat.card F ^ 5 :=
  card_fiveRootSubgroup _ _

end Atlas.G2.LieParabolicSetup

namespace Atlas.G2.LieParabolicSetup
open Explicit
variable {F : Type*} [Field F]

/-- Every positive root product commutes with the highest-root group. -/
theorem unipotentProduct_commute_rootA (t : Fin 6 → F) (a : F) :
    Commute (unipotentProduct t) (rootA a) := by
  have ha : rootA a = unipotentProduct ![a,0,0,0,0,0] := by simp [unipotentProduct]
  change unipotentProduct t * rootA a = rootA a * unipotentProduct t
  rw [ha, unipotentProduct_mul, unipotentProduct_mul]
  congr 1
  funext i
  fin_cases i <;> simp [unipotentProductParameters, add_comm]

/-- The short simple reflection fixes the highest root pointwise. -/
theorem weylS_commute_rootA [CharP F 2] (a : F) : Commute weylS (rootA a) := by
  change weylS * rootA a = rootA a * weylS
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;> simp [weylS, weylSEquiv, weylSLinear, weylSApply,
    rootA, rootAEquiv, rootALinear, rootAApply, CharTwo.neg_eq, CharTwo.sub_eq_add]

end Atlas.G2.LieParabolicSetup

namespace Atlas.G2.LieParabolicSetup
open Explicit
variable {F : Type*} [Field F]

/-- The first local group fixes every element of the highest-root group. -/
theorem local₁_le_centralizer_rootA [CharP F 2] (a : F) :
    local₁ (F := F) ≤ Subgroup.centralizer {rootA a} := by
  apply sup_le
  · intro g hg
    rw [unipotent_eq_range] at hg
    obtain ⟨t, rfl⟩ := hg
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (unipotentProduct_commute_rootA t a).eq
  · apply (Subgroup.closure_le _).mpr
    rintro g (rfl : g = weylS)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (weylS_commute_rootA a).eq

theorem radical₁_le_local₁ : radical₁ (F := F) ≤ local₁ :=
  (fiveRootSubgroup_le_unipotent _ _).trans unipotent_le_local₁

theorem radical₂_le_local₂ : radical₂ (F := F) ≤ local₂ :=
  (fiveRootSubgroup_le_unipotent _ _).trans unipotent_le_local₂

/-- The full Borel equals the unipotent subgroup only at the binary parameter. -/
theorem borel_eq_unipotent_of_card_two [Finite F] (hq : Nat.card F = 2) :
    borel (K := F) = unipotent := by
  apply (Subgroup.eq_of_le_of_card_ge (show unipotent (K := F) ≤ borel from le_sup_left) ?_).symm
  rw [card_borel, card_unipotent, hq]
  norm_num

end Atlas.G2.LieParabolicSetup
