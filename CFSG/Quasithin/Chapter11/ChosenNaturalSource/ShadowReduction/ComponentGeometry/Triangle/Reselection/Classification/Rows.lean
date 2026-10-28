module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryActorCases
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.Models
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder

/-!
# The two field-four rows of the earlier FF classification

The orders of Sp₄(4) and G₂(4) distinguish their actual component from every
other row of B.4.2 and from the repeated alternatives of B.5.1. Monotone order
bounds leave only small field degrees; the surviving degree is two. The
conclusions retain the action equivalences supplied by the source classification.

Source: Aschbacher--Smith B.4.2, B.5.1, 3.2.8 and 11.0.2, printed pp.86,
99--103, 582 and 759--760.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine

/-- Only the orders of the two actual triangle components enter the row sieve. -/
def FieldFourOrder (n : ℕ) : Prop := n = 979200 ∨ n = 251596800

private theorem order_bound {n : ℕ} (h : FieldFourOrder n) : n ≤ 251596800 := by
  rcases h with rfl | rfl <;> decide

/-- Neither field-four component can be a binary-field rank-one group. -/
theorem no_linearTwo_order (F : BinaryField)
    (h : FieldFourOrder (Nat.card SL(2,F.Carrier))) : False := by
  have hc := order_bound h
  rw [Atlas.card_sl_two, F.card_eq] at hc
  have hb : F.degree ≤ 9 := by
    by_contra hn
    have hp : 1024 ≤ 2 ^ F.degree := by
      exact Nat.pow_le_pow_right (show 0 < 2 by decide) (show 10 ≤ F.degree by omega)
    have hh : 1024 * (1024^2-1) ≤ 2^F.degree * ((2^F.degree)^2-1) := by gcongr
    omega
  rw [FieldFourOrder, Atlas.card_sl_two, F.card_eq] at h
  have hpos := F.degree_pos
  interval_cases F.degree <;> norm_num at h

private theorem no_linearThree_order (F : BinaryField)
    (h : FieldFourOrder (Nat.card SL(3,F.Carrier))) : False := by
  have hc := order_bound h
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear, F.card_eq] at hc
  have hb : F.degree ≤ 3 := by
    by_contra hn
    have hp : 16 ≤ 2 ^ F.degree := by
      exact Nat.pow_le_pow_right (show 0 < 2 by decide) (show 4 ≤ F.degree by omega)
    have hh : 16^3 * (16^3-1) * (16^2-1) ≤
        (2^F.degree)^3 * ((2^F.degree)^3-1) * ((2^F.degree)^2-1) := by gcongr
    omega
  rw [FieldFourOrder, Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear, F.card_eq] at h
  have hpos := F.degree_pos
  interval_cases F.degree <;> norm_num at h

private theorem symplectic_degree (F : BinaryField)
    (h : FieldFourOrder (Nat.card (Matrix.symplecticGroup (Fin 2) F.Carrier))) :
    F.degree = 2 := by
  have hc := order_bound h
  rw [Theory.SpecificGroups.SymplecticFour.card_sp, F.card_eq] at hc
  have hb : F.degree ≤ 2 := by
    by_contra hn
    have hp : 8 ≤ 2 ^ F.degree := by
      exact Nat.pow_le_pow_right (show 0 < 2 by decide) (show 3 ≤ F.degree by omega)
    have hh : 8^4 * (8^2-1) * (8^4-1) ≤
        (2^F.degree)^4 * ((2^F.degree)^2-1) * ((2^F.degree)^4-1) := by gcongr
    omega
  rw [FieldFourOrder, Theory.SpecificGroups.SymplecticFour.card_sp, F.card_eq] at h
  have hpos := F.degree_pos
  interval_cases F.degree <;> norm_num at h
  rfl

private theorem g2_degree (F : BinaryField)
    (h : FieldFourOrder (Nat.card (Atlas.G2.Model F.Carrier))) : F.degree = 2 := by
  have hc := order_bound h
  rw [Atlas.G2.card_Model, F.card_eq] at hc
  have hb : F.degree ≤ 2 := by
    by_contra hn
    have hp : 8 ≤ 2 ^ F.degree := by
      exact Nat.pow_le_pow_right (show 0 < 2 by decide) (show 3 ≤ F.degree by omega)
    have hh : 8^6 * (8^6-1) * (8^2-1) ≤
        (2^F.degree)^6 * ((2^F.degree)^6-1) * ((2^F.degree)^2-1) := by gcongr
    omega
  rw [FieldFourOrder, Atlas.G2.card_Model, F.card_eq] at h
  have hpos := F.degree_pos
  interval_cases F.degree <;> norm_num at h
  rfl

private theorem binary_card (n : ℕ) :
    Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp

private theorem no_binary_order {n : ℕ} (hn : n = 4 ∨ n = 5)
    (h : FieldFourOrder (Nat.card SL(n,ZMod 2))) : False := by
  rw [FieldFourOrder, binary_card] at h
  rcases hn with rfl | rfl <;> norm_num [Fin.prod_univ_succ] at h

private theorem no_alternating_order {n : ℕ} (hn : 2 ≤ n) (hb : n ≤ 8)
    (h : FieldFourOrder (Nat.card (alternatingGroup (Fin n)))) : False := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [FieldFourOrder, nat_card_alternatingGroup] at h
  interval_cases n <;> norm_num [Nat.factorial] at h

variable {P W : Type*} [Group P] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) P W)

/-- The surviving rows retain the component's order and the original intertwiner. -/
def FieldFourAction : Prop :=
  ∃ F : BinaryField, F.degree = 2 ∧
    ((Nat.card P = 979200 ∧ Nonempty (ActionEquiv ρ (binarySymplectic F))) ∨
     (Nat.card P = 251596800 ∧ Nonempty (ActionEquiv ρ (binaryG2 F))))

theorem fieldFourAction_of_irreducibleCase {L H : Subgroup P}
    (hc : FieldFourOrder (Nat.card L))
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H) : FieldFourAction (ρ.comp L.subtype) := by
  cases h with
  | linearTwo F _ e _ _ =>
    exact (no_linearTwo_order F ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)).elim
  | linearThree F _ e _ =>
    exact (no_linearThree_order F ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)).elim
  | symplectic F _ _ e _ =>
    have hd := symplectic_degree F ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)
    refine ⟨F, hd, Or.inl ⟨?_, ⟨e⟩⟩⟩
    rw [Nat.card_congr e.groupEquiv.toEquiv, Theory.SpecificGroups.SymplecticFour.card_sp,
      F.card_eq, hd]
    norm_num
  | g2 F _ _ e _ _ =>
    have hd := g2_degree F ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)
    refine ⟨F, hd, Or.inr ⟨?_, ⟨e⟩⟩⟩
    rw [Nat.card_congr e.groupEquiv.toEquiv, Atlas.G2.card_Model, F.card_eq, hd]
    norm_num
  | symplecticTwo e _ =>
    have hb := Nat.card_le_card_of_injective
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).subtype
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).subtype_injective
    rw [← Nat.card_congr e.subgroupEquiv.toEquiv,
      Theory.SpecificGroups.SymplecticFour.Binary.card_sp_two] at hb
    rcases hc with hc | hc <;> omega
  | g2Two e _ _ =>
    have he := Nat.card_congr e.subgroupEquiv.toEquiv
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
      Atlas.G2.BinaryException.card_H] at he
    rcases hc with hc | hc <;> omega
  | symmetric n hn e _ _ =>
    exact (no_alternating_order (by rcases hn with rfl | rfl <;> decide)
      (by rcases hn with rfl | rfl <;> decide)
      ((Nat.card_congr e.subgroupEquiv.toEquiv) ▸ hc)).elim
  | alternatingSix _ e _ _ =>
    exact (no_alternating_order (by decide) (by decide)
      ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)).elim
  | alternatingSeven _ _ e _ _ _ =>
    exact (no_alternating_order (by decide) (by decide)
      ((Nat.card_congr e.toEquiv) ▸ hc)).elim
  | tripleSix _ a _ =>
    have he := Subgroup.card_eq_card_quotient_mul_card_subgroup (center L)
    rw [Nat.card_congr a.quotientEquiv.toEquiv, Nat.card_congr a.centerEquiv.toEquiv,
      nat_card_alternatingGroup] at he
    norm_num [Nat.factorial, Nat.card_congr Multiplicative.toAdd] at he
    rcases hc with hc | hc <;> omega
  | binaryLinear n hn _ e _ =>
    exact (no_binary_order hn ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)).elim
  | orthogonalSix _ _ e _ _ =>
    exact (no_alternating_order (by decide) (by decide)
      ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)).elim
  | symmetricEight _ e _ =>
    exact (no_alternating_order (by decide) (by decide)
      ((Nat.card_congr e.subgroupEquiv.toEquiv) ▸ hc)).elim
  | exteriorFive _ _ e _ _ _ =>
    exact (no_binary_order (Or.inr rfl) ((Nat.card_congr e.toEquiv) ▸ hc)).elim

/-- The field-four orders also force the source moved space itself to be Irr⁺. -/
theorem irrPlus_of_sourceCase {L : Subgroup P} {s : MovedSection ρ L}
    (hc : FieldFourOrder (Nat.card L))
    (h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s) :
    IsIrrPlus ρ L s.space.toSubmodule := by
  cases h with
  | irreducible hi _ _ _ _ => exact hi
  | doubleThree F _ e _ _ =>
    exact (no_linearThree_order F ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)).elim
  | naturalDual n hn _ hnat =>
    exact (no_binary_order hn ((Nat.card_congr hnat.some.groupEquiv.toEquiv) ▸ hc)).elim
  | repeatedNatural n _ hn _ _ _ hnat =>
    exact (no_binary_order hn ((Nat.card_congr hnat.some.groupEquiv.toEquiv) ▸ hc)).elim

/-- All repeated and mixed B.5.1 rows have incompatible actual component groups. -/
theorem fieldFourAction_of_sourceCase {L : Subgroup P} {s : MovedSection ρ L}
    (hc : FieldFourOrder (Nat.card L))
    (h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s) : FieldFourAction (s.action.comp L.subtype) := by
  cases h with
  | irreducible _ _ _ h _ => exact fieldFourAction_of_irreducibleCase _ hc h
  | doubleThree F _ e _ _ =>
    exact (no_linearThree_order F ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)).elim
  | naturalDual n hn _ hnat =>
    exact (no_binary_order hn ((Nat.card_congr hnat.some.groupEquiv.toEquiv) ▸ hc)).elim
  | repeatedNatural n _ hn _ _ _ hnat =>
    exact (no_binary_order hn ((Nat.card_congr hnat.some.groupEquiv.toEquiv) ▸ hc)).elim

/-- In the actual 3.2.5 doubled-seed list only the symplectic field-four
constituent is compatible with either triangle group. -/
theorem symplectic_of_constituent (hc : FieldFourOrder (Nat.card P))
    (h : Chapter3.Section02.ChosenSource325.ConstituentModel ρ) :
    Nat.card P = 979200 ∧ ∃ F : BinaryField, F.degree = 2 ∧
      Nonempty (ActionEquiv ρ (binarySymplectic F)) := by
  rcases h with ⟨F, ⟨e⟩⟩ | ⟨F, _, ⟨e⟩⟩ | ⟨e⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨σ, _, ⟨e⟩⟩
  · exact (no_linearThree_order F ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)).elim
  · have hd := symplectic_degree F ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)
    refine ⟨?_, F, hd, ⟨e⟩⟩
    rw [Nat.card_congr e.groupEquiv.toEquiv, Theory.SpecificGroups.SymplecticFour.card_sp,
      F.card_eq, hd]
    norm_num
  · obtain ⟨e⟩ := e
    exact (no_alternating_order (by decide) (by decide)
      ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)).elim
  · exact (no_binary_order hn ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)).elim
  · exact (no_alternating_order (by decide) (by decide)
      ((Nat.card_congr e.groupEquiv.toEquiv) ▸ hc)).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
