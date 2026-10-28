module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.ChiefFaithfulness
public import Theory.SpecificGroups.BinaryLinear.SylowCenters
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Center
public import Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.InnerAction
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Comparing the natural actors in the B.5.1 chief flag

Sylow-center orders separate even SL3 and Sp4 groups from binary SL4 and SL5.
The small derived symplectic endpoint is excluded by its order bound. These
facts compare actual groups, retaining their central kernels until the earlier
covering argument removes them. The full B.4.2 list on a binary natural actor
then leaves the same-degree natural module under the source ratio bounds.

Source: Aschbacher--Smith B.5.1, pp.100–101, after (++) and before (I).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups ENNReal IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion

private theorem binary_card (n : ℕ) :
    Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp

/-- Sylow center orders separate every even SL3 group from the binary
higher natural families, including the projective order-20160 coincidence. -/
theorem no_linearThree_binary_equiv (F : BinaryField) {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : SL(3,F.Carrier) ≃* SL(d,ZMod 2)) : False := by
  let := Fintype.ofFinite F.Carrier
  have hdz : 0 < d := by rcases hd with rfl | rfl <;> decide
  have hz : center SL(3,F.Carrier) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [Nat.card_congr (centerCongr e).toEquiv, BinaryLinear.OuterCyclic.binary_center_eq_bot hdz]
    exact Subgroup.card_bot
  let p := e.symm.trans (Matrix.SL3.equivProjectiveOfCenterEqBot F.Carrier hz)
  let S : Sylow 2 SL(d,ZMod 2) := Classical.choice inferInstance
  have hS := Matrix.PSL3.LinearThree.card_center_sylow_of_equiv F.Carrier
    F.degree_pos F.card_eq p S
  have hb := BinaryLinear.sl_sylow_center_card_le_two (by omega : 2 ≤ d) S
  have hfield : Nat.card F.Carrier = 2 := by
    rw [hS, ← F.card_eq] at hb
    exact le_antisymm hb (Nat.succ_le_iff.mpr ((by simpa only [Nat.card_eq_fintype_card] using Fintype.one_lt_card (α := F.Carrier))))
  let ef := ZMod.ringEquivOfPrime F.Carrier Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hfield)
  have h3 : Nat.card SL(3,F.Carrier) = 168 := by
    rw [← Nat.card_congr (Atlas.fieldEquivSL 3 ef).toEquiv, binary_card]
    decide
  have hc := (Nat.card_congr e.toEquiv).symm.trans h3
  rcases hd with rfl | rfl <;> rw [binary_card] at hc <;> norm_num [Fin.prod_univ_succ] at hc

/-- Every even Sp4 Sylow center has at least four elements; binary linear
Sylow centers have at most two. This separates the actual full groups. -/
theorem no_symplectic_binary_equiv (F : BinaryField) {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : Matrix.symplecticGroup (Fin 2) F.Carrier ≃* SL(d,ZMod 2)) : False := by
  let := Fintype.ofFinite F.Carrier
  let S : Sylow 2 (Matrix.symplecticGroup (Fin 2) F.Carrier) := Classical.choice inferInstance
  have hc := Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.card_sylow_center
    F.card_eq F.degree_pos S
  have ht := BinaryLinear.sylow_center_card_congr e S
  have hb := BinaryLinear.sl_sylow_center_card_le_two (by rcases hd with rfl | rfl <;> decide)
    (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  rw [← ht, hc] at hb
  have htwo : 2 ≤ Nat.card F.Carrier := Nat.succ_le_iff.mpr (by simpa only [Nat.card_eq_fintype_card] using Fintype.one_lt_card (α := F.Carrier))
  nlinarith

/-- The binary derived symplectic endpoint has order at most 720. -/
theorem no_symplecticTwo_binary_equiv {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) ≃* SL(d,ZMod 2)) : False := by
  have hb := Nat.card_le_card_of_injective
    (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).subtype
    (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).subtype_injective
  rw [Nat.card_congr e.toEquiv, Theory.SpecificGroups.SymplecticFour.Binary.card_sp_two] at hb
  rcases hd with rfl | rfl <;> rw [binary_card] at hb <;> norm_num [Fin.prod_univ_succ] at hb

theorem binary_degree_eq {d n : ℕ} (hd : d = 4 ∨ d = 5) (hn : n = 4 ∨ n = 5)
    (e : SL(d,ZMod 2) ≃* SL(n,ZMod 2)) : d = n := by
  have hc := Nat.card_congr e.toEquiv
  rcases hd with rfl | rfl <;> rcases hn with rfl | rfl
  · rfl
  · rw [binary_card, binary_card] at hc
    norm_num [Fin.prod_univ_succ] at hc
  · rw [binary_card, binary_card] at hc
    norm_num [Fin.prod_univ_succ] at hc
  · rfl

/-- On a binary natural actor the ratio bound excludes every different row
of the full earlier catalogue. The exceptional S8 row is retained until its
ratio or its actual alternating subgroup order excludes it. -/
theorem binary_natural_of_ratio {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) {L H : Subgroup G}
    (h : SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : L ≃* SL(d,ZMod 2))
    (hq : quadraticRatio ρ < 1) (hfour : d = 4 → quadraticRatio ρ < 3 / 4) :
    IsLinearNatural (ρ.comp L.subtype) BinaryField.two d := by
  cases h with
  | linearThree F _ e _ =>
    exact (no_linearThree_binary_equiv F hd (e.groupEquiv.symm.trans mark)).elim
  | binaryLinear n hn _ e _ =>
    have heq := binary_degree_eq hn hd (e.groupEquiv.symm.trans mark)
    subst n
    exact ⟨e⟩
  | symplectic F _ _ e _ =>
    exact (no_symplectic_binary_equiv F hd (e.groupEquiv.symm.trans mark)).elim
  | symplecticTwo e _ =>
    exact (no_symplecticTwo_binary_equiv hd (e.subgroupEquiv.symm.trans mark)).elim
  | symmetricEight _ e hr =>
    rcases hd with rfl | rfl
    · have hh := hfour rfl
      rw [hr] at hh
      exact (lt_irrefl _ hh).elim
    · have hc := Nat.card_congr (e.subgroupEquiv.symm.trans mark).toEquiv
      rw [nat_card_alternatingGroup, binary_card] at hc
      norm_num [Fin.prod_univ_succ, Nat.factorial] at hc
  | linearTwo _ _ _ _ hr => rw [hr] at hq; exact (lt_irrefl _ hq).elim
  | g2 _ _ _ _ _ hr => rw [hr] at hq; exact (lt_irrefl _ hq).elim
  | g2Two _ _ hr => rw [hr] at hq; exact (lt_irrefl _ hq).elim
  | symmetric _ _ _ _ hr => rw [hr] at hq; exact (lt_irrefl _ hq).elim
  | alternatingSix _ _ _ hr => rw [hr] at hq; exact (lt_irrefl _ hq).elim
  | alternatingSeven _ _ _ _ _ hr => rw [hr] at hq; exact (lt_irrefl _ hq).elim
  | tripleSix _ _ hr => rw [hr] at hq; exact (lt_irrefl _ hq).elim
  | orthogonalSix _ _ _ _ hr => rw [hr] at hq; exact (lt_irrefl _ hq).elim
  | exteriorFive _ _ _ _ _ hr => rw [hr] at hq; exact (lt_irrefl _ hq).elim

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
