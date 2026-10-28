module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.CaseComparison
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
/-!
# B.5.1 actions on the binary degree-four and degree-five components

The literal component marking rules out the other group families in the full
B.4.2 list. The remaining action alternatives retain the moved section,
coordinates, marked offenders and extension data. In particular the exterior
row asserts exactly the available dimension and offender data, without adding
an unproved exterior-square coordinate recognition.

Source: Aschbacher--Smith B.4.2, B.5.1 and 15.1.27, pp.86,99,1102--1103.
-/
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups ENNReal IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
namespace BinaryActor
private theorem binary_card (n : ℕ) :
    Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp

private theorem no_linearTwo {n : ℕ} (hn : n = 4 ∨ n = 5)
    (F : BinaryField) (e : SL(2,F.Carrier) ≃* SL(n,ZMod 2)) : False := by
  have hc := Nat.card_congr e.toEquiv
  rw [Atlas.card_sl_two, binary_card] at hc
  let q := Nat.card F.Carrier
  rcases hn with rfl | rfl
  · have hh : q * (q^2-1) = 20160 := by simpa [Fin.prod_univ_succ] using hc
    by_cases hq : q ≤ 27
    · have hb : q * (q^2-1) ≤ 27 * (27^2-1) := by gcongr
      omega
    · have hb : 28 * (28^2-1) ≤ q * (q^2-1) := by gcongr <;> omega
      omega
  · have hh : q * (q^2-1) = 9999360 := by simpa [Fin.prod_univ_succ] using hc
    by_cases hq : q ≤ 215
    · have hb : q * (q^2-1) ≤ 215 * (215^2-1) := by gcongr
      omega
    · have hb : 216 * (216^2-1) ≤ q * (q^2-1) := by gcongr <;> omega
      omega

private theorem no_g2 {n : ℕ} (hn : n = 4 ∨ n = 5)
    (F : BinaryField) (e : Atlas.G2.Model F.Carrier ≃* SL(n,ZMod 2)) : False := by
  have hc := Nat.card_congr e.toEquiv
  rw [Atlas.G2.card_Model, binary_card] at hc
  let q := Nat.card F.Carrier
  rcases hn with rfl | rfl
  · have hh : q^6 * (q^6-1) * (q^2-1) = 20160 := by
      simpa [Fin.prod_univ_succ] using hc
    by_cases hq : q ≤ 2
    · have hb : q^6 * (q^6-1) * (q^2-1) ≤ 2^6 * (2^6-1) * (2^2-1) := by gcongr
      omega
    · have hb : 3^6 * (3^6-1) * (3^2-1) ≤ q^6 * (q^6-1) * (q^2-1) := by
        gcongr <;> omega
      omega
  · have hh : q^6 * (q^6-1) * (q^2-1) = 9999360 := by
      simpa [Fin.prod_univ_succ] using hc
    by_cases hq : q ≤ 3
    · have hb : q^6 * (q^6-1) * (q^2-1) ≤ 3^6 * (3^6-1) * (3^2-1) := by gcongr
      omega
    · have hb : 4^6 * (4^6-1) * (4^2-1) ≤ q^6 * (q^6-1) * (q^2-1) := by
        gcongr <;> omega
      omega

private theorem no_g2Two {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : commutator (Atlas.G2.Model (ZMod 2)) ≃* SL(n,ZMod 2)) : False := by
  have hc := Nat.card_congr e.toEquiv
  rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
    Atlas.G2.BinaryException.card_H, binary_card] at hc
  rcases hn with rfl | rfl <;> norm_num [Fin.prod_univ_succ] at hc

private theorem no_small_alternating {n m : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : m = 5 ∨ m = 6 ∨ m = 7)
    (e : alternatingGroup (Fin m) ≃* SL(n,ZMod 2)) : False := by
  let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by rcases hm with rfl | rfl | rfl <;> decide)
  have hc := Nat.card_congr e.toEquiv
  rw [nat_card_alternatingGroup, binary_card] at hc
  rcases hn with rfl | rfl <;> rcases hm with rfl | rfl | rfl <;>
    norm_num [Fin.prod_univ_succ, Nat.factorial] at hc

private theorem alternatingEight_degree {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : alternatingGroup (Fin 8) ≃* SL(n,ZMod 2)) : n = 4 := by
  rcases hn with rfl | rfl
  · rfl
  · have hc := Nat.card_congr e.toEquiv
    rw [nat_card_alternatingGroup, binary_card] at hc
    norm_num [Fin.prod_univ_succ, Nat.factorial] at hc

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

/-- The exact surviving irreducible source rows on SL4(2) or SL5(2). -/
inductive IrreducibleCase (L H : Subgroup D) (n : ℕ) : Prop
  | natural (generated : H = L)
      (action : ActionEquiv (ρ.comp L.subtype) (linearNatural BinaryField.two n))
      (ratio : quadraticRatio ρ = 1 / (n - 1 : ℕ))
  | orthogonal (degree : n = 4) (generated : H = L) (whole : L = ⊤)
      (action : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 8))
      (offenders : ∀ A, IsBestOffender ρ A → rank A = 3)
      (ratio : quadraticRatio ρ = 1)
  | symmetricEight (degree : n = 4) (whole : H = ⊤)
      (action : MarkedActionEquiv ρ H L (BinaryPermutation.naturalRepresentation (Fin 8))
        (alternatingGroup (Fin 8)))
      (ratio : quadraticRatio ρ = 3 / 4)
  | exterior (degree : n = 5) (generated : H = L) (whole : L = ⊤)
      (equiv : L ≃* SL(5,ZMod 2)) (dimension : Module.finrank (ZMod 2) V = 10)
      (offenders : ∀ A, IsBestOffender ρ A →
        IsEndNodeRadical ((A.subgroupOf L).map equiv.toMonoidHom))
      (ratio : quadraticRatio ρ = 1)

theorem irreducibleCase {L H : Subgroup D} {n : ℕ} (hn : n = 4 ∨ n = 5)
    (mark : L ≃* SL(n,ZMod 2))
    (h : SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H) :
    IrreducibleCase ρ L H n := by
  cases h with
  | linearTwo F _ e _ _ => exact (no_linearTwo hn F (e.groupEquiv.symm.trans mark)).elim
  | linearThree F _ e _ => exact (no_linearThree_binary_equiv F hn (e.groupEquiv.symm.trans mark)).elim
  | symplectic F _ _ e _ => exact (no_symplectic_binary_equiv F hn (e.groupEquiv.symm.trans mark)).elim
  | symplecticTwo e _ => exact (no_symplecticTwo_binary_equiv hn (e.subgroupEquiv.symm.trans mark)).elim
  | g2 F _ _ e _ _ => exact (no_g2 hn F (e.groupEquiv.symm.trans mark)).elim
  | g2Two e _ _ => exact (no_g2Two hn (e.subgroupEquiv.symm.trans mark)).elim
  | symmetric m hm e _ _ =>
    exact (no_small_alternating hn (hm.imp_right Or.inr) (e.subgroupEquiv.symm.trans mark)).elim
  | alternatingSix _ e _ _ =>
    exact (no_small_alternating hn (Or.inr (Or.inl rfl)) (e.groupEquiv.symm.trans mark)).elim
  | alternatingSeven _ _ e _ _ _ =>
    exact (no_small_alternating hn (Or.inr (Or.inr rfl)) (e.symm.trans mark)).elim
  | tripleSix _ a _ =>
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (center L)
    rw [Nat.card_congr mark.toEquiv, binary_card, Nat.card_congr a.quotientEquiv.toEquiv,
      Nat.card_congr a.centerEquiv.toEquiv, nat_card_alternatingGroup] at hc
    rcases hn with rfl | rfl <;>
      norm_num [Fin.prod_univ_succ, Nat.factorial, Nat.card_congr Multiplicative.toAdd] at hc
  | binaryLinear m hm hg e hr =>
    have he := binary_degree_eq hm hn (e.groupEquiv.symm.trans mark)
    subst m
    exact .natural hg e hr
  | orthogonalSix hg hw e ho hr =>
    exact .orthogonal (alternatingEight_degree hn (e.groupEquiv.symm.trans mark)) hg hw e ho hr
  | symmetricEight hw e hr =>
    exact .symmetricEight (alternatingEight_degree hn (e.subgroupEquiv.symm.trans mark)) hw e hr
  | exteriorFive hg hw e hd ho hr =>
    exact .exterior (binary_degree_eq hn (Or.inr rfl) (mark.symm.trans e)) hg hw e hd ho hr

/-- The full B.5.1 alternatives, specialized to the marked binary actor. -/
inductive ActionCase (L : Subgroup D) (s : MovedSection ρ L) (n : ℕ) : Prop
  | irreducible (irrPlus : IsIrrPlus ρ L s.space.toSubmodule)
      (faithful : Function.Injective s.action)
      (irreducible : IsIrreducible (s.action.comp L.subtype))
      (source : IrreducibleCase s.action L (offenderSubgroup s.action) n)
      (extension : L = ⊤ ∨ (∀ T : Sylow 2 D, L ⊔ (T : Subgroup D) = ⊤) ∧
        OuterNaturalAction s.action)
  | naturalDual (whole : L = ⊤)
      (natural : IsNaturalPlusDual (s.space.toRepresentation.comp L.subtype) n)
  | repeatedNatural (r : ℕ) (positive : 0 < r) (bound : r ≤ n - 1) (whole : L = ⊤)
      (natural : IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype)
        BinaryField.two n r)

theorem actionCase {L : Subgroup D} {s : MovedSection ρ L} {n : ℕ}
    (hn : n = 4 ∨ n = 5) (mark : L ≃* SL(n,ZMod 2))
    (h : SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s) :
    ActionCase ρ L s n := by
  cases h with
  | irreducible hi hf hir hs he => exact .irreducible hi hf hir (irreducibleCase _ hn mark hs) he
  | doubleThree F _ e _ _ => exact (no_linearThree_binary_equiv F hn (e.groupEquiv.symm.trans mark)).elim
  | naturalDual m hm hw hnat =>
    have he := binary_degree_eq hm hn (hnat.some.groupEquiv.symm.trans mark)
    subst m
    exact .naturalDual hw hnat
  | repeatedNatural m r hm hp hb hw hnat =>
    have he := binary_degree_eq hm hn (hnat.some.groupEquiv.symm.trans mark)
    subst m
    exact .repeatedNatural r hp hb hw hnat

end BinaryActor
end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
