module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeActor
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# The two irreducible B.5 actions on an A₇ component

Compare every actor in the full B.5 table with the literal A₇ component.
Orders and the defining unipotent subgroups exclude the other families.
The surviving symmetric-seven row supplies its marked restricted natural
representation; the exceptional row retains its four-dimensional section.
The rank-one block consumer excludes the latter using its actual full module.
Source: Aschbacher–Smith B.4.2, B.5.1, pp.86,99–103, and C.4.1, pp.151–153.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion.AlternatingSevenActor
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine

private theorem binary_card (n : ℕ) :
    Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv,
    Matrix.card_GL_field]
  simp

private theorem two_power_bound {k : ℕ} (h : 2 ^ k ∣ 2520) : k ≤ 3 := by
  by_contra hk
  have hd : 16 ∣ 2520 := (pow_dvd_pow 2 (by omega : 4 ≤ k)).trans h
  norm_num at hd

private theorem no_linearTwo {E : Type*} [Group E] (hE : Nat.card E = 2520)
    (F : BinaryField) (e : E ≃* SL(2,F.Carrier)) : False := by
  have hc : Nat.card SL(2,F.Carrier) = 2520 := (Nat.card_congr e.toEquiv).symm.trans hE
  rw [Atlas.card_sl_two,F.card_eq] at hc
  have hd : F.degree ≤ 3 := two_power_bound (hc ▸ dvd_mul_right (2 ^ F.degree) _)
  have hp := F.degree_pos
  interval_cases he : F.degree <;> norm_num [he] at hc

private noncomputable def fieldTwoEquiv (F : BinaryField) (h : F.degree = 1) :
    F.Carrier ≃+* ZMod 2 := by
  let : Fintype F.Carrier := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, F.card_eq,h]
    simp)

private theorem no_linearThree {E : Type*} [Group E] (hE : Nat.card E = 2520)
    (F : BinaryField) (e : E ≃* SL(3,F.Carrier)) : False := by
  have hc : Nat.card SL(3,F.Carrier) = 2520 := (Nat.card_congr e.toEquiv).symm.trans hE
  have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotentSL,F.card_eq,← pow_mul,hc] at hd
  have hb := two_power_bound hd
  have he : F.degree = 1 := by have := F.degree_pos; omega
  have hh := Nat.card_congr (Atlas.fieldEquivSL 3 (fieldTwoEquiv F he)).toEquiv
  rw [hc,binary_card] at hh
  norm_num [Fin.prod_univ_succ] at hh

private theorem no_symplectic {E : Type*} [Group E] (hE : Nat.card E = 2520)
    (F : BinaryField) (e : E ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm.trans hE
  have hd := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F.Carrier)).card_subgroup_dvd_card
  rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,F.card_eq,← pow_mul,hc] at hd
  have hb := two_power_bound hd
  have := F.degree_pos
  omega

private theorem no_g2 {E : Type*} [Group E] (hE : Nat.card E = 2520)
    (F : BinaryField) (e : E ≃* Atlas.G2.Model F.Carrier) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm.trans hE
  have hd := (Atlas.G2.unipotent (K := F.Carrier)).card_subgroup_dvd_card
  rw [Atlas.G2.card_unipotent,F.card_eq,← pow_mul,hc] at hd
  have hb := two_power_bound hd
  have := F.degree_pos
  omega

private theorem no_binaryLinear {E : Type*} [Group E] (hE : Nat.card E = 2520)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (e : E ≃* SL(d,ZMod 2)) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm.trans hE
  rcases hd with rfl | rfl <;> rw [binary_card] at hc <;>
    norm_num [Fin.prod_univ_succ] at hc

private theorem no_other_alternating {E : Type*} [Group E] (hE : Nat.card E = 2520)
    {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8) (e : E ≃* alternatingGroup (Fin n)) : False := by
  have hc := (Nat.card_congr e.toEquiv).symm.trans hE
  rcases hn with rfl | rfl | rfl <;>
    rw [nat_card_alternatingGroup] at hc <;> norm_num [Nat.factorial] at hc

universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {C J : Subgroup D}

/-- The original action is natural, or its actual section has dimension four. -/
theorem natural_or_four
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ C J)
    (e : C ≃* alternatingGroup (Fin 7)) :
    IsAlternatingNatural (ρ.comp C.subtype) 7 ∨ Module.finrank (ZMod 2) V = 4 := by
  have hc : Nat.card C = 2520 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  cases h with
  | linearTwo F _ a _ _ => exact (no_linearTwo hc F a.groupEquiv).elim
  | linearThree F _ a _ => exact (no_linearThree hc F a.groupEquiv).elim
  | symplectic F _ _ a _ => exact (no_symplectic hc F a.groupEquiv).elim
  | symplecticTwo a _ =>
    have hb := Nat.card_le_card_of_injective
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).subtype
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).subtype_injective
    rw [Theory.SpecificGroups.SymplecticFour.Binary.card_sp_two,
      ← Nat.card_congr a.subgroupEquiv.toEquiv,hc] at hb
    omega
  | g2 F _ _ a _ _ => exact (no_g2 hc F a.groupEquiv).elim
  | g2Two a _ _ =>
    have hh := (Nat.card_congr a.subgroupEquiv.toEquiv).symm.trans hc
    rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hh
    norm_num at hh
  | symmetric n hn a _ _ =>
    rcases hn with rfl | rfl
    · exact (no_other_alternating hc (Or.inl rfl) a.subgroupEquiv).elim
    · left
      refine ⟨⟨a.subgroupEquiv,a.action.linearEquiv,?_⟩⟩
      intro g v
      have he := a.action.intertwines ⟨g,a.contained g.property⟩ v
      rw [a.compatible] at he
      exact he
  | alternatingSix _ a _ _ => exact (no_other_alternating hc (Or.inr (Or.inl rfl)) a.groupEquiv).elim
  | alternatingSeven _ _ _ hd _ _ => exact Or.inr hd
  | tripleSix _ a _ =>
    have hz : Nat.card (center C) = 1 := by
      rw [Nat.card_congr (centerCongr e).toEquiv,
        alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 7)),card_bot]
    have hh := Nat.card_congr a.centerEquiv.toEquiv
    rw [hz] at hh
    norm_num at hh
  | binaryLinear d hd _ a _ => exact (no_binaryLinear hc hd a.groupEquiv).elim
  | orthogonalSix _ _ a _ _ => exact (no_other_alternating hc (Or.inr (Or.inr rfl)) a.groupEquiv).elim
  | symmetricEight _ a _ => exact (no_other_alternating hc (Or.inr (Or.inr rfl)) a.subgroupEquiv).elim
  | exteriorFive _ _ a _ _ _ => exact (no_binaryLinear hc (Or.inr rfl) a).elim

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion.AlternatingSevenActor
