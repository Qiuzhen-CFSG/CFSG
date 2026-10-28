module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFSocle
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.SpecificGroups.BinaryLinear.SylowCenters
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Theory.Representation.BinaryOffender.AmbientSectionTransport
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryOffender.NoncentralMoved
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.Representation.NormalElementaryEmbedding
public import Theory.GroupTheory.ReducedNormal.QuasisimpleImage
public import Theory.GroupTheory.ReducedNormal.MovedCentralizer
public import CFSG.Quasithin.KnownSimpleSectionTransport
/-!
# The moved layer of an FF module with alternating-five socle

The faithful self-centralizing simple component has order 60. The complete
B.5.1 classification forces its moved space into Irr⁺: the three reducible
alternatives have actors SL₃(F), SL₄(2), or SL₅(2), whose orders differ from
60. For a reduced module with A₅ residual, the original action quotient
has that simple self-centralizing socle. This supplies the FF application
without assuming its kernel or centralizer.

Source: Aschbacher–Smith B.5.1 and its application in 12.3.12,
printed pp.99–103,811.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
private theorem linear_three_card_ne_60 (F : BinaryField) :
    Nat.card SL(3,F.Carrier) ≠ 60 := by
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
  have hq : 2 ≤ Nat.card F.Carrier := Finite.one_lt_card
  by_cases he : Nat.card F.Carrier = 2
  · simp [he]
  · have hq3 : 3 ≤ Nat.card F.Carrier := by omega
    have hb : 5616 ≤ Nat.card F.Carrier ^ 3 * (Nat.card F.Carrier ^ 3 - 1) *
        (Nat.card F.Carrier ^ 2 - 1) := by
      calc
        5616 = 3^3 * (3^3-1) * (3^2-1) := by norm_num
        _ ≤ _ := by gcongr
    omega
private theorem binary_card (n : ℕ) :
    Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp
private theorem binary_higher_card_ne_60 {d : ℕ} (hd : d = 4 ∨ d = 5) :
    Nat.card SL(d,ZMod 2) ≠ 60 := by
  rcases hd with rfl | rfl <;> rw [binary_card] <;> norm_num [Fin.prod_univ_succ]

variable {G : Type*} [Group G] [Finite G]
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
/-- The complete FF classification has only the Irr⁺ branch at order 60. -/
theorem ff_card60_moved_irrPlus
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    [L.Normal] [IsSimpleGroup L] [IsQuasisimple L]
    (hcard : Nat.card L = 60) (hC : centralizer (L : Set G) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple L)
    (hf : Function.Injective ρ) (hff : IsFFModule ρ) :
    IsIrrPlus ρ L (subspaceCommutator ρ ⊤ L) := by
  obtain ⟨hLJ,⟨c⟩⟩ := ff_socle_source_conclusion ρ L hC hsq hf hff
  have hc : Nat.card (L.subgroupOf (offenderSubgroup ρ)) = 60 :=
    (Nat.card_congr (subgroupOfEquivOfLe hLJ).toEquiv).trans hcard
  cases c.clause_one with
  | irreducible hi _ _ _ _ =>
    rw [c.sectionData.space_eq] at hi
    change IsIrrPlus _ _ (subspaceCommutator (ρ.comp (offenderSubgroup ρ).subtype) ⊤ (L.subgroupOf (offenderSubgroup ρ))) at hi
    rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le hLJ] at hi
    exact (IsIrrPlus.subgroupOf_iff ρ L (offenderSubgroup ρ) hLJ _).mp hi
  | doubleThree F _ e _ _ =>
    exact (linear_three_card_ne_60 F ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
  | naturalDual d hd _ hn =>
    obtain ⟨e⟩ := hn
    exact (binary_higher_card_ne_60 hd ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨e⟩ := hn
    exact (binary_higher_card_ne_60 hd ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc)).elim
end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion

namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
variable {M Q : Type*} [Group M] [Finite M] [Group Q] [Finite Q]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]

private theorem center_bot_of_five {A : Type*} [Group A]
    (e : A ≃* alternatingGroup (Fin 5)) : center A = ⊥ := by
  apply bot_unique
  intro x hx
  apply mem_bot.mpr
  apply e.injective
  rw [map_one]
  apply mem_bot.mp
  rw [← alternatingGroup.center_eq_bot (by simp)]
  apply mem_center_iff.mpr
  intro y
  obtain ⟨z,rfl⟩ := e.surjective y
  simpa only [map_mul] using congrArg e ((mem_center_iff.mp hx) z)

/-- A reduced module with alternating-five residual gives an Irr⁺ moved space
for every faithful FF realization of its actual action quotient. -/
theorem ff_reduced_five_residual_moved_irrPlus
    (U : Subgroup M) [U.Normal] [IsElementaryAbelian 2 U]
    (hr : IsPReduced 2 U)
    (e : (pResidual 2 M ⧸ pCore 2 (pResidual 2 M)) ≃* alternatingGroup (Fin 5))
    (hsq : IsSQTK KnownSimple.IsKnownSimple (pResidual 2 M ⧸ pCore 2 (pResidual 2 M)))
    (hm : ⁅U,pResidual 2 M⁆ ≠ ⊥)
    (q : M →* Q) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set M))
    (ρ : Representation (ZMod 2) Q W) (hf : Function.Injective ρ) (hff : IsFFModule ρ) :
    IsIrrPlus ρ ((pResidual 2 M).map q)
      (subspaceCommutator ρ ⊤ ((pResidual 2 M).map q)) := by
  let K := pResidual 2 M
  let C := K.map q
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv e.symm
  have hz : center (K ⧸ pCore 2 K) = ⊥ := center_bot_of_five e
  have hker : (q.subgroupMap K).ker = pCore 2 K := by
    have hh := reduced_quasisimple_subgroupMap_ker U K hr hz hm
    simpa only [ker_subgroupMap,hk,QuotientGroup.ker_mk'] using hh
  let a : (K ⧸ pCore 2 K) ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap K)
        (q.subgroupMap_surjective K))
  let : IsSimpleGroup C := (a.symm.trans e).isSimpleGroup
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv a
  let : C.Normal := Normal.map inferInstance q hq
  have hcore : pCore 2 Q = ⊥ := by
    let b : (M ⧸ centralizer (U : Set M)) ≃* Q :=
      (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [← pCore_map_iso 2 b,hr.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hCC : centralizer (C : Set Q) ≤ C := by
    change centralizer ((K.map q) : Set Q) ≤ K.map q
    rw [show K = pResidual 2 M from rfl,map_pResidual_of_surjective 2 q hq]
    exact centralizer_pResidual_le_of_pCore_eq_bot hcore
  have hC : centralizer (C : Set Q) = ⊥ := by
    apply bot_unique
    intro x hx
    have hz' : (⟨x,hCC hx⟩ : C) ∈ center C := by
      apply Subgroup.mem_center_iff.mpr
      intro c
      exact Subtype.ext (hx c c.property)
    have he : center C = ⊥ := center_bot_of_five (a.symm.trans e)
    have hx1 : (⟨x,hCC hx⟩ : C) = 1 := mem_bot.mp (he ▸ hz')
    exact mem_bot.mpr (congrArg (fun c : C => (c : Q)) hx1)
  apply ff_card60_moved_irrPlus ρ C _ hC (hsq.knownSimple_of_equiv a) hf hff
  rw [← Nat.card_congr a.toEquiv,Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
  norm_num [Nat.factorial]
end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
