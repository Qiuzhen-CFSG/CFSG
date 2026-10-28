module

public import Theory.GroupTheory.CComponent.TwoComponent.Involution
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismOrder
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.OuterInvolutions
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models
public import Theory.SpecificGroups.PSL2.RankOneRoots
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.GroupAction.InnerInvolutionGeometry
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Two-components in involution fixed groups of binary PSL₂

Every involutory automorphism of PSL₂ over a finite field of characteristic
two has either a solvable fixed subgroup or a fixed subgroup with trivial
odd core. Inner involutions have two-group centralizers. Semilinear coverage
and determinant-one Hilbert--90 identify the fixed subgroup of an outer
involution with PSL₂ over the actual fixed field. That group is simple with
even order, except over the two-element field, where it is solvable.

Consequently every two-component of every such fixed subgroup is
quasisimple, including the outer involutions of PSL₂(4). The definition
uses the intrinsic quotient L/O_{2'}(L). No Sylow-fixation hypothesis is used.

Sources: GLS II, Definition 2.4 (`refs/KGroup/GLS2/ChapterA.tex`), and GLS III,
§4.9 (`refs/KGroup/GLS3/chapter4.tex`), for the field-automorphism centralizer.
The imported root and semilinear calculations retain their own source references.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem solvable_or_oddCore_eq_bot :
    _root_.Group.IsSolvable (Group F) ∨ pPrimeCore 2 (Group F) = ⊥ := by
  classical
  let : Fintype F := Fintype.ofFinite F
  by_cases hsmall : Nat.card F = 2
  · exact Or.inl (OuterSolvable.isSolvable_of_card_two hsmall)
  right
  have heven : 2 ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.dvd_of_mod_eq_zero (FiniteField.even_card_of_char_two (ringChar.eq F 2))
  have hlarge : 4 ≤ Nat.card F := by have := Nat.card_pos (α := F); omega
  let : IsSimpleGroup (Group F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
  rcases (inferInstance : (pPrimeCore 2 (Group F)).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  have hcard : Nat.card (Group F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← Nat.card_congr (sl2QuotientEquiv F).toEquiv,
      BenderSuzuki.External.huppert614_card_specialLinearGroup]
  have hc := pPrimeCore_coprime_card (p := 2) (G := Group F)
  rw [ht, Subgroup.card_top, hcard] at hc
  exact (Nat.prime_two.coprime_iff_not_dvd.mp hc (dvd_mul_of_dvd_left heven _)).elim

/-- The full fixed subgroup is solvable or has trivial odd core. -/
theorem charTwo_fixed_solvable_or_oddCore_eq_bot
    (a : MulAut (Group F)) (ha : orderOf a = 2) :
    _root_.Group.IsSolvable a.fixedSubgroup ∨ pPrimeCore 2 a.fixedSubgroup = ⊥ := by
  classical
  by_cases hi : ∃ g : Group F, a = MulAut.conj g
  · obtain ⟨g, hg, _, hfix⟩ := MulAut.inner_involution_representative
      Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot a ha hi
    obtain ⟨_, _, _, _, _, hp⟩ := involution_root_geometry g hg
    left
    rw [hfix]
    let : _root_.Group.IsNilpotent (centralizer ({g} : Set (Group F))) := hp.isNilpotent
    infer_instance
  have ha2 : a ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
  obtain ⟨g, σ, heq⟩ := BenderSuzuki.ZD.Linear.semilinear_coverage a
  have hout : a ∉ inner F := by simpa only [mem_inner_iff] using hi
  obtain ⟨_, c, hc⟩ := outer_conjugate_field_of_semilinear a ha2 g σ heq hout
  let e : a.fixedSubgroup ≃* Group (FixedBy.subfield F σ) :=
    ((MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup hc.symm)).trans
      (MulAut.fixedSubgroupCongr (MulAut.conj c) (fieldAut σ)).symm).trans
      (fieldAutFixedEquiv σ)
  rcases solvable_or_oddCore_eq_bot (F := FixedBy.subfield F σ) with hs | ho
  · let := hs
    exact Or.inl (_root_.Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective)
  · right
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [pPrimeCore_map_iso, ho, Subgroup.map_bot]

/-- The source B₂ condition for every finite characteristic-two PSL₂. -/
theorem charTwo_hasInvolutoryB2 : HasInvolutoryB2 (Group F) := by
  intro a ha L hL
  rcases charTwo_fixed_solvable_or_oddCore_eq_bot a ha with hs | ho
  · let := hs
    exact (hL.1.not_isSolvable inferInstance).elim
  · exact (hL.isComponent_of_oddCore_eq_bot ho).2

end Theory.PSL2
