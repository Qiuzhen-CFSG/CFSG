module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.CaseComparison
public import Theory.SpecificGroups.PSL3.BinaryCubicRankParity
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.SpecificGroups.SL2.BinaryLinearComparison
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank
public import Theory.SpecificGroups.FFG2DerivedCenter.Even

/-!
# Selecting the natural action on a large binary SL₃ component

Inspect the full irreducible B.5 table while retaining each action marking.
A centerless binary SL₃ has odd field degree and cubic rank at most one;
this excludes the symplectic and G₂ models. Orders exclude the finite small
rows and the triple cover of A₆. The established rank and Sylow-center
comparisons exclude SL₂ and the binary higher linear groups. Only the natural
SL₃ action remains, with its actual intertwining equivalence.
Source: Aschbacher–Smith B.4.2, B.5.1 and C.4.7, printed pp.86,99,153.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion

private theorem rank_one_of_centerless_linearThree (F : BinaryField)
    (hz : center SL(3,F.Carrier) = ⊥) : primeRank 3 SL(3,F.Carrier) ≤ 1 := by
  have ho : Odd F.degree := by
    apply Nat.not_even_iff_odd.mp
    intro he
    have hh := (Matrix.SL3.center_eq_bot_iff_card_mod_three F.Carrier).mp hz
    rw [F.card_eq, Nat.BinaryTorusParity.two_pow_mod_three,
      if_pos (Nat.even_iff.mp he)] at hh
    exact hh rfl
  rw [primeRank_equiv 3 (Matrix.SL3.equivProjectiveOfCenterEqBot F.Carrier hz)]
  exact Matrix.PSL3.BinaryCubicRankParity.rank_le_one_of_odd F.card_eq ho

private theorem no_centerless_rank_two (F : BinaryField) {E : Type*}
    [Group E] [Finite E] (e : SL(3,F.Carrier) ≃* E)
    (hz : center E = ⊥) (hr : 2 ≤ primeRank 3 E) : False := by
  have hc : center SL(3,F.Carrier) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [Nat.card_congr (centerCongr e).toEquiv,hz,Subgroup.card_bot]
  have hb := rank_one_of_centerless_linearThree F hc
  rw [primeRank_equiv 3 e] at hb
  omega

private theorem large_linearThree_card (F : BinaryField) (hF : 1 < F.degree) :
    60480 ≤ Nat.card SL(3,F.Carrier) := by
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
  have hq : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hF
  calc
    60480 = 4^3*(4^3-1)*(4^2-1) := by norm_num
    _ ≤ Nat.card F.Carrier ^ 3 * (Nat.card F.Carrier ^ 3 - 1) *
        (Nat.card F.Carrier ^ 2 - 1) := by gcongr

private theorem no_small_linearThree (F : BinaryField) (hF : 1 < F.degree)
    {E : Type*} [Group E] [Finite E] (e : SL(3,F.Carrier) ≃* E)
    (hc : Nat.card E < 60480) : False := by
  have hb := large_linearThree_card F hF
  rw [Nat.card_congr e.toEquiv] at hb
  omega

/-- The irreducible B.5 table on an actual large SL₃ actor selects its
natural module. Centerless rank-two models and the finite exceptions cannot
be mistaken for the supplied full special-linear group. -/
theorem linearThree_natural_of_irreducible_source
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) {C J : Subgroup D}
    (hc : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase σ C J)
    (F : BinaryField) (hF : 1 < F.degree) (mark : C ≃* SL(3,F.Carrier)) :
    ∃ E : BinaryField, IsLinearNatural (σ.comp C.subtype) E 3 := by
  cases hc with
  | linearThree E _ e _ => exact ⟨E,⟨e⟩⟩
  | linearTwo E _ e _ _ =>
    exact (Matrix.SL2.binary_not_equiv_linear_three F.degree_pos F.card_eq
      (e.groupEquiv.symm.trans mark)).elim
  | symplectic E hE _ e _ =>
    exact (no_centerless_rank_two F (mark.symm.trans e.groupEquiv)
      Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot
      (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic.trans
        (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator _).subtype
          (commutator _).subtype_injective))).elim
  | g2 E hE _ e _ _ =>
    have hq : 2 < Nat.card E.Carrier := by
      rw [E.card_eq]
      exact Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hE
    exact (no_centerless_rank_two F (mark.symm.trans e.groupEquiv)
      (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hq)
      (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2.trans
        (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator _).subtype
          (commutator _).subtype_injective))).elim
  | g2Two e _ _ =>
    exact (no_centerless_rank_two F (mark.symm.trans e.subgroupEquiv)
      Theory.SpecificGroups.g2_derived_two_center_eq_bot
      Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2).elim
  | symplecticTwo e _ =>
    apply False.elim
    apply no_small_linearThree F hF (mark.symm.trans e.subgroupEquiv)
    have hb := Nat.card_le_card_of_injective
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).subtype
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).subtype_injective
    rw [Theory.SpecificGroups.SymplecticFour.Binary.card_sp_two] at hb
    omega
  | symmetric d hd e _ _ =>
    apply False.elim
    apply no_small_linearThree F hF (mark.symm.trans e.subgroupEquiv)
    rcases hd with rfl | rfl <;> (rw [nat_card_alternatingGroup]; norm_num)
  | alternatingSix _ e _ _ =>
    exact (no_small_linearThree F hF (mark.symm.trans e.groupEquiv)
      (by (rw [nat_card_alternatingGroup]; norm_num))).elim
  | alternatingSeven _ _ e _ _ _ =>
    exact (no_small_linearThree F hF (mark.symm.trans e)
      (by (rw [nat_card_alternatingGroup]; norm_num))).elim
  | orthogonalSix _ _ e _ _ =>
    exact (no_small_linearThree F hF (mark.symm.trans e.groupEquiv)
      (by (rw [nat_card_alternatingGroup]; norm_num))).elim
  | symmetricEight _ e _ =>
    exact (no_small_linearThree F hF (mark.symm.trans e.subgroupEquiv)
      (by (rw [nat_card_alternatingGroup]; norm_num))).elim
  | binaryLinear d hd _ e _ =>
    exact (no_linearThree_binary_equiv F hd (mark.symm.trans e.groupEquiv)).elim
  | exteriorFive _ _ e _ _ _ =>
    exact (no_linearThree_binary_equiv F (Or.inr rfl) (mark.symm.trans e)).elim
  | tripleSix _ a _ =>
    apply False.elim
    apply no_small_linearThree F hF mark.symm
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center C),
      Nat.card_congr a.centerEquiv.toEquiv, Nat.card_congr a.quotientEquiv.toEquiv]
    (rw [nat_card_alternatingGroup]; norm_num)

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
