module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ComponentSource.LinearThree
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ComponentSource.Eight
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieFixers.SmallRank
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.Automorphisms
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.SymplecticOrthogonal.RankTwo
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.SplitExceptional
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.TwistedExceptional.BinaryG2Core
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.HigherLinear
public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups.CentralCover
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
public import Theory.SpecificGroups.BinaryLinear.SylowPointwiseInner
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract

/-!
# Sylow bounds for every actual B.4.2 component row

Each model equivalence transports its proved pointwise Sylow fixer and proper
Sylow-overgroup bounds to the original actor. The linear-three and triple-A₆
rows pass through their literal central quotients. The binary symplectic and
G₂ exceptions use their actual derived groups. Only the five- and seven-letter
rows survive as alternatives to the proper-overgroup bound.

Source: Aschbacher--Smith B.1.13, pp.73--74, and B.4.2, p.86.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource
open ChapterB.ComponentRecognition.SylowOvergroups ChapterB.QuasisimpleSource
open ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers

private theorem six_bound : ProperSylowFittingBound (alternatingGroup (Fin 6)) :=
  AlternatingSix.ProperSylowOvergroups.centralCover_fitting_bound (MonoidHom.id _)
    Function.surjective_id (by simp)

private theorem eight_bound : ProperSylowFittingBound (alternatingGroup (Fin 8)) := by
  intro S X hSX hX
  rw [generalizedFitting_eq_pCore_of_selfCentralizing 2
    (alternatingEight_sylow_overgroup_core S X hSX hX)]
  exact le_sup_left

private theorem binary_g2_bound :
    ProperSylowFittingBound (commutator (Atlas.G2.Model (ZMod 2))) := by
  intro S X hSX hX
  rw [generalizedFitting_eq_pCore_of_selfCentralizing 2
    (TwistedExceptional.BinaryG2.centralizer_twoCore_le S X hX hSX)]
  exact le_sup_left

private theorem binary_linear_fixer {d : ℕ} (hd : d = 4 ∨ d = 5) :
    SylowFixerIsTwoGroup SL(d,ZMod 2) := by
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup d) :=
    Finite.of_injective (fun g : BinaryLinear.OuterCyclic.LinearGroup d =>
      (g : (Fin d → ZMod 2) → (Fin d → ZMod 2))) DFunLike.coe_injective
  exact fixer_of_equiv (BinaryLinear.OuterCyclic.slEquivLinear d)
    (fixer_twoGroup_of_inner (BinaryLinear.OuterCyclic.sylow_fixing_inner hd))

private theorem binary_linear_bound {d : ℕ} (hd : d = 4 ∨ d = 5) :
    ProperSylowFittingBound SL(d,ZMod 2) := by
  apply properSylowFittingBound_of_equiv
    (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < d)).symm
  rcases hd with rfl | rfl
  · exact linearFour_properSylowFittingBound
  · exact properSylowFittingBound_psl5_two

private theorem transfer {L M : Type*} [Group L] [Group M] [Finite L]
    (e : L ≃* M) (hf : SylowFixerIsTwoGroup M) (hb : ProperSylowFittingBound M) :
    SylowFixerIsTwoGroup L ∧ ProperSylowFittingBound L :=
  ⟨fixer_of_equiv e hf, properSylowFittingBound_of_equiv e hb⟩

/-- Every actual B.4 actor has the two Sylow estimates, except for the
explicit five- and seven-letter alternatives in the proper-overgroup step. -/
theorem source_action_sylow_bounds
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L H : Subgroup D) [IsQuasisimple L]
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H) :
    SylowFixerIsTwoGroup L ∧ (ProperSylowFittingBound L ∨
      Nonempty (L ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (L ≃* alternatingGroup (Fin 7))) := by
  cases h with
  | linearTwo F _ e _ _ =>
    let q := e.groupEquiv.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F.Carrier))
    exact ⟨fixer_of_equiv q linearTwo_fixer,
      Or.inl (properSylowFittingBound_psl2 F.Carrier F.degree F.degree_pos F.card_eq q)⟩
  | linearThree F _ e _ =>
    let : IsQuasisimple SL(3,F.Carrier) := IsQuasisimple.of_mulEquiv e.groupEquiv
    have hf : SylowFixerIsTwoGroup SL(3,F.Carrier) :=
      fixer_twoGroup_of_centralQuotient (MulEquiv.refl _)
        (linearThree_fixer F.Carrier F.degree_pos F.card_eq)
    have hb : ProperSylowFittingBound SL(3,F.Carrier) :=
      properSylowFittingBound_of_centralQuotient (MulEquiv.refl _)
        (linearThree_properSylowFittingBound F.Carrier F.degree_pos F.card_eq)
    exact (transfer e.groupEquiv hf hb).imp_right Or.inl
  | symplectic F hF _ e _ =>
    exact (transfer e.groupEquiv (symplecticFour_fixer F.Carrier hF F.card_eq)
      (properSylowFittingBound_sp_four F.Carrier F.degree hF F.card_eq)).imp_right Or.inl
  | symplecticTwo e _ =>
    let q := e.subgroupEquiv.trans
      (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (F := ZMod 2) (by simp))
    exact (transfer q (alternating_fixer 6 (by decide)) six_bound).imp_right Or.inl
  | g2 F hF _ e _ _ =>
    have hc : 2 < Nat.card F.Carrier := by
      rw [F.card_eq]
      exact (show (2 : ℕ)^1 < 2^F.degree from Nat.pow_lt_pow_right (by decide) hF)
    exact (transfer e.groupEquiv (g2_fixer F.Carrier hc)
      (properSylowFittingBound_g2 F.Carrier (MulEquiv.refl _))).imp_right Or.inl
  | g2Two e _ _ =>
    exact (transfer e.subgroupEquiv g2Derived_fixer binary_g2_bound).imp_right Or.inl
  | symmetric n hn e _ _ =>
    refine ⟨fixer_of_equiv e.subgroupEquiv (alternating_fixer n (by omega)), Or.inr ?_⟩
    rcases hn with rfl | rfl
    · exact Or.inl ⟨e.subgroupEquiv⟩
    · exact Or.inr ⟨e.subgroupEquiv⟩
  | alternatingSix _ e _ _ =>
    exact (transfer e.groupEquiv (alternating_fixer 6 (by decide)) six_bound).imp_right Or.inl
  | alternatingSeven _ _ e _ _ _ =>
    exact ⟨fixer_of_equiv e (alternating_fixer 7 (by decide)), Or.inr (Or.inr ⟨e⟩)⟩
  | tripleSix _ a _ =>
    exact ⟨alternating_centralCover_fixer (by decide : 5 ≤ 6) a.quotientEquiv,
      Or.inl (properSylowFittingBound_of_centralQuotient a.quotientEquiv six_bound)⟩
  | binaryLinear d hd _ e _ =>
    exact (transfer e.groupEquiv (binary_linear_fixer hd) (binary_linear_bound hd)).imp_right Or.inl
  | orthogonalSix _ _ e _ _ =>
    exact (transfer e.groupEquiv (alternating_fixer 8 (by decide)) eight_bound).imp_right Or.inl
  | symmetricEight _ e _ =>
    exact (transfer e.subgroupEquiv (alternating_fixer 8 (by decide)) eight_bound).imp_right Or.inl
  | exteriorFive _ _ e _ _ _ =>
    exact (transfer e (binary_linear_fixer (Or.inr rfl))
      (binary_linear_bound (Or.inr rfl))).imp_right Or.inl
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource
