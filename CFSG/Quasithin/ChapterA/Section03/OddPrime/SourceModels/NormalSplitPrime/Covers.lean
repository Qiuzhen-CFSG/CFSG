module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Catalogue
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer

/-!
# Centerless and actual three-cover cases in the two-core quotient

Apply the completed A.3.6 covering theorem to the actual ordinary component
in H/O₂(H), using the full Theorem C central-quotient model. Quasisimplicity
excludes the natural and nilpotent alternatives: its generalized Fitting
subgroup is the whole group, whereas its Fitting subgroup is solvable.
The surviving cases have trivial center or a center isomorphic to C₃ with
one of the genuine ThreeCoverModel identifications.

This preserves the covering center and supplies the case distinction for
normal split-prime A.3.18. The prime-specific star quotient and diagonal
actor analysis remain separate source obligations.
Source: Aschbacher–Smith A.3.6 and A.3.18, printed pp.43–45,51–53.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.LocalModels
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
variable {H : Type*} [Group H] [Finite H]

theorem twoCore_center_cases
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)] :
    center (twoCoreComponent K) = ⊥ ∨
      (Nonempty (center (twoCoreComponent K) ≃* Multiplicative (ZMod 3)) ∧
        ThreeCoverModel (twoCoreComponent K)) := by
  let B := twoCoreComponent K
  let := (twoCore_isComponent hK).2
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : Nontrivial B := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center B))
  have hm := SourceComponents.sourceTheoremC_to_local
    (Group.IsPerfect.not_isMulCommutative (B ⧸ center B))
    (twoCore_central_quotient_model hH hK)
  have hs := SQTKStructure.OrdinarySource.ordinary_conclusion_of_model
    (pCore_quotient_pCore_eq_bot 2) B (twoCore_isComponent hK) hm
  have hn : generalizedFitting B ≠ fittingSubgroup B := by
    intro he
    have hfit : fittingSubgroup B = ⊤ := he.symm.trans generalizedFitting_eq_top_of_quasisimple
    let e : fittingSubgroup B ≃* B := (MulEquiv.subgroupCongr hfit).trans topEquiv
    exact Group.IsPerfect.not_isSolvable B
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  cases hs.1 with
  | simple _ hsimple _ =>
    let := hsimple
    left
    rcases (inferInstance : (center B).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp ht)).elim
  | cover _ hz hm => exact Or.inr ⟨hz, hm⟩
  | natural hn' => exact (hn hn'.1).elim
  | nilpotent hn' => exact (hn hn'.1).elim

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
