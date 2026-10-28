module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.CoverRecovery
public import Theory.SpecificGroups.SL2.EvenCentralKernel
public import Theory.SpecificGroups.PSL2.OuterSolvable
public import BenderSuzuki.Converse.PSL2

/-!
# RankOneRecovery

The original two-core actor is recovered from its rank-one action. The binary endpoint is excluded by perfectness and solvability; even central-cover kernels are two-groups and hence vanish in the reduced actor.
Source: Aschbacher--Smith 11.0.1 and 12.2.2, pp.759--760,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
open ChapterB.QuasisimpleSource PerfectCentralCovering
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {H : Type*} [Group H]
    {ρ : Representation (ZMod 2) H D.space} {K : Subgroup H}
    (c : D.LiteralComparison ρ K)
include c

/-- The rank-one B.4.2 actor recovers the original two-core quotient,
including the exceptional double-cover kernel at field size four. -/
theorem rankOne_marking (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (F : BinaryField) (e : K ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :
    1 < F.degree ∧ ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ F.degree) := by
  let := hq
  let := c.nontrivial
  let p : Matrix.SpecialLinearGroup (Fin 2) F.Carrier ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F.Carrier :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi F.Carrier)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  let f := c.modelCover hq (e.trans p)
  let : Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F.Carrier) :=
    (e.trans p).symm.surjective.nontrivial
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F.Carrier) :=
    Group.IsPerfect.ofSurjective f.surjective
  have hF : 1 < F.degree := by
    by_contra hn
    have h1 : F.degree = 1 := by have := F.degree_pos; omega
    have hs := Theory.PSL2.OuterSolvable.isSolvable_of_card_two
      (show Nat.card F.Carrier = 2 by rw [F.card_eq,h1]; rfl)
    exact Group.IsPerfect.not_isSolvable _ hs
  have hk := Theory.SL2.perfect_central_kernel_isTwoGroup F.degree (by omega) F.card_eq f
  have hf : Function.Injective f.toMonoidHom := by
    apply f.toMonoidHom.ker_eq_bot_iff.mp
    apply bot_unique
    rw [← pCore_quotient_pCore_eq_bot 2]
    exact le_sSup ⟨inferInstance,hk⟩
  exact ⟨hF,F.Carrier,inferInstance,inferInstance,F.card_eq,
    ⟨MulEquiv.ofBijective f.toMonoidHom ⟨hf,f.surjective⟩⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
