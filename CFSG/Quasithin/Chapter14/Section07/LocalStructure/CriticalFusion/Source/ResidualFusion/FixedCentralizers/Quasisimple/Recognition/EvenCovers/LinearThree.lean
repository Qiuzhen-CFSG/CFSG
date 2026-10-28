module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.EvenCovers.Setup
public import Theory.GroupAction.PGroupFixedLift
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.FourElementField
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.InvolutionConjugacy

/-!
# Excluding the PSL₃(4) central two-covers

The action on the actual central quotient is faithful because J is perfect.
It is therefore a nonidentity inner involution on PSL₃(4). The existing
matrix conjugacy calculation identifies its centralizer with UT₃(F₄), a
two-group. The fixed subgroup upstairs is a two-group too, since the kernel
is O₂(J); surjectivity on fixed points is unnecessary for this implication.
The original K in that fixed subgroup is nonsolvable, giving a contradiction.

This proves the linear branch with every allowed central two-kernel, without
a multiplier assumption or a chief-count certificate. The G₂(4) branch
remains a separate model-action comparison.
Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.7.68(2), printed p.1071; 1.1.5(3)(b), printed pp.501–503.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace EvenCoverSieve

theorem pslThreeFour_fixed_isTwoGroup {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] (α : MulAut A) (ha : α ^ 2 = 1) (hne : α ≠ 1)
    (hi : α ∈ (MulAut.conj (G := A)).range)
    (hz : center A = pCore 2 A) (hm : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 4) :
    IsPGroup 2 α.fixedSubgroup := by
  obtain ⟨k, hk, hf, hcard, ⟨e⟩⟩ := hm
  let : Field k := hk
  let : Finite k := hf
  let eZ : (A ⧸ center A) ≃* PSL(3,k) :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans e
  let β := MulAut.centralQuotientAction eZ α
  have hβ : β ^ 2 = 1 := by
    rw [← map_pow, ha, map_one]
  have hβne : β ≠ 1 := fun he => hne
    (MulAut.centralQuotientAction_injective eZ (he.trans (map_one _).symm))
  have hβi : ∃ x, β = MulAut.conj x := by
    apply (MulAut.centralQuotientAction_inner_iff eZ α).mpr
    obtain ⟨x, hx⟩ := hi
    exact ⟨x, hx.symm⟩
  let : Group.IsPerfect (SL(3,k)) := Atlas.sl_perfect 3 (by decide)
  obtain ⟨x, hx, he, hc⟩ := MulAut.inner_involution_representative
    (Group.IsPerfect.center_quotient_center_eq_bot (SL(3,k))) β
    (orderOf_eq_prime hβ hβne) hβi
  have htwo : IsPGroup 2 β.fixedSubgroup := by
    rw [hc]
    exact (Matrix.PSL3.EvenInnerCentralizers.centralizer_isTwoGroup_of_card_four k hcard).of_equiv
      (Matrix.PSL3.EvenInnerCentralizers.involutionCentralizerEquiv k (n := 2)
        (by decide) (by simpa using hcard) x (by intro h; simp [h] at hx)
        (hx ▸ pow_orderOf_eq_one x)).symm
  let f : A →* PSL(3,k) := eZ.toMonoidHom.comp (QuotientGroup.mk' (center A))
  have hker : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ eZ.injective, QuotientGroup.ker_mk', hz]
    exact pCore_isPGroup
  exact MulAut.isPGroup_fixedSubgroup_of_compatible α β f hker
    (fun x => (MulAut.centralQuotientAction_apply eZ α x).symm) htwo

theorem Case.not_pslThreeFour {d : Data T L V F W} {u : F.U} {Lu : Subgroup G}
    {α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))} (c : Case d u Lu α) :
    ¬ ClassicalGroup.IsPSL ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) 3 4 := by
  let := c.quasisimple
  let : IsQuasisimple (Lu.subgroupOf (d.fixedCentralizer u)) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe c.le_centralizer).symm
  intro hm
  exact c.fixed_not_isTwoGroup (pslThreeFour_fixed_isTwoGroup α
    (d.fixedComponentAction_sq u α c.conjugation)
    (d.fixedComponentAction_ne_one u α c.conjugation c.le_centralizer c.escapes)
    c.inner c.center_eq hm)

end EvenCoverSieve
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
