module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.Statements
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Two-residuals in the outer sporadic centralizer models

A quasisimple normal subgroup with a two-group quotient is exactly the
two-residual. In C₂×A₅ this is the A₅ factor. In Aut(PSL₃(2)) and S₈,
the existing component calculations identify it with the inner subgroup
and A₈, respectively. Quasisimplicity is inherited from the actual
component, rather than imposed on a residual.

Source: Aschbacher–Smith, 16.1.5(4),(8),(10), printed pp.1171–1172;
application: the outer branch of 16.3.11(3), printed p.1181.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.CoverExclusion.OuterResidual
open CFSG.Quasithin.Chapter16.OtherPreliminaries

private theorem perfect_twoPerfect {H : Type*} [Group H] [Finite H]
    [Group.IsPerfect H] : IsPPerfect 2 H := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (H ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (H ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro x _
  exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)

private theorem residual_quasisimple_of_normal {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] [IsQuasisimple N]
    (hp : IsPGroup 2 (H ⧸ N)) : IsQuasisimple (pResidual 2 H) := by
  rw [pResidual_eq_of_isPPerfect N perfect_twoPerfect hp]
  infer_instance

private noncomputable def botProdEquiv {H S : Type*} [Group H] [Group S] :
    (⊥ : Subgroup H).prod (⊤ : Subgroup S) ≃* S where
  toFun x := x.val.2
  invFun x := ⟨(1, x), ⟨rfl, trivial⟩⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext (mem_bot.mp x.property.1).symm rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The A₅ factor is the quasisimple two-residual of the M₁₂ outer row. -/
theorem m12_product_residual [IsQuasisimple Mathieu.A5] :
    IsQuasisimple (pResidual 2 (Mathieu.C2 × Mathieu.A5)) := by
  let N := (⊥ : Subgroup Mathieu.C2).prod (⊤ : Subgroup Mathieu.A5)
  let e : N ≃* Mathieu.A5 := botProdEquiv
  let := IsQuasisimple.of_mulEquiv e.symm
  apply residual_quasisimple_of_normal N
  apply IsPGroup.of_card (n := 1)
  have hn : Nat.card N = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hg : Nat.card (Mathieu.C2 × Mathieu.A5) = 120 := by
    rw [Nat.card_prod, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Mathieu.C2, Nat.card_eq_fintype_card]
  have he := N.card_mul_index
  rw [hn, hg] at he
  change Nat.card ((Mathieu.C2 × Mathieu.A5) ⧸ N) = 2
  rw [← Subgroup.index_eq_card]
  omega

/-- A component of S₈ is A₈, which has two-group quotient. -/
theorem hs_symmetric_residual (C : Subgroup JankoTwoHigmanSims.S8)
    (hc : IsComponent _ C) : IsQuasisimple (pResidual 2 JankoTwoHigmanSims.S8) := by
  have he := JankoTwoHigmanSims.HSOuter.symmetric_component_eq C hc
  have hq := hc.2
  rw [he] at hq
  let := hq
  apply residual_quasisimple_of_normal (alternatingGroup (Fin 8))
  apply IsPGroup.of_card (n := 1)
  change (alternatingGroup (Fin 8)).index = 2 ^ 1
  simp

/-- A component of Aut(PSL₃(2)) is its index-two inner subgroup. -/
theorem j2_automorphism_residual (C : Subgroup (MulAut Matrix.PSL3Two.PSL))
    (hc : IsComponent _ C) : IsQuasisimple (pResidual 2 (MulAut Matrix.PSL3Two.PSL)) := by
  let := Atlas.Comparisons.Exceptional.psl3Two_simple
  let e : Matrix.PSL3Two.PSL ≃* MulAut.innerSubgroup Matrix.PSL3Two.PSL :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot
      Matrix.PSL3Two.Automorphisms.center_psl_eq_bot)
  have he := hc.eq_innerSubgroup Matrix.PSL3Two.Automorphisms.center_psl_eq_bot
  have hq := hc.2
  rw [he] at hq
  let := hq
  apply residual_quasisimple_of_normal (MulAut.innerSubgroup Matrix.PSL3Two.PSL)
  apply IsPGroup.of_card (n := 1)
  have hn : Nat.card (MulAut.innerSubgroup Matrix.PSL3Two.PSL) = 168 :=
    (Nat.card_congr e.symm.toEquiv).trans Matrix.PSL3Two.card_PSL
  have h := (MulAut.innerSubgroup Matrix.PSL3Two.PSL).card_mul_index
  rw [hn, Matrix.PSL3Two.Automorphisms.card_aut] at h
  change Nat.card ((MulAut Matrix.PSL3Two.PSL) ⧸ _) = 2
  rw [← Subgroup.index_eq_card]
  omega

end CFSG.Quasithin.Chapter16.EnlargementSieve.CoverExclusion.OuterResidual
