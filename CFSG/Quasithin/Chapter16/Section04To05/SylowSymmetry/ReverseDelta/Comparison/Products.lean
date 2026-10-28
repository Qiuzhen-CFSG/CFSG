module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.M12Consequences
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Contracts
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The two product residuals in the M₁₂ row

The two-residuals of C₂×S₅ and C₂×A₅ are their actual A₅ factors.
The factors are perfect normal subgroups with two-group quotients, so the
residual characterization supplies genuine multiplicative equivalences.
These are intrinsic calculations for the two product rows in source
16.1.5(4), used in 16.4.11(2), printed pp.1171 and 1193 of the
Aschbacher–Smith combined manuscript (1 March 2004).
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison
open Subgroup Theory.GroupTheory

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

private noncomputable def residualEquivOfNormal {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] (e : N ≃* A5)
    (hp : IsPGroup 2 (H ⧸ N)) : pResidual 2 H ≃* A5 := by
  let : Group.IsPerfect A5 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect N := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  exact (MulEquiv.subgroupCongr
    (pResidual_eq_of_isPPerfect N perfect_twoPerfect hp)).trans e

private noncomputable def botProdEquiv {H K : Type*} [Group H] [Group K]
    (N : Subgroup K) : (⊥ : Subgroup H).prod N ≃* N where
  toFun x := ⟨x.val.2, x.property.2⟩
  invFun x := ⟨(1, x), ⟨rfl, x.property⟩⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext (mem_bot.mp x.property.1).symm rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem a5_card : Nat.card A5 = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

/-- The outer product row has two-residual A₅. -/
noncomputable def outerProductResidualEquiv : pResidual 2 (C2 × A5) ≃* A5 := by
  let N := (⊥ : Subgroup C2).prod (⊤ : Subgroup A5)
  let e : N ≃* A5 := (botProdEquiv (⊤ : Subgroup A5)).trans Subgroup.topEquiv
  apply residualEquivOfNormal N e
  apply IsPGroup.of_card (n := 1)
  have hn : Nat.card N = 60 := (Nat.card_congr e.toEquiv).trans a5_card
  have hg : Nat.card (C2 × A5) = 120 := by
    rw [Nat.card_prod, a5_card]
    norm_num [C2, Nat.card_eq_fintype_card]
  have he := N.card_mul_index
  rw [hn, hg] at he
  change Nat.card ((C2 × A5) ⧸ N) = 2
  rw [← Subgroup.index_eq_card]
  omega

/-- The nonsolvable inner product row also has two-residual A₅. -/
noncomputable def innerProductResidualEquiv : pResidual 2 InnerCentralizerModel ≃* A5 := by
  let N := (⊥ : Subgroup C2).prod (alternatingGroup (Fin 5))
  let e : N ≃* A5 := botProdEquiv (alternatingGroup (Fin 5))
  apply residualEquivOfNormal N e
  apply IsPGroup.of_card (n := 2)
  have hn : Nat.card N = 60 := (Nat.card_congr e.toEquiv).trans a5_card
  have hg : Nat.card InnerCentralizerModel = 240 := by
    rw [Nat.card_prod]
    norm_num [C2, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have he := N.card_mul_index
  rw [hn, hg] at he
  change Nat.card (InnerCentralizerModel ⧸ N) = 4
  rw [← Subgroup.index_eq_card]
  omega

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison
