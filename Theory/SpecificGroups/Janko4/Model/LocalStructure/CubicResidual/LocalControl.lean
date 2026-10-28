module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CubicResidual.Contained
public import Theory.GroupTheory.CComponent.InvolutionSeedResidual
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.Mathieu.M22.TripleCover.ScalarAutomorphisms

/-!
# Local control for the marked cubic centralizer

The simultaneous centralizer maps onto the genuine triple cover of M₂₂.
Its kernel embeds in the order-two center of the original extraspecial
core. Hence its two-core is central, and the centralizer of its perfect
residual has order dividing six. These are the local inputs to the full
cubic-residual recognition, with the original matrix quotient unchanged.

Source: Aschbacher--Smith 4.2.13, printed p.612; GLS3 Table 5.3i.
The imported ATLAS matrices retain their original attribution and license.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.InvolutionCentralizers.First.CubicResidual
open OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreLinearModel TwoCoreComparison QuotientExtension Sporadic.Mathieu
attribute [local irreducible] modelGroup matrixA matrixB involutionCentralizer involutionTwoCore
  actionGroup derivedGroup scalarUnit

private theorem triple_twoCore : pCore 2 M22TripleCover = ⊥ := by
  have hd := card_dvd_of_le (IsQuasisimple.pCore_le_center (G := M22TripleCover) 2)
  rw [M22TripleCover.center_card] at hd
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := M22TripleCover)).exists_card_eq
  have hc := (by decide : Nat.Coprime 2 3).pow_left n
  rw [←hn] at hc
  exact card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hc (dvd_refl _) hd)

private theorem projection_kernel_card (x : centralizer) (ho : orderOf x = 3)
    (hx : centralizerExtension.rightHom x = scalarElement) :
    Nat.card (scalarCentralizerProjection x ho hx).ker ∣ 2 := by
  let f := scalarCentralizerProjection x ho hx
  have hq (c : f.ker) : c.val.val ∈ pCore 2 centralizer := by
    change c.val.val ∈ Q
    rw [←centralizerProjection_ker]
    have hh := congrArg coverInclusion c.property
    exact (scalarCentralizerProjection_inclusion x ho hx c.val).symm.trans
      (hh.trans (map_one _))
  let j : f.ker →* center (pCore 2 centralizer) := {
    toFun c := ⟨⟨c.val.val,hq c⟩,scalar_lift_core_fixed x hx ⟨c.val.val,hq c⟩
      (mem_centralizer_singleton_iff.mp c.val.property)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hi : Function.Injective j := by
    intro c d h
    exact Subtype.ext (Subtype.ext (congrArg
      (fun z : center (pCore 2 centralizer) => (z.val : centralizer)) h))
  have hc : Nat.card (center (pCore 2 centralizer)) = 2 :=
    by
      let e : center (pCore 2 centralizer) ≃* center involutionTwoCore := centerCongr First.twoCoreEquiv
      exact (Nat.card_congr e.toEquiv).trans TwoCoreComparison.center_card_two
  simpa only [hc] using card_dvd_of_injective j hi

/-- The simultaneous centralizer has central two-core. -/
theorem scalar_centralizer_core_central (x : centralizer) (ho : orderOf x = 3)
    (hx : centralizerExtension.rightHom x = scalarElement) :
    pCore 2 (Subgroup.centralizer ({x} : Set centralizer)) ≤
      center (Subgroup.centralizer ({x} : Set centralizer)) := by
  let D := Subgroup.centralizer ({x} : Set centralizer)
  let f := scalarCentralizerProjection x ho hx
  have hf := scalarCentralizerProjection_surjective x ho hx
  have hn : ((pCore 2 D).map f).Normal := (inferInstance : (pCore 2 D).Normal).map f hf
  have hm : (pCore 2 D).map f ≤ pCore 2 M22TripleCover :=
    le_sSup ⟨hn,pCore_isPGroup.map f⟩
  have hk : pCore 2 D ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp
    (bot_unique (triple_twoCore ▸ hm))
  exact hk.trans (scalarCentralizerProjection_central_kernel x ho hx)

/-- The centralizer of the simultaneous-centralizer residual has order dividing six. -/
theorem scalar_centralizer_residual_centralizer_card (x : centralizer) (ho : orderOf x = 3)
    (hx : centralizerExtension.rightHom x = scalarElement) :
    Nat.card (Subgroup.centralizer (solvableResidual
      (Subgroup.centralizer ({x} : Set centralizer)) : Set
        (Subgroup.centralizer ({x} : Set centralizer)))) ∣ 6 := by
  let D := Subgroup.centralizer ({x} : Set centralizer)
  let f := scalarCentralizerProjection x ho hx
  let S := solvableResidual D
  let Z := Subgroup.centralizer (S : Set D)
  have hm : S.map f = ⊤ := by
    rw [map_solvableResidual_eq f (scalarCentralizerProjection_surjective x ho hx),
      solvableResidual_eq_top]
  let g : Z →* center M22TripleCover := {
    toFun z := ⟨f z,by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨s,hs,rfl⟩ := hm.symm ▸ mem_top y
      simpa only [map_mul] using congrArg f (z.property s hs)⟩
    map_one' := Subtype.ext (map_one f)
    map_mul' a b := Subtype.ext (map_mul f (a : D) (b : D)) }
  let j : g.ker →* f.ker := {
    toFun z := ⟨z.val.val,congrArg (center M22TripleCover).subtype z.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hk : Nat.card g.ker ∣ 2 := (card_dvd_of_injective j
    (fun a b h => Subtype.ext (Subtype.ext
      (congrArg (fun y : f.ker => (y : D)) h)))).trans (projection_kernel_card x ho hx)
  have hi : Nat.card g.range ∣ 3 := by
    simpa only [M22TripleCover.center_card] using g.range.card_subgroup_dvd_card
  have hc := g.ker.card_mul_index
  rw [index_ker] at hc
  rw [←hc]
  exact Nat.mul_dvd_mul hk hi

end Janko4.InvolutionCentralizers.First.CubicResidual
