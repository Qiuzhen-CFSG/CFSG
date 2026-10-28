module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionTriality
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.LinearThree
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.SymplecticFour
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.NaturalBlockAlternative

/-!
# The linear and symplectic amalgam comparisons in 5.2.6

Restriction of an actual parabolic isomorphism to its solvable residual
identifies the original selected factor with the concrete point or line/plane
factor. Both are genuine natural L₂-blocks, including their quotient actions.
The binary parabolics are solvable (S₄ or C₂ × S₄), so cannot occur here.
Comparison of the actual PSL₂ quotient orders fixes the model exponent to
the original n. These arguments apply in both compatible orientations and
exclude both amalgams when the selected diagram factor is nonshort.

The maps use the whole overlap, retaining the odd Cartans and the scalar
quotient in PSL₃. These are local model comparisons, not an exhaustive
amalgam classification or an identification of the ambient completion.
Those steps and the independent F.1.12 core bound remain with
qt-d-1222-rankone-generic-global; original uniqueness retains its producer.

Source: Aschbacher–Smith 5.2.6–7, pp.650–651, and F.1.12(I)(1–2),
pp.262–264 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace BlockComparison
open Matrix.PSL3.LinearThree
open ChapterF.GreenBook.LieModels

private theorem binary_linear_parabolic_solvable
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = 2) (j : Bool) :
    Group.IsSolvable (CoveredLocals.parabolic F j) := by
  let := Fintype.ofFinite F
  let e : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by rwa [← Nat.card_eq_fintype_card])).symm
  have hu : ∀ a : F, a ≠ 0 → a = 1 := by
    intro a ha
    apply e.injective
    have hne : e a ≠ 0 := by simpa only [map_ne_zero] using ha
    have h : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
    simpa only [map_one] using h (e a) hne
  have hp : pointLocalSL F = pointParabolicSL F := by
    apply le_antisymm (pointLocalSL_le F)
    intro g hg
    have h := (mem_pointParabolicSL_iff F g).mp hg
    have hn : g.val 0 0 ≠ 0 := by
      intro hz
      have hi := congrArg (fun a : Matrix.SpecialLinearGroup (Fin 3) F => a.val 0 0)
        (inv_mul_cancel g)
      change (g⁻¹.val * g.val) 0 0 = 1 at hi
      simp [Matrix.mul_apply, Fin.sum_univ_three, h.1, h.2, hz] at hi
    exact (mem_pointLocalSL_iff F g).mpr ⟨hu _ hn,h⟩
  have hl : lineLocalSL F = lineParabolicSL F := by
    apply le_antisymm (lineLocalSL_le F)
    intro g hg
    have h := (mem_lineParabolicSL_iff F g).mp hg
    have hn : g.val 2 2 ≠ 0 := by
      intro hz
      have hi := congrArg (fun a : Matrix.SpecialLinearGroup (Fin 3) F => a.val 2 2)
        (mul_inv_cancel g)
      change (g.val * g⁻¹.val) 2 2 = 1 at hi
      simp [Matrix.mul_apply, Fin.sum_univ_three, h.1, h.2, hz] at hi
    exact (mem_lineLocalSL_iff F g).mpr ⟨h.1,h.2,hu _ hn⟩
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  cases j
  · change Group.IsSolvable (lineParabolic F)
    have he : lineLocal F = lineParabolic F := congrArg (fun K => K.map (Matrix.PSL3.projection F)) hl
    rw [← he]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (LinearThree.lineLocalEquivS4 F hF).toMonoidHom)
      (LinearThree.lineLocalEquivS4 F hF).injective
  · change Group.IsSolvable (pointParabolic F)
    have he : pointLocal F = pointParabolic F := congrArg (fun K => K.map (Matrix.PSL3.projection F)) hp
    rw [← he]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (LinearThree.pointLocalEquivS4 F hF).toMonoidHom)
      (LinearThree.pointLocalEquivS4 F hF).injective

private def residualFactorEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (P K : Subgroup X) (Q J : Subgroup Y) (e : P ≃* Q)
    (hP : (solvableResidual P).map P.subtype = K)
    (hQ : (solvableResidual Q).map Q.subtype = J) : K ≃* J :=
  (((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective).trans
    (MulEquiv.subgroupCongr hP)).symm.trans
    (e.solvableResidualEquiv.trans
      (((solvableResidual Q).equivMapOfInjective Q.subtype Q.subtype_injective).trans
        (MulEquiv.subgroupCongr hQ)))

variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
include d h hTH hp

/-- Restriction to the solvable residual identifies the actual linear local
factor; solvability excludes the binary field before this restriction. -/
theorem linear_parabolic_factor
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) (i : Fin 2) (j : Bool)
    (e : ChapterF.Source.parabolic ![L,R] (sourceS L H) i ≃*
      CoveredLocals.parabolic F j) :
    1 < m ∧ Nonempty (![L,R] i ≃* CoveredLocals.localProjective F j) ∧
      ChapterC.IsL2EvenBlock (![L,R] i) m := by
  have hgt : 1 < m := by
    by_contra hn
    have hm1 : m = 1 := by omega
    have hc : Nat.card F = 2 := by simpa only [hm1,pow_one] using hF
    let := binary_linear_parabolic_solvable F hc j
    exact d.parabolics_not_solvable h hp i
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  have hc : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hgt
  have hr : (solvableResidual (CoveredLocals.parabolic F j)).map
      (CoveredLocals.parabolic F j).subtype = CoveredLocals.localProjective F j := by
    cases j
    · exact ParabolicResiduals.lineParabolic_residual F hc
    · exact ParabolicResiduals.pointParabolic_residual F hc
  let a := residualFactorEquiv _ _ _ _ e (d.parabolic_residuals h hTH hp i) hr
  have hb : ChapterC.IsL2EvenBlock (CoveredLocals.localProjective F j) m := by
    cases j
    · exact LinearThree.lineLocal_isL2EvenBlock F hF hgt
    · exact LinearThree.pointLocal_isL2EvenBlock F hF hgt
  exact ⟨hgt,⟨a⟩,hb.of_equiv a.symm⟩

open Theory.SpecificGroups.SymplecticFour
/-- The symplectic analogue uses the actual point/plane determinant kernels.
At the binary field both parabolics are C₂ × S₄ and hence solvable. -/
theorem symplectic_parabolic_factor
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) (i : Fin 2) (j : Bool)
    (e : ChapterF.Source.parabolic ![L,R] (sourceS L H) i ≃*
      (if j then Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F) else planeParabolic : Subgroup (Sp F))) :
    1 < m ∧ Nonempty (![L,R] i ≃*
      (if j then Theory.SpecificGroups.SymplecticFour.pointLocal (F := F) else planeLocal : Subgroup (Sp F))) ∧
      ChapterC.IsL2EvenBlock (![L,R] i) m := by
  have hgt : 1 < m := by
    by_contra hn
    have hm1 : m = 1 := by omega
    have hc : Nat.card F = 2 := by simpa only [hm1,pow_one] using hF
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm (Fin 2)) :=
      Group.isSolvable_of_comm (by decide)
    have a : (if j then Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F) else planeParabolic : Subgroup (Sp F)) ≃*
        Binary.LocalProduct := by
      cases j
      · exact Binary.planeParabolicEquivProd hc
      · exact Binary.pointParabolicEquivProd hc
    exact d.parabolics_not_solvable h hp i
      (Group.isSolvable_of_isSolvable_injective (f := (e.trans a).toMonoidHom)
        (e.trans a).injective)
  have hr : (solvableResidual (if j then Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F) else planeParabolic : Subgroup (Sp F))).map
      (if j then Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F) else planeParabolic : Subgroup (Sp F)).subtype =
        (if j then Theory.SpecificGroups.SymplecticFour.pointLocal (F := F) else planeLocal : Subgroup (Sp F)) := by
    cases j
    · let := planeLocal_perfect hF hgt
      exact planeParabolic_solvableResidual_eq_of_perfect
    · let := pointLocal_perfect hF hgt
      exact pointParabolic_solvableResidual_eq_of_perfect
  let a := residualFactorEquiv _ _ _ _ e (d.parabolic_residuals h hTH hp i) hr
  have hb : ChapterC.IsL2EvenBlock
      (if j then Theory.SpecificGroups.SymplecticFour.pointLocal (F := F) else planeLocal : Subgroup (Sp F)) m := by
    cases j
    · exact SymplecticFour.planeLocal_isL2EvenBlock hF hgt
    · exact SymplecticFour.pointLocal_isL2EvenBlock hF hgt
  exact ⟨hgt,⟨a⟩,hb.of_equiv a.symm⟩

end BlockComparison

private theorem exponent_eq_of_left_block
    {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {T : Sylow 2 G} {L W : Subgroup G} {n m : ℕ}
    (h : Input κ T L W n) (hb : ChapterC.IsL2EvenBlock L m) : m = n := by
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := h.linear
  obtain ⟨_,_,E,_,_,_,hq,_⟩ := hb
  obtain ⟨K,_,_,hK,⟨b⟩⟩ := hq
  let := Fintype.ofFinite F
  let := Fintype.ofFinite K
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  have hc := binary_psl_field_card_eq (a.symm.trans b)
  rw [hF,hK] at hc
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2) hc).symm

open ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
include d h hTH hp

/-- In either compatible L₃ orientation both original local factors are genuine
natural blocks at the original exponent. This includes exclusion of q = 2. -/
theorem Preparation.linear_amalgam_blocks
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,R] (sourceS L H)) (LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,R] (sourceS L H)) (LinearThree.amalgam F).reverse)) :
    m = n ∧ ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n := by
  have hb : ChapterC.IsL2EvenBlock L m ∧ ChapterC.IsL2EvenBlock R m := by
    rcases he with he | he
    · obtain ⟨e⟩ := he
      exact ⟨(BlockComparison.linear_parabolic_factor d h hTH hp F hm hF 0 true e.left).2.2,
        (BlockComparison.linear_parabolic_factor d h hTH hp F hm hF 1 false e.right).2.2⟩
    · obtain ⟨e⟩ := he
      exact ⟨(BlockComparison.linear_parabolic_factor d h hTH hp F hm hF 0 false e.left).2.2,
        (BlockComparison.linear_parabolic_factor d h hTH hp F hm hF 1 true e.right).2.2⟩
  have he := exponent_eq_of_left_block h hb.1
  exact ⟨he,he ▸ hb⟩

/-- In either compatible Sp₄ orientation both original local factors are genuine
natural blocks. The actual PSL₂ quotients force the field to be the original one. -/
theorem Preparation.symplectic_amalgam_blocks
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,R] (sourceS L H)) (SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,R] (sourceS L H)) (SymplecticFour.amalgam F).reverse)) :
    m = n ∧ ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n := by
  have hb : ChapterC.IsL2EvenBlock L m ∧ ChapterC.IsL2EvenBlock R m := by
    rcases he with he | he
    · obtain ⟨e⟩ := he
      exact ⟨(BlockComparison.symplectic_parabolic_factor d h hTH hp F hm hF 0 true e.left).2.2,
        (BlockComparison.symplectic_parabolic_factor d h hTH hp F hm hF 1 false e.right).2.2⟩
    · obtain ⟨e⟩ := he
      exact ⟨(BlockComparison.symplectic_parabolic_factor d h hTH hp F hm hF 0 false e.left).2.2,
        (BlockComparison.symplectic_parabolic_factor d h hTH hp F hm hF 1 true e.right).2.2⟩
  have he := exponent_eq_of_left_block h hb.1
  exact ⟨he,he ▸ hb⟩

/-- The nonshort selected diagram factor excludes both orientations of both
natural-block amalgams, over every positive binary exponent. -/
theorem Preparation.not_block_amalgams (hnot : ¬ ChapterC.IsShort R)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) :
    let α := sourceParabolicAmalgam ![L,R] (sourceS L H)
    ¬ Nonempty (RankTwoAmalgam.Iso α (LinearThree.amalgam F)) ∧
      ¬ Nonempty (RankTwoAmalgam.Iso α (LinearThree.amalgam F).reverse) ∧
      ¬ Nonempty (RankTwoAmalgam.Iso α (SymplecticFour.amalgam F)) ∧
      ¬ Nonempty (RankTwoAmalgam.Iso α (SymplecticFour.amalgam F).reverse) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro he
    exact hnot (d.linear_amalgam_blocks h hTH hp F hm hF (Or.inl he)).2.2.2.1
  · intro he
    exact hnot (d.linear_amalgam_blocks h hTH hp F hm hF (Or.inr he)).2.2.2.1
  · intro he
    exact hnot (d.symplectic_amalgam_blocks h hTH hp F hm hF (Or.inl he)).2.2.2.1
  · intro he
    exact hnot (d.symplectic_amalgam_blocks h hTH hp F hm hF (Or.inr he)).2.2.2.1

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
