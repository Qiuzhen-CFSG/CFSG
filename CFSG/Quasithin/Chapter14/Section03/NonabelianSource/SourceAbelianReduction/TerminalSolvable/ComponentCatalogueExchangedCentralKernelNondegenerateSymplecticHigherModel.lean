module
public import Theory.SpecificGroups.Symplectic.BinaryPerfect
public import Theory.SpecificGroups.Symplectic.FundamentalPlane.ThreeRank
public import Theory.LinearAlgebra.AlternatingFinrank
public import Theory.GroupTheory.QuasithinBasic
public import CFSG.Quasithin.ChapterG.Section12.ResidualModels
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateOrthogonalReduction

/-!
# Excluding higher-dimensional symplectic exchanged constituents

A symplectic basis identifies the actual form stabilizer with the standard
matrix group. In degree at least six that group is perfect and centerless,
so its embedded solvable residual is the full form stabilizer. Independent
cubic plane rotations give 3-rank at least three. In the original source,
centerlessness removes the central constituent kernel, while the terminal
quotient retains 3-rank at most two. These bounds contradict one another.

This specialized source argument replaces the stronger higher-dimensional
module-automorphism premise in the earlier conditional symplectic reduction.
It uses the original small-actor and quasithin hypotheses. G.12 recognition
and the separate degree-four case remain with the central-kernel owner.

Source: Aschbacher--Smith G.10.15, printed p.363, with the original
14.3.12--15 small-actor hypotheses, printed pp.993--994. The imported binary
perfectness module retains attribution for its authorized ATLAS adaptation.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterG.Section12
open Matrix.PSp4Three Subgroup Theory.GroupTheory
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A specified form isometry identifies its full stabilizer with the actual
symplectic matrix group. The degree-four residual consumer uses this same
group equivalence, with its original inclusion in the linear group. -/
def formStabilizerEquivSp {n : ℕ} (B : LinearMap.BilinForm (ZMod 2) V)
    (e : B.IsometryEquiv (form (n := n) (F := ZMod 2))) :
    formStabilizer B ≃* Sp n (ZMod 2) := by
  have he (x : Vector n (ZMod 2)) : e (e.symm x) = x := e.toLinearEquiv.apply_symm_apply x
  have he' (x : V) : e.symm (e x) = x := e.toLinearEquiv.symm_apply_apply x
  let f (g : formStabilizer B) : Vector n (ZMod 2) ≃ₗ[ZMod 2] Vector n (ZMod 2) :=
    (e.symm.toLinearEquiv.trans g.val).trans e.toLinearEquiv
  have hpres (g : formStabilizer B) (x y : Vector n (ZMod 2)) :
      form (f g x) (f g y) = form x y := by
    change form (e (g.val (e.symm x))) (e (g.val (e.symm y))) = _
    rw [e.map_app, g.property, ← e.map_app]
    simp only [he]
  let j : formStabilizer B →* Sp n (ZMod 2) := {
    toFun := fun g => ofLinear (f g) (hpres g)
    map_one' := by
      apply ext_action
      intro x
      simp [ofLinear_apply, f, he]
    map_mul' := by
      intro g h
      apply ext_action
      intro x
      simp [mul_smul, ofLinear_apply, f, he'] }
  apply MulEquiv.ofBijective j
  constructor
  · intro g h he
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    have hx := congrArg (fun a : Sp n (ZMod 2) => a • e x) he
    change ofLinear (f g) (hpres g) • e x = ofLinear (f h) (hpres h) • e x at hx
    simpa [f, he'] using congrArg e.symm hx
  · intro a
    let k : V ≃ₗ[ZMod 2] V := (e.toLinearEquiv.trans (toLinear a)).trans e.symm.toLinearEquiv
    have hk : k ∈ formStabilizer B := by
      intro x y
      rw [← e.map_app, ← e.map_app y x]
      change form (e (e.symm (toLinear a (e x)))) (e (e.symm (toLinear a (e y)))) = _
      simp only [he, toLinear_apply]
      exact preserves a _ _
    refine ⟨⟨k,hk⟩, ?_⟩
    apply ext_action
    intro x
    change ofLinear (f ⟨k,hk⟩) (hpres ⟨k,hk⟩) • x = a • x
    simp [f, k, he]

/-- In binary degree at least six, the literal symplectic residual is
centerless and contains an elementary abelian cubic subgroup of rank three. -/
theorem symplecticResidual_center_and_threeRank
    (B : LinearMap.BilinForm (ZMod 2) V) (halt : B.IsAlt) (hnd : B.Nondegenerate)
    (hd : 6 ≤ Module.finrank (ZMod 2) V) :
    center (embeddedResidual (formStabilizer B)) = ⊥ ∧
      3 ≤ primeRank 3 (embeddedResidual (formStabilizer B)) := by
  obtain ⟨n,hn⟩ := AlternatingForm.even_finrank B halt hnd
  have hn3 : 3 ≤ n := by omega
  obtain ⟨f⟩ := exists_isometry n B halt hnd (by omega)
  let e := formStabilizerEquivSp B f
  let : Finite (formStabilizer B) := Finite.of_injective e e.injective
  let : Group.IsPerfect (Sp n (ZMod 2)) := perfect_of_card_two hn3 (by simp)
  let : Group.IsPerfect (formStabilizer B) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hr : embeddedResidual (formStabilizer B) = formStabilizer B := by
    rw [embeddedResidual, Subgroup.solvableResidual_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [hr]
  constructor
  · apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply e.injective
    have he := (Subgroup.centerCongr e ⟨x,hx⟩).property
    change e x ∈ center (Sp n (ZMod 2)) at he
    rw [binary_center_eq_bot (by omega), mem_bot] at he
    simpa using he
  · rw [primeRank_equiv 3 e]
    exact hn3.trans Theory.SpecificGroups.Symplectic.FundamentalPlane.ThreeRank.rank_le_primeRank

end CFSG.Quasithin.ChapterG.Section12
end

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
namespace ExchangedCentralSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedCentralSource T M Mc F g B v L I)

include s

/-- The original constituent cannot be the symplectic residual in degree
at least six. The literal image equality is retained; no automorphism
invariance or full-linear properness premise is needed. -/
theorem false_of_symplectic_higher
    (hnd : (B.restrict I).Nondegenerate)
    (heq : s.constituentLinearAction.range = ChapterG.Section12.embeddedResidual
      (ChapterG.Section12.formStabilizer (B.restrict I)))
    (hd : 6 ≤ finrank (ZMod 2) I) : False := by
  have hm := ChapterG.Section12.symplecticResidual_center_and_threeRank
    (B.restrict I) (fun w => s.hypothesis.alternating w) hnd hd
  rw [← heq] at hm
  have hb := s.constituentImage_odd_primeRank_le_two hm.1 3 (by decide)
  omega

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
