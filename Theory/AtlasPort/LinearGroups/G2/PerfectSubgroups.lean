module

public import Theory.AtlasPort.LinearGroups.G2.HigherFieldResiduals
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.Quasithin.CoprimeRank

/-!
# Perfect odd-rank-two subgroups in binary G₂

A perfect subgroup of a root parabolic lies in its actual solvable residual.
The residual has a two-group kernel and an SL₂ quotient, so its odd-prime
rank is at most one. The full-Sylow parabolic cover therefore excludes a
proper Sylow overgroup containing a perfect odd-rank-two subgroup.

Source: Aschbacher–Smith A.3.12, printed pp.47–48, and F.1.12, pp.263–264.
-/

public section
open Subgroup Theory.GroupTheory
namespace Atlas.G2.PerfectSubgroups
open LieParabolicSetup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem local₁_odd_primeRank_le_one {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (local₁ (F := F)) ≤ 1 := by
  rw [← primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 (local₁ (F := F)))
    pCore_isPGroup,
    primeRank_equiv p (local₁CoreQuotientEquivPSL.trans
      RankOneFieldAutomorphisms.slEquivPSL.symm)]
  exact Matrix.SL2.binary_odd_primeRank_le_one ho

theorem local₂_odd_primeRank_le_one {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (local₂ (F := F)) ≤ 1 := by
  rw [← primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 (local₂ (F := F)))
    pCore_isPGroup,
    primeRank_equiv p (local₂CoreQuotientEquivPSL.trans longSLEquivPSL.symm)]
  exact Matrix.SL2.binary_odd_primeRank_le_one ho

theorem no_perfect_odd_rank_two_in_parabolic {K : Type*} [Group K] [Finite K]
    [Group.IsPerfect K] {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hr : 2 ≤ primeRank p K) (hq : 2 < Nat.card F)
    (f : K →* Model F) (hf : Function.Injective f)
    (hlocal : f.range ≤ parabolic₁ ∨ f.range ≤ parabolic₂) : False := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  rcases hlocal with hlocal | hlocal
  · have hh : f.range ≤ local₁ := by
      rw [← HigherFieldResiduals.parabolic₁_residual hq]
      exact le_map_solvableResidual_of_isPerfect _ _ hlocal
    let j := f.codRestrict (local₁ (F := F)) (fun x => hh ⟨x,rfl⟩)
    have hj : Function.Injective j := fun x y h => hf (congrArg Subtype.val h)
    have hb := (Theory.GroupTheory.primeRank_le_of_injective p j hj).trans (local₁_odd_primeRank_le_one ho)
    omega
  · have hh : f.range ≤ local₂ := by
      rw [← HigherFieldResiduals.parabolic₂_residual hq]
      exact le_map_solvableResidual_of_isPerfect _ _ hlocal
    let j := f.codRestrict (local₂ (F := F)) (fun x => hh ⟨x,rfl⟩)
    have hj : Function.Injective j := fun x y h => hf (congrArg Subtype.val h)
    have hb := (Theory.GroupTheory.primeRank_le_of_injective p j hj).trans (local₂_odd_primeRank_le_one ho)
    omega

/-- The literal perfect subgroup and supplied full Sylow cannot lie in a
proper subgroup of the actual octonion carrier. -/
theorem perfect_odd_rank_two_sylow_overgroup_eq_top
    {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hr : 2 ≤ primeRank p K)
    (hq : 2 < Nat.card F) (S : Sylow 2 (Model F)) (D : Subgroup (Model F))
    (hSD : (S : Subgroup (Model F)) ≤ D)
    (f : K →* Model F) (hf : Function.Injective f) (hKD : f.range ≤ D) : D = ⊤ := by
  by_contra hD
  obtain ⟨g,hg⟩ := ProperSylowOvergroups.conjugate_le_parabolic S D hSD hD
  let j := (MulAut.conj g).toMonoidHom.comp f
  have him : j.range ≤ D.map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.range_comp]
    exact map_mono hKD
  exact no_perfect_odd_rank_two_in_parabolic ho hr hq j
    ((MulAut.conj g).injective.comp hf) (hg.imp him.trans him.trans)

end Atlas.G2.PerfectSubgroups
