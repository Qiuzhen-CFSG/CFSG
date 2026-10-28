module
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.Coordinates
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.Extension
public import Theory.SpecificGroups.SymplecticFour.LocalStructure
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement.OvergroupGeometry
/-! # Perfect odd-rank-two groups in binary symplectic overgroups
The determinant character kills every perfect image. Its image in a parabolic
therefore lies in the actual determinant kernel, whose elementary two-radical
quotient is SL₂. Odd-prime rank is consequently at most one. Combining this
with the proved proper Sylow-overgroup geometry excludes every proper
overgroup containing both the full Sylow and a perfect odd-rank-two image.
Source: Aschbacher--Smith 2.5.6, printed p.554, the rank-two model rows.
-/
public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour
variable {F:Type*} [Field F] [Finite F] [CharP F 2]
theorem pointLocal_odd_primeRank_le_one {p:ℕ} [Fact p.Prime] (ho:Odd p) :
    primeRank p (pointLocal (F:=F))≤1 := by
  apply Matrix.SL2.primeRank_le_one_of_two_kernel ho (pointQuotient (F:=F))
  rw [pointQuotient_ker]
  exact IsElementaryAbelian.isPGroup 2 _

theorem planeLocal_odd_primeRank_le_one {p:ℕ} [Fact p.Prime] (ho:Odd p) :
    primeRank p (planeLocal (F:=F))≤1 := by
  apply Matrix.SL2.primeRank_le_one_of_two_kernel ho (Plane.quotientMap (F:=F))
  rw [Plane.quotientMap_ker]
  exact IsElementaryAbelian.isPGroup 2 _

omit [Finite F] [CharP F 2] in
private theorem perfect_image_le_local {K:Type*} [Group K] [Group.IsPerfect K]
    (f:K→*Sp F) (W:Submodule F (Vector F)) (hf:f.range≤stabilizer W) :
    f.range≤determinantKernel W := by
  let : Group.IsPerfect f.range:=Group.IsPerfect.range f
  exact (le_map_solvableResidual_of_isPerfect f.range (stabilizer W) hf).trans
    (determinantKernel_solvableResidual_le W)

theorem no_perfect_odd_rank_two_in_parabolic {K:Type*} [Group K] [Finite K]
    [Group.IsPerfect K] {p:ℕ} [Fact p.Prime] (ho:Odd p) (hr:2≤primeRank p K)
    (f:K→*Sp F) (hf:Function.Injective f)
    (hlocal:f.range≤pointParabolic ∨ f.range≤planeParabolic) : False := by
  rcases hlocal with hpt | hpl
  · have him:f.range≤pointLocal:=perfect_image_le_local f (point F) hpt
    let j:K→*pointLocal (F:=F):=f.codRestrict _ (fun x=>him ⟨x,rfl⟩)
    have hj:Function.Injective j:=by
      intro x y h
      exact hf (congrArg Subtype.val h)
    have hb:=(primeRank_le_of_injective p j hj).trans (pointLocal_odd_primeRank_le_one ho)
    omega
  · have him:f.range≤planeLocal:=perfect_image_le_local f (plane F) hpl
    let j:K→*planeLocal (F:=F):=f.codRestrict _ (fun x=>him ⟨x,rfl⟩)
    have hj:Function.Injective j:=by
      intro x y h
      exact hf (congrArg Subtype.val h)
    have hb:=(primeRank_le_of_injective p j hj).trans (planeLocal_odd_primeRank_le_one ho)
    omega

theorem perfect_odd_rank_two_sylow_overgroup_eq_top {K:Type*} [Group K] [Finite K]
    [Group.IsPerfect K] {p:ℕ} [Fact p.Prime] (ho:Odd p) (hr:2≤primeRank p K)
    (hF:2<Nat.card F) (P:Sylow 2 (Sp F)) (D:Subgroup (Sp F))
    (hPD:(P:Subgroup (Sp F))≤D) (f:K→*Sp F) (hf:Function.Injective f)
    (hKD:f.range≤D) : D=⊤ := by
  by_contra hD
  obtain ⟨g,hg⟩:=ThreeResidualPlacement.proper_sylow_overgroup_parabolic_cover hF P D hPD hD
  let j:K→*Sp F:=(MulAut.conj g).toMonoidHom.comp f
  apply no_perfect_odd_rank_two_in_parabolic ho hr j ((MulAut.conj g).injective.comp hf)
  have him:j.range≤D.map (MulAut.conj g).toMonoidHom:=by
    rintro _ ⟨k,rfl⟩
    exact mem_map_of_mem _ (hKD ⟨k,rfl⟩)
  exact hg.elim (fun h=>Or.inl (him.trans h)) (fun h=>Or.inr (him.trans h))

end Theory.SpecificGroups.SymplecticFour
