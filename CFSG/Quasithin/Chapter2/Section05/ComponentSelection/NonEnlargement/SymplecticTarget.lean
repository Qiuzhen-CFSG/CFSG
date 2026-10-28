module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectSubgroups
public import Theory.SpecificGroups.Classical.EvenRankTwoOddRank
public import Theory.Quasithin.NormalTwoRank
/-! # Source rank-two models exclude proper symplectic Sylow overgroups
The original central quotient model has odd-prime rank at least two. Its
central two-kernel preserves that rank. The proved parabolic Levi obstruction
then forces every target subgroup containing the target's full Sylow and this
literal component image to equal the full symplectic group. This is the exact
symplectic target-row exclusion for the original non-enlargement argument;
construction and ordinary promotion of the containing component are separate.
Source: Aschbacher--Smith 2.5.6, printed p.554.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
open Theory.SpecificGroups.SymplecticFour
variable {K F F₀:Type*} [Group K] [Finite K] [Group.IsPerfect K]
    [Field F] [Finite F] [CharP F 2] [Field F₀] [Finite F₀]

theorem linear_in_symplectic_sylow_overgroup_eq_top
    (hZ:IsPGroup 2 (center K)) {n:ℕ} (hn:1<n) (hF₀:Nat.card F₀=2^n)
    (e:K⧸center K≃*PSL(3,F₀))
    (hF:2<Nat.card F) (P:Sylow 2 (Sp F)) (D:Subgroup (Sp F))
    (hPD:(P:Subgroup (Sp F))≤D) (f:K→*Sp F) (hf:Function.Injective f)
    (hKD:f.range≤D) : D=⊤ := by
  obtain ⟨p,hp,ho,hr⟩:=Theory.SpecificGroups.Classical.EvenRankTwoOddRank.linear hn hF₀
  let : Fact p.Prime:=⟨hp⟩
  have hK:2≤primeRank p K:=by
    rw [←primeRank_quotient_eq_of_isTwoGroup p ho (center K) hZ,primeRank_equiv p e]
    exact hr
  exact perfect_odd_rank_two_sylow_overgroup_eq_top ho hK hF P D hPD f hf hKD

theorem symplectic_in_symplectic_sylow_overgroup_eq_top [CharP F₀ 2]
    (hZ:IsPGroup 2 (center K))
    (e:K⧸center K≃*(Sp F₀⧸center (Sp F₀)))
    (hF:2<Nat.card F) (P:Sylow 2 (Sp F)) (D:Subgroup (Sp F))
    (hPD:(P:Subgroup (Sp F))≤D) (f:K→*Sp F) (hf:Function.Injective f)
    (hKD:f.range≤D) : D=⊤ := by
  have hK:2≤primeRank 3 K:=by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (center K) hZ,primeRank_equiv 3 e]
    exact Theory.SpecificGroups.Classical.EvenRankTwoOddRank.symplectic
  exact perfect_odd_rank_two_sylow_overgroup_eq_top (by decide : Odd 3) hK hF P D hPD f hf hKD
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
