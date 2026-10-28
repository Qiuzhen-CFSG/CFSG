module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerActors
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.CentralizerStructure.Residual
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.CentralizerStructure.Quasisimple

/-!
# Component structure above the actual SL₂(p) centralizer residual

For p > 3, the full centralizer residual is the actual SL₂(p), including
every ambient two-extension. Its center has order two. In the residual
supplement K = C_G(z)^∞T, both residuals agree and the quotient is a two-group.
The quasisimple calculation therefore supplies the radical, layer and local-tau
clauses. The remaining model premise says that the inner four-group has a
nontrivial image modulo the radical; it is not inferred from an abstract
isomorphism of residuals.

Source: Aschbacher--Smith A.3.21(a), p.55; E.1.2(E2) and E.1.14(7), pp.210,214.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
variable {G : Type*} [Group G] [Finite G]

private theorem eCaseComponent_of_residual_sl2
    {p : ℕ} [Fact p.Prime] (hodd : Odd p) (hlarge : 3 < p)
    (T A K : Subgroup G)
    (e : solvableResidual K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (hres : pResidual 2 K = solvableResidual K)
    (hA : ¬ A.subgroupOf K ≤ solvableRadical K) : ECaseComponent T A K := by
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod p) (by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using hlarge)
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
    ⟨Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using Nat.succ_le_of_lt hlarge)⟩
  let : IsQuasisimple (solvableResidual K) := IsQuasisimple.of_mulEquiv e.symm
  have hzSL : IsPGroup 2 (center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) := by
    exact (GorensteinWalter.sl2ProjectiveProjection_ker_isPGroup (ZMod p) (by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using hodd)).of_equiv
        (MulEquiv.subgroupCongr (GorensteinWalter.sl2ProjectiveProjection_ker (ZMod p)))
  have hcenter : IsPGroup 2 (center (solvableResidual K)) :=
    hzSL.of_equiv (centerCongr e).symm
  have hq : IsPGroup 2 (K ⧸ solvableResidual K) :=
    (isPGroup_quotient_pResidual (G := K) 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq (hres))
  exact eCaseComponent_of_quasisimple_two_quotient T A K (solvableResidual K) hcenter hq hA


/-- All literal component clauses, with only the inner actor's survival in the
radical quotient left to the marked unitary action calculation. -/
theorem inner_centralizer_component_of_not_le_radical
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (hLT : L ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hlarge : 3 < p)
    (hmodel : ClassicalGroup.IsPSU L 3 p) (A : Subgroup G)
    (z : G) (hzL : z ∈ L) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hA : ¬ A.subgroupOf (centralizerResidualOvergroup T z) ≤
      solvableRadical (centralizerResidualOvergroup T z)) :
    ECaseComponent (T : Subgroup G) A (centralizerResidualOvergroup T z) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨ec⟩ := inner_centralizer_residual_equiv L T hLT hp hodd hlarge hmodel z hzL hz
  exact eCaseComponent_of_residual_sl2 (p := p) hodd hlarge
    (T : Subgroup G) A (centralizerResidualOvergroup T z)
    ((centralizerResidualOvergroup_residualEquiv hTz).trans ec)
    (centralizerResidualOvergroup_pResidual_eq hTz) hA

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
