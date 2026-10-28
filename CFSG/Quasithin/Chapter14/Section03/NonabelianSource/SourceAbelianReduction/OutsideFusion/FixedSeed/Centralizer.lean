module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion.FixedSeed.Factors
public import Theory.GroupTheory.ElementaryFactorSwapCentralizer

/-!
# The fixed-seed centralizer inside the original parabolic core

The specified t exchanges the original two maximal elementary factors.
Every involution in R belongs to one of them. Since t fixes their
intersection V, the elementary-factor centralizer argument gives C_R(t)=V.
This supplies the fixed subgroup for the remaining orbit calculation in
the coset Rt; it does not assert that orbit calculation.

Source: Aschbacher--Smith, Quasithin Groups, 14.3.21(2), printed p.998.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The fixed subgroup in R for the specified outside involution is the seed. -/
theorem source_fixed_seed_core_centralizer_of_solvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (t : G) (ht : t ∈ (T : Subgroup G)) (ht2 : orderOf t = 2)
    (htout : t ∉ (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.H.pCoreIn 2)
    (htV : t ∈ centralizer (rankTwoSeed T M : Set G)) :
    (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊓ centralizer ({t} : Set G) =
      rankTwoSeed T M := by
  obtain ⟨A,B,hAR,_,hEA,hEB,_,_,hi,hAB,_,_,hBN,hmax,hswap⟩ :=
    source_outside_element_exchanges_factors_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs t ht htout
  let := hEA
  let := hEB
  have hn : A ≤ normalizer (B : Set G) :=
    hAR.trans ((pCoreIn_le 2 _).trans (le_sup_left.trans hBN))
  have hcover : ∀ x ∈ A ⊔ B, x ^ 2 = 1 → x ∈ A ∨ x ∈ B := by
    intro x hx hx2
    let : IsElementaryAbelian 2 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one hx2
    rcases hmax (zpowers x) inferInstance (zpowers_le.mpr (hAB ▸ hx)) with hA | hB
    · exact Or.inl (hA (mem_zpowers x))
    · exact Or.inr (hB (mem_zpowers x))
  have htsq : t ^ 2 = 1 := by rw [←ht2]; exact pow_orderOf_eq_one t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using htsq)
  have hswap' : A.map (MulAut.conj t).toMonoidHom = B := by
    change A.map (MulAut.conj t⁻¹).toMonoidHom = B at hswap
    rwa [hti] at hswap
  have hfix : t ∈ centralizer (A ⊓ B : Set G) := by
    change t ∈ centralizer ((A ⊓ B : Subgroup G) : Set G)
    rwa [hi]
  simpa only [hAB,hi] using
    elementary_factor_swap_centralizer A B hn hcover t htsq hswap' hfix

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
