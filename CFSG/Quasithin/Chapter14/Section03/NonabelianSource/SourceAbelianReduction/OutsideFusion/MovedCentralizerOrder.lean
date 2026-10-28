module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion.MovedSeed
public import Theory.GroupTheory.ElementaryPairFixedCardSquare

/-!
# Order eight for the moved-seed centralizer

An involution of T outside the original RQ exchanges the two normal elementary
factors A and B of R. Their intersection is the seed V of order four. When the
involution moves V, its fixed subgroup on V is the marked point of order two.
The elementary fixed-point count makes these fixed elements coboundaries;
counting the fixed group through the literal quotient by B gives
|C_R(t)|·4 = 16·2.

The conjugation fixed subgroup is identified with the actual ambient
centralizer, so this discharges exactly the cardinality premise of
`source_moved_seed_core_return_of_centralizer_card`.

Source: Aschbacher--Smith 14.3.21(2), printed p.998, the moved-seed case
using Aschbacher, *Sporadic Groups* (1994), Exercise 2.8.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition
variable {G : Type*} [Group G] [Finite G]

variable
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
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs

/-- The moved-seed centralizer has order eight in the original source context. -/
theorem source_moved_centralizer_card_eight
    (t : G) (htT : t ∈ (T : Subgroup G)) (ht2 : orderOf t = 2)
    (htout : t ∉ (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.H.pCoreIn 2)
    (htV : t ∉ centralizer (rankTwoSeed T M : Set G)) :
    Nat.card ((F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊓
      centralizer ({t} : Set G) : Subgroup G) = 8 := by
  obtain ⟨_, A, B, _, _, _, _, hEA, hEB, hAc, _, hi, hgen, _, hnA, hnB, hAB, _, _⟩ :=
    source_outside_factor_exchange_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs t htT htout
  let := hEA
  let := hEB
  have htpow : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using htpow)
  have ha2 : (MulAut.conj t) ^ 2 = 1 := by rw [← map_pow, htpow, map_one]
  have ha : Function.Involutive (MulAut.conj t) := by
    intro x
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using
      congrArg (fun a : MulAut G => a x) ha2
  have hmap : A.map (MulAut.conj t).toMonoidHom = B := by
    change A.map (MulAut.conj t⁻¹).toMonoidHom = B at hAB
    simpa only [hti] using hAB
  have hfixed : (MulAut.conj t).toMonoidHom.eqLocus (MonoidHom.id G) =
      centralizer ({t} : Set G) := by
    ext x
    change t * x * t⁻¹ = x ↔ x ∈ centralizer ({t} : Set G)
    rw [mul_inv_eq_iff_eq_mul, mem_centralizer_singleton_iff, eq_comm]
  have hVc : Nat.card (rankTwoSeed T M) = 4 := by
    simpa only [F.last, show (2 : ℕ) ^ 2 = 4 from rfl] using F.card 2 le_rfl
  have hCV : Nat.card (rankTwoSeed T M ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 := by
    rw [seed_centralizer_eq_point_of_movement F t htT htV]
    simpa using F.card 1 (by decide)
  have hc := elementary_pair_fixed_card_mul_of_fixed_square
    ((F.I₂ (sourceResidual M Mc)).pCoreIn 2) A B (rankTwoSeed T M)
    hgen hnA hnB hi (MulAut.conj t) ha hmap (by rw [hfixed, hCV, hVc]; decide)
  rw [hfixed, hVc, hAc, hCV] at hc
  omega

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
