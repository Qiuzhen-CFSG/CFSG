module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.Rank
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import Theory.GroupTheory.PerfectCentralCoverAbelianSylow
public import Theory.GroupTheory.GeneralizedFitting.ComponentPrimeRankNormal

/-!
# Centerless odd-rank-one nonnormal ordinary components

The complete A.3.6 covering catalogue gives center order one or three.
The commuting-conjugate rank obstruction forces three-rank at most one.
Its cyclic Sylow three-subgroup is abelian, so perfect central transfer kills
the possible central three-subgroup. Distinct conjugates of the resulting
centerless component have additive odd ranks, hence every odd rank is at
most one. This is the source reduction for A.3.8(3), pp.45–46, with the
literal central quotient retained throughout.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource.FourModels
open Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]

/-- In a quasisimple group the common A.3.6 alternative is the central one. -/
theorem center_card_of_common {B : Type*} [Group B] [Finite B] [IsQuasisimple B]
    (h : A36Common B) : Nat.card (center B) = 1 ∨ Nat.card (center B) = 3 := by
  have hF : fittingSubgroup B = center B := le_antisymm
    ((le_solvableRadical _ inferInstance inferInstance).trans
      IsQuasisimple.solvableRadical_le_center) (le_sSup ⟨inferInstance, inferInstance⟩)
  have hR : solvableRadical B = center B := le_antisymm
    IsQuasisimple.solvableRadical_le_center
    (le_solvableRadical _ inferInstance inferInstance)
  rcases h.2.2.1 with hh | hh
  · have he := hh.2.2
    rw [hF, hR, relIndex_self] at he
    omega
  · simpa only [hF] using hh.2.2

/-- Perfect central transfer removes the only possible odd scalar kernel. -/
theorem center_eq_bot_of_model (hG : primeRank 3 G ≤ 2) (hcore : pCore 2 G = ⊥)
    (B : Subgroup G) (hB : IsComponent G B) (hn : ¬ B.Normal)
    (hmodel : LocalModels.TheoremCModel (B ⧸ center B)) : center B = ⊥ := by
  let : IsQuasisimple B := hB.2
  have hc := center_card_of_common (OrdinarySource.ordinary_conclusion_of_model hcore B hB hmodel).2
  have hle : Nat.card (center B) ≤ 3 := by rcases hc with hc | hc <;> omega
  have hr := (nonnormal_component_three_rank hG hB hle hn).1
  let P : Sylow 3 B := default
  let := P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  have hnot := PerfectCentralCovering.not_dvd_card_kernel_of_abelian_sylow
    (QuotientGroup.mk' (center B)) (by rw [QuotientGroup.ker_mk']) P inferInstance
  rw [QuotientGroup.ker_mk'] at hnot
  rcases hc with hc | hc
  · exact (eq_bot_iff_card _).mpr hc
  · exact (hnot (hc ▸ dvd_rfl)).elim

/-- Nonnormality forces rank at most one at every odd prime in the actual component. -/
theorem odd_ranks_of_model (hG : IsStronglyQuasithin G) (hcore : pCore 2 G = ⊥)
    (B : Subgroup G) (hB : IsComponent G B) (hn : ¬ B.Normal)
    (hmodel : LocalModels.TheoremCModel (B ⧸ center B)) :
    ∀ p : ℕ, p.Prime → Odd p → primeRank p B ≤ 1 := by
  have hz := center_eq_bot_of_model (hG 3 (by decide) (by decide)) hcore B hB hn hmodel
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  by_contra! hr
  have hu := hG p hp ho
  exact hn (hB.normal_of_centerless_of_primeRank hz p (by omega))

/-- The original ordinary component is simple; this derives simplicity rather
than replacing the perfect central cover by its quotient model. -/
theorem simple_of_model (hG : primeRank 3 G ≤ 2) (hcore : pCore 2 G = ⊥)
    (B : Subgroup G) (hB : IsComponent G B) (hn : ¬ B.Normal)
    (hmodel : LocalModels.TheoremCModel (B ⧸ center B)) : IsSimpleGroup B := by
  let : IsQuasisimple B := hB.2
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  have hz := center_eq_bot_of_model hG hcore B hB hn hmodel
  let e : B ≃* B ⧸ center B := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hz.symm)
  exact e.isSimpleGroup

end CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource.FourModels
