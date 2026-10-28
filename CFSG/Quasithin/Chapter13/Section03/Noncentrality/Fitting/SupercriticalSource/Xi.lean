module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.Transport
public import CFSG.Quasithin.Chapter1.Section03.Terminal.Definitions

/-!
# Actual Ξ-f membership of the selected residual

The original ambient Sylow contains the two-core of H, so the selected
residual joined with that Sylow remains a two-local subgroup. The actual
quaternion subgroup proves irreducibility on the intrinsic Frattini quotient.
Together with A.4.8 this supplies the literal Ξ-f member in 13.3.14(d).
-/

public section

open Subgroup

namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem star_residual_mem_Xi
    (T : Sylow 2 G) (H Lplus : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hLH : Lplus ≤ H) (hcore : pCore 2 H ≠ ⊥)
    (D : Subgroup (Star H)) [D.Normal]
    (hp : Odd p) (hD : Chapter1.XiOddQuotient p D)
    (hQ : Nonempty ((((T : Subgroup G).subgroupOf Lplus).map
      ((MulAut.conjNormal : Star H →* MulAut D).comp (starMap H Lplus hLH))) ≃*
        QuaternionGroup 2)) :
    (starResidual H D).map H.subtype ∈ Chapter1.Xi G (T : Subgroup G) := by
  let P := starResidual H D
  let S := (T : Subgroup G).subgroupOf H
  let : P.Normal := starResidual_normal H D
  have hn : S ≤ normalizer (P : Set H) := le_normalizer_of_normal
  have hXi : P ∈ Chapter1.Xi H S := by
    refine ⟨starResidual_isPPerfect H D, hn, ?_, ?_, ?_⟩
    · have hcoreS : pCore 2 H ≤ S :=
        pCore_isPGroup.le_sylow_of_normal (T.subtype hTH)
      have hle : pCore 2 H ≤ (P ⊔ S).pCoreIn 2 :=
        le_pCoreIn_of_normalizes pCore_isPGroup (hcoreS.trans le_sup_right)
          le_normalizer_of_normal
      intro hz
      exact hcore (le_bot_iff.mp (hle.trans hz.le))
    · exact ⟨p, Fact.out, hp, hD.of_mulEquiv (oddStarResidualCoreEquiv H D hp hD.isPGroup).symm⟩
    · exact residual_frattini_irreducible (T : Subgroup G) H Lplus hLH D hp hD hQ hn
  have hm := (Chapter1.mem_Xi_map_iff H.subtype H.subtype_injective).mpr hXi
  simpa only [S, map_subgroupOf_eq_of_le hTH] using hm

theorem source_selected_XiF
    (T : Sylow 2 G) (H Lplus U : Subgroup G)
    (hH : H ∈ Chapter1.He G) (hTH : (T : Subgroup G) ≤ H) (hLH : Lplus ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (Lplus : Set G))
    (hL : IsPPerfect 2 Lplus) (hL3 : Nat.card (Lplus ⧸ pCore 2 Lplus) = 3)
    (hp : Odd p) (hr : primeRank p (Star H) ≤ 2)
    (hm : ¬ (star H Lplus hLH).pCoreIn 2 ≤ centralizer (pCore p (Star H) : Set (Star H)))
    (hU : U ≤ Stellmacher.omegaOneCenterAmbient (H.pCoreIn 2))
    (hY : primeRank p (centralizingResidual U) ≤ 1) :
    ∃ (D : Subgroup (Star H)) (hD : D.Characteristic),
      letI : D.Characteristic := hD
      let a := (MulAut.conjNormal : Star H →* MulAut D).comp (starMap H Lplus hLH)
      D ≤ pCore p (Star H) ∧ primeRank p D = 2 ∧ Chapter1.XiOddQuotient p D ∧
      (pCore 2 Lplus).map a ≠ ⊥ ∧
      Nonempty (a.range ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
      Nonempty ((((T : Subgroup G).subgroupOf Lplus).map a) ≃* QuaternionGroup 2) ∧
      ⁅U, (starResidual H D).map H.subtype⁆ ≠ ⊥ ∧
      (starResidual H D).map H.subtype ∈ Chapter1.XiF G (T : Subgroup G) := by
  obtain ⟨D, hD, hle, hrD, hmodel, hmove, hfull, hsyl, hmoved, hfaith⟩ :=
    source_selected_actors T H Lplus U hH hLH hTL hL hL3 hp hr hm hU hY
  let : D.Characteristic := hD
  have hc : pCore 2 H ≠ ⊥ := by
    intro hz
    have hUle : U ≤ H.pCoreIn 2 := fun u hu =>
      ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp (hU hu)).1
    have he : U = ⊥ := by
      apply le_bot_iff.mp
      simpa only [pCoreIn, hz, Subgroup.map_bot] using hUle
    exact hmoved (by rw [he, commutator_bot_left])
  exact ⟨D, hD, hle, hrD, hmodel, hmove, hfull, hsyl, hmoved,
    star_residual_mem_Xi T H Lplus hTH hLH hc D hp hmodel hsyl, hfaith⟩

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
