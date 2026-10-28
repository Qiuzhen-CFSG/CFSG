module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.Selection

/-!
# The moving residual selected in the star quotient

Start with the source noncentral action of O₂(L₊*) on an odd prime core
of H/O₂(H). The proved selection constructs the characteristic rank-two
subgroup D and preserves that action. Its actual residual preimage is
normal and two-perfect, and its intrinsic two-core quotient is D. The
rank-one centralizing-residual bound from 13.3.14(b) forces it to move U.

Source: Aschbacher–Smith, Lemma 13.3.14(d), printed p.892. This is an
application to the literal star projection and O²-preimage, not a supplied
quotient model or a supplied moving subgroup.
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_moving_star_residual
    (H Lplus U : Subgroup G) (hLH : Lplus ≤ H) (hL : IsPPerfect 2 Lplus)
    (hp : Odd p) (hr : primeRank p (Star H) ≤ 2)
    (hm : ¬ (star H Lplus hLH).pCoreIn 2 ≤ centralizer (pCore p (Star H) : Set (Star H)))
    (hY : primeRank p (centralizingResidual U) ≤ 1) :
    ∃ (D : Subgroup (Star H)) (hD : D.Characteristic),
      letI : D.Characteristic := hD
      D ≤ pCore p (Star H) ∧ primeRank p D = 2 ∧ Chapter1.XiOddQuotient p D ∧
      (pCore 2 Lplus).map
        ((MulAut.conjNormal : Star H →* MulAut D).comp (starMap H Lplus hLH)) ≠ ⊥ ∧
      (starResidual H D).Normal ∧ IsPPerfect 2 (starResidual H D) ∧
      Nonempty ((starResidual H D ⧸ pCore 2 (starResidual H D)) ≃* D) ∧
      ⁅U, (starResidual H D).map H.subtype⁆ ≠ ⊥ := by
  have hr' := (primeRank_subgroup_le p (pCore p (Star H))).trans hr
  obtain ⟨X, hX, hchar, hle, hrD, hmodel, hmove⟩ :=
    exists_star_supercritical H Lplus hLH hL hp hr'
      (original_core_moves_of_star_core_moves H Lplus hLH hm)
  let : X.Characteristic := hX.characteristic
  let D := X.map (pCore p (Star H)).subtype
  let : D.Characteristic := hchar
  have hrl : 1 < primeRank p D := by rw [show primeRank p D = 2 from hrD]; decide
  exact ⟨D, hchar, hle, hrD, hmodel, hmove, starResidual_normal H D,
    starResidual_isPPerfect H D, ⟨oddStarResidualCoreEquiv H D hp hmodel.isPGroup⟩,
    starResidual_moves_of_rank H U D hp hmodel.isPGroup hrl hY⟩

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
