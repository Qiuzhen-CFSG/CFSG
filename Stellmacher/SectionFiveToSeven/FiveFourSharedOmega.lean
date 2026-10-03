module

public import Stellmacher.SectionFiveToSeven.Result5_4
public import Stellmacher.ElementaryAbelianMaxJFixedCenter

/-!
# The shared subgroup's central involutions in the local join core

Under the exact hypotheses of Stellmacher (5.4), the central involutions
of the shared subgroup `T` lie in `O₂(H₀)`, where `H₀ = F₁ ⊔ F₂`.
This supplies the omega-center hypothesis for (3.9) when its common Sylow
is the Baumann subgroup, as in (6.1) and (6.3).

Write `Z = Ω₁(Z(T))`. Since `J(S) ≤ B(S) ≤ T`, the elementary subgroup
`Z ≤ T ≤ S` centralizes `J(S)`. Maximal-order elementary subgroup theory
therefore puts `Z` in `Ω₁(Z(J(S)))`, hence in `J(S)`. The general
normalizer-core argument extracted from (5.4) applies, because `T`
centralizes `Z`.

Source: `refs/latex/stellmacher-n-group.tex`, proof of (5.4), journal page 30,
and its applications with shared subgroup `B` in (6.1) and (6.3), page 31.
The original public statement of (5.4) remains unchanged; this module proves
the stronger consequence needed by those applications.
-/

namespace Stellmacher.SectionsFiveToSeven

universe u
variable {H : Type u} [Group H] [Finite H]

/-- The central involutions of the shared subgroup lie in the join core. -/
public theorem omegaOneCenter_shared_subgroup_le_join_core
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (T F1 F2 H0 M : Subgroup H)
    (hT : baumannIn S ≤ T ∧ T ≤ S)
    (hF1 : F1 ∈ PFamily (⊤ : Subgroup H) T)
    (hF2 : F2 ∈ PFamily (⊤ : Subgroup H) T)
    (hH0 : H0 = F1 ⊔ F2)
    (hM : IsMaximalTwoLocalContaining (S0 : Subgroup H) M)
    (hcore : twoCoreIn H0 ≠ ⊥)
    (halt : S = (S0 : Subgroup H) ∨ ¬ H0 ≤ M) :
    omegaOneCenter T ≤ twoCoreIn H0 := by
  let Z := omegaOneCenter T
  let _ : IsElementaryAbelian 2 Z := omegaOneCenterAmbient_elementaryAbelian T
  have hZT : Z ≤ T := fun z hz => (mem_omegaOneCenterAmbient_iff T z).mp hz |>.1
  have hTZ : T ≤ Subgroup.centralizer (Z : Set H) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff T z).mp hz).2.2 t ht |>.symm
  have hJS : elementaryAbelianMaxJ S ≤ S := sSup_le fun _ hA => hA.1
  have hJB : elementaryAbelianMaxJ S ≤ baumannIn S := by
    refine le_inf hJS ?_
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff (elementaryAbelianMaxJ S) z).mp hz).2.2 j hj |>.symm
  have hJT : elementaryAbelianMaxJ S ≤ T := hJB.trans hT.1
  have hZJ : Z ≤ elementaryAbelianMaxJ S := by
    have hZomega := elementary_centralizer_maxJ_le_omegaCenter S Z
      (hZT.trans hT.2)
      ((Subgroup.le_centralizer_iff.mp hTZ).trans (Subgroup.centralizer_le hJT))
    exact fun z hz => (mem_omegaOneCenterAmbient_iff _ z).mp (hZomega hz) |>.1
  exact elementary_thompson_centralizer_le_join_core
    S0 S P1 P2 h T F1 F2 H0 M hT hF1 hF2 hH0 hM hcore halt Z hZJ hTZ

end Stellmacher.SectionsFiveToSeven
