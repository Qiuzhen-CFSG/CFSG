module
public import Stellmacher.Recognition.Parrott.ConcreteTits
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.OriginalSource

/-!
# Original Tits centralizer hypotheses in 14.2.22

Original 14.2.21 identifies the selected first parabolic H with the full
centralizer of the order-two Sylow omega-center. A generator of that same
omega-center therefore has the concrete Tits first parabolic as its full
centralizer. The model calculation supplies every clause of Parrott's
original centralizer hypotheses, retaining the original Sylow marking.

Global recognition still requires the independent N₂ premise used by the
available Parrott theorem. The first-parabolic marking is supplied by the
index-(5,3) amalgam recognition branch; neither premise is inferred here.

Source: Aschbacher--Smith 14.2.21--22, printed pp.988--989; Parrott (1972), p.672.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The selected Tits parabolic supplies Parrott's original hypotheses for
a generator of the prescribed Sylow omega-center. -/
theorem source_tits_parrott_hypotheses
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hmodel : Nonempty (Tits.ExceptionalParabolics.first ≃* H)) :
    ∃ z : G, zpowers z = centralInvolutions T ∧ Recognition.ParrottCentralizerHypotheses z := by
  let Z := centralInvolutions T
  have hZ := plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨_,_,hMc,_⟩ := plane_ordering_and_overgroups hG T hempty hM hu hmany hcard hZ
  have hHMc := (ReeLocal.source_ree_tits_rigidity hG T hempty hM hu hmany hcard e
    H hH (Or.inr hmodel)).1
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (hZ ▸ (by decide : 2 ∣ 2))
  have hzG : orderOf (z : G) = 2 := (orderOf_injective Z.subtype Z.subtype_injective z).trans hz
  have hzgen : zpowers (z : G) = Z := eq_of_le_of_card_ge (zpowers_le.mpr z.property) (by
    rw [Nat.card_zpowers,hzG]
    exact hZ.le)
  have hC : centralizer ({(z : G)} : Set G) = H := by
    calc
      _ = centralizer (zpowers (z : G) : Set G) := by
        rw [zpowers_eq_closure,centralizer_closure]
      _ = H := (congrArg (fun K : Subgroup G => centralizer (K : Set G)) hzgen).trans
        (hHMc.trans hMc).symm
  exact ⟨z,hzgen,Recognition.parrott_hypotheses_of_tits_centralizer (z : G) hzG
    (hmodel.some.trans (MulEquiv.subgroupCongr hC.symm))⟩

/-- The original Tits branch is recognized once the separate N₂ hypothesis
has been established; all concrete centralizer premises are discharged. -/
theorem source_tits_recognition_of_nTwo
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hmodel : Nonempty (Tits.ExceptionalParabolics.first ≃* H))
    (hN : IsNTwoGroup G) : Nonempty (G ≃* Tits.ParrottGroup) := by
  let : IsSimpleGroup G := hG.simple
  have hns : ¬ Group.IsSolvable G := fun hs =>
    hG.nonabelian (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr hs))
  obtain ⟨z,_,hz⟩ := source_tits_parrott_hypotheses hG T hempty hM hu hmany hcard e H hH hmodel
  exact Recognition.nonempty_equiv_tits_of_parrott hns hN hz

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
