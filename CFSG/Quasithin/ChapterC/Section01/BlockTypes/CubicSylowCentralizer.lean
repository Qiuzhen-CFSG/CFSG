module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.PGroupSelfCentralizingAction
public import Theory.GroupTheory.CharacteristicCentralizerFusion
/-!
# Cubic actors fixing a full Sylow subgroup of a short group

A short group has self-centralizing two-core and trivial three-core. Thus
an external three-group normalizing the group and fixing a full Sylow
two-subgroup fixes the entire group by coprime self-centralizing action.
The result retains arbitrary central covers.

Source: the cross-centralization step in Aschbacher–Smith 10.2.3(4), p.747.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- A three-group fixing a full Sylow two-subgroup of a short group fixes it all. -/
theorem IsShort.centralizes_of_cubic_sylow_fixed (K P A : Subgroup G) (hK : IsShort K)
    (hP : Chapter1.IsSylowIn 2 P K)
    (hA : IsPGroup 3 A) (hAK : A ≤ normalizer (K : Set G))
    (hAP : A ≤ centralizer (P : Set G)) : A ≤ centralizer (K : Set G) := by
  have hcore : pCore 3 K = ⊥ := by
    apply bot_unique
    have hle : pCore 3 K ≤ pCore 2 K :=
      (pCore_le_fitting K 3).trans ((fitting_le_generalizedFitting K).trans_eq hK.fitting)
    exact (le_inf hle le_rfl).trans (pCore_disjoint_of_ne 2 3 (by decide)).eq_bot.le
  have hself : centralizer (pCore 2 K : Set K) ≤ pCore 2 K := by
    rw [←hK.fitting]
    exact centralizer_generalizedFitting_le K
  obtain ⟨Q,hQ⟩ := hP
  have hQP : K.pCoreIn 2 ≤ P :=
    (map_mono (pCore_isPGroup.le_sylow_of_normal Q)).trans_eq hQ
  exact Subgroup.centralizes_of_pGroup_of_selfCentralizing_normal
    A K (pCore 2 K) hA hAK hcore hself (hAP.trans (centralizer_le hQP))

/-- The common normalizing two-group also moves the cubic actor inside the centralizer. -/
theorem IsShort.cubic_and_commutator_centralize (K P A S : Subgroup G) (hK : IsShort K)
    (hP : Chapter1.IsSylowIn 2 P K) (hA : Nat.card A = 3)
    (hAK : A ≤ normalizer (K : Set G)) (hAP : A ≤ centralizer (P : Set G))
    (hSK : S ≤ normalizer (K : Set G)) :
    A ≤ centralizer (K : Set G) ∧ ⁅S,A⁆ ≤ centralizer (K : Set G) := by
  have hp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hc := IsShort.centralizes_of_cubic_sylow_fixed K P A hK hP hp hAK hAP
  refine ⟨hc,?_⟩
  have hSC := hSK.trans (normalizer_le_normalizer_centralizer K)
  have hh := le_normalizer_iff_commutator_le_left.mp hSC
  exact (commutator_mono le_rfl hc).trans (by rwa [commutator_comm] at hh)
end CFSG.Quasithin.ChapterC
