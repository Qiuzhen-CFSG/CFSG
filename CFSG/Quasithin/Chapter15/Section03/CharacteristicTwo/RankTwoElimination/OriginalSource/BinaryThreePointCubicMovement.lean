module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeCrossCoreFour
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCubicConjugate

/-!
# The original point cubic moves the opposite component core

The conjugated point construction supplies an actual cubic v in Lᵍ outside L,
commuting with a residual cubic and fixing the chosen original involution.
Conjugating the self-centralizing cross-core image calculation proves that
v acts nontrivially on [O₂(L),L]. The resulting elementary nine and its points
remain in the caller's literal involution centralizer.

The original BinaryMS input, setup, CommonFacts and Earlier are reused. No
conjugated source setup, splitting, or original-core fixation is assumed.
The independent third cubic needed for a rank-three contradiction is not
constructed here.

Source: Aschbacher–Smith 15.3.23, printed pp.1128–1129, with the genuine
MS93 core-center decomposition used in the original point-cubic construction.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))

include hG hempty hM hu hmany hI htwo hf e b

/-- Cubics of the conjugated component cannot centralize the original core. -/
theorem binary_three_source_conjugate_cubic_moves_core
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S)
    (v : G) (hvL : v ∈ c.L.conjBy g) (hv : orderOf v = 3) :
    v ∉ centralizer (LinearThree.commutatorCore c.L : Set G) := by
  obtain ⟨x,hx,rfl⟩ := hvL
  have hx3 : orderOf x = 3 :=
    (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x).symm.trans hv
  have hmove := binary_three_source_cubic_moves_conjugate_core
    hG d hempty hM hu hmany hI htwo hf c e b g⁻¹ (inv_mem hgT)
    (fun hh => hgS (inv_mem_iff.mp hh))
    (⟨x,mem_sup_left hx⟩ : (c.L ⊔ d.S : Subgroup G)) hx3
  intro hc
  apply hmove
  have hback := map_centralizer_le_centralizer_image
    (LinearThree.commutatorCore c.L : Set G) (MulAut.conj g⁻¹).toMonoidHom
    (mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hc)
  change (MulAut.conj g⁻¹) ((MulAut.conj g) x) ∈
    centralizer ((LinearThree.commutatorCore c.L).conjBy g⁻¹ : Set G) at hback
  simpa only [MulAut.conj_apply,mul_assoc,inv_mul_cancel_left,inv_mul_cancel_right,
    inv_inv,inv_mul_cancel,mul_one] using hback

/-- The actual outside point cubic moves the original commutator core while
remaining in the same elementary nine and the same point centralizer. -/
theorem binary_three_source_intrinsic_point_moving_cubic
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (z : G) (hz : z ∈ intrinsicFour c.L)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ a v : G, ∃ E : Subgroup G,
      a ∈ YL d c.L ∧ v ∈ c.L.conjBy g ∧
      orderOf a = 3 ∧ orderOf v = 3 ∧
      a ∈ centralizer ({z} : Set G) ∧ v ∈ centralizer ({z} : Set G) ∧
      a * v = v * a ∧ v ∉ c.L ∧
      E ≤ centralizer ({z} : Set G) ∧ a ∈ E ∧ v ∈ E ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
      v ∉ centralizer (LinearThree.commutatorCore c.L : Set G) := by
  obtain ⟨a,v,E,haY,hvL,ha,hv,haz,hvz,hav,hvout,hEC,haE,hvE,hE,hcard⟩ :=
    binary_three_source_intrinsic_point_outside_cubic
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz g hgT hgS
  exact ⟨a,v,E,haY,hvL,ha,hv,haz,hvz,hav,hvout,hEC,haE,hvE,hE,hcard,
    binary_three_source_conjugate_cubic_moves_core
      hG d hempty hM hu hmany hI htwo hf c e b g hgT hgS v hvL hv⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
