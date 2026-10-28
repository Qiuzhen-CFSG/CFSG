module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.NumericalGeometry
public import CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry.Construction

/-!
# Sylow invariance of the original parabolic intersection

The point-plane stabilizer is the product of the plane centralizer and U.
Both normalize the literal intersection E=W∩Wᵍ: the first preserves W and
Wᵍ, while the second does so by the source commutator bound. Thus T
normalizes E. Passing through the defining central quotient gives invariance
of E-hat under the actual dotted Sylow image and terminal representation.

Source: Aschbacher--Smith 12.8.9 and 14.3.15, printed pp.852--853,994.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
open Symplectic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

theorem E_normalized_by_sylow (F : InvariantFlag T V 2) [IsElementaryAbelian 2 V]
    (g : G) (hg : g∈F.Gi 2) (hVE : V≤F.E g)
    (hcomm : ⁅F.U,F.U⁆≤F.Vi 1) (hindex : F.W.relIndex F.U=2) :
    (T:Subgroup G)≤normalizer (F.E g:Set G) := by
  let : IsElementaryAbelian 2 (F.Vi 2) := IsElementaryAbelian.of_injective
    (inclusion (F.le_seed 2)) (inclusion_injective _)
  obtain ⟨z,hz,hzp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hfactor := F.H2_eq_plane_centralizer_sup_U (by decide) z hzp hz
    (F.binary_point_commutator (by decide) hcomm hindex)
  have hC : centralizer (F.Vi 2:Set G)≤normalizer (F.W:Set G) := by
    have hCH : centralizer (F.Vi 2:Set G)≤F.H :=
      (centralizer_le (F.monotone (by decide : 1≤2))).trans (Subgroup.centralizer_le_normalizer _)
    exact (le_inf (hCH.trans (le_normalizer_conjugateSpanBy V F.H))
      (centralizer (F.Vi 2:Set G)).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hCE : centralizer (F.Vi 2:Set G)≤normalizer (F.E g:Set G) :=
    (le_inf hC (F.plane_centralizer_normalizes_actors g hg).1).trans
      inf_normalizer_le_normalizer_inf
  have hUE : F.U≤normalizer (F.E g:Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    exact ((commutator_mono le_rfl (show F.E g≤F.U from inf_le_left.trans inf_le_left)).trans
      hcomm).trans ((F.le_seed 1).trans hVE)
  exact (le_inf (F.invariant 1) (F.invariant 2)).trans
    (hfactor ▸ sup_le hCE hUE)

omit [Finite G] in
/-- Normalization of an actual subgroup descends through the defining central quotient. -/
theorem terminal_hatSpace_invariant (F : InvariantFlag T V 2)
    [IsElementaryAbelian 2 F.Uhat] (A D : Subgroup G)
    (hDA : D≤normalizer (A:Set G)) :
    ∀ t∈F.terminalDot D, ∀ v∈hatSpace F A,
      F.terminalRepresentation t v∈hatSpace F A := by
  rintro t ⟨a,ha,rfl⟩ v ⟨u,hu,rfl⟩
  refine ⟨F.uAction a u,?_,?_⟩
  · change (a:G)*(u:G)*(a:G)⁻¹∈A
    exact (mem_normalizer_iff.mp (hDA ha) (u:G)).mp hu
  · exact (F.uhatAction_apply_mk a u).symm
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag

namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
variable {T : Sylow 2 G} {L M : Subgroup G}

theorem rankTwo_terminal_intersection_invariant (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬IsMulCommutative F.U) (g : G) (hgP : g∈F.P L) (hgH : g∉F.H) :
    ∀ t∈F.terminalDot (T:Subgroup G), ∀ v∈hatSpace F (F.E g),
      F.terminalRepresentation t v∈hatSpace F (F.E g) := by
  have hnat : 3≤2 → Nonempty (AmbientNaturalMarking L h.L_normalizes_seed 2) := by omega
  obtain ⟨hcomm,hsquare⟩ := F.localKernel_commutator_squares h.simpleQTKE L M (by decide)
    h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat (h.flag_escape F)
  have hspan : F.U=conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hindex,_⟩ := F.binary_generation (by decide) L
    h.L_normalizes_seed (h.binarySeedAction_surjective F) h.centralizer
    hcomm hsquare hspan hne g hgP hgH
  apply F.terminal_hatSpace_invariant (F.E g) (T:Subgroup G)
  exact F.E_normalized_by_sylow g (F.P_le_G₂ (by decide) L h.L_normalizes_seed hgP)
    (F.seed_le_E_of_normalizes g (F.P_le_seed_normalizer L h.L_normalizes_seed hgP))
    hcomm hindex
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
