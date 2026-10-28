module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterAbovePoint.Full
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Normality
public import CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry.Construction

/-!
# Displaced-center geometry in the larger-center branch

The original rank-two center calculation cuts the displaced center in U,
and hence in W, at precisely the displaced point. The plane centralizer
normalizes that center, so its commutator with W lies in the same point.
The actual parabolic two-core and point-plane stabilizer factorization
also make its dotted image normal in the dotted Sylow subgroup.

Source: Aschbacher--Smith 12.8.10, 12.8.12(2), 14.3.15, pp.853--855,995.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
variable {T : Sylow 2 G} {L M : Subgroup G}

theorem rankTwo_conjugate_center_inf_U (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    conjugate F.ZU g ⊓ F.U = conjugate (F.Vi 1) g := by
  have hnat : 3 ≤ 2 → Nonempty (AmbientNaturalMarking L h.L_normalizes_seed 2) := by omega
  obtain ⟨hcomm,hsquare⟩ := F.localKernel_commutator_squares h.simpleQTKE L M (by decide)
    h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat (h.flag_escape F)
  have hspan : F.U = conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  obtain ⟨_,_,_,_,hIG,hIN,_⟩ := F.binary_generation (by decide) L h.L_normalizes_seed
    (h.binarySeedAction_surjective F) h.centralizer hcomm hsquare hspan hne g hgP hgH
  let B := F.localKernel_markedForm (by decide) d.two d.frattini_point hcomm
  have hc := F.binary_source_center_calculations (by decide) L h.L_normalizes_seed
    ((pResidual_eq_top_iff 2 L).mp h.L_residual) h.sylow_normalizes_L
    (h.binarySeedAction_surjective F) (fun hn => by omega) h.centralizer d.seed_center
    hcomm hsquare hspan hne g hgP hgH d.tilde_kernel B
  have hdis := (F.parabolic_displaced_centers (by decide) L h.L_normalizes_seed
    d.seed_center g hgP hgH).1
  have hzero := (F.rankTwo_centers L g (F.P_le_seed_normalizer L h.L_normalizes_seed hgP)
    (h.sylowOmega_eq_point F) (F.binary_U_le_sylow (by decide) hsquare)
    ((F.invariant 2).trans ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN))
    d.seed_center hdis hc.2.1).1
  have hk := hc.2.2.2.2.2
  calc
    _ = Chapter12.Section08.centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g :=
      hk.2.2.2.1.trans hk.2.2.2.2.1
    _ = _ := by rw [hzero,bot_sup_eq]

theorem rankTwo_conjugate_center_inf_W (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    conjugate F.ZU g ⊓ F.W = conjugate (F.Vi 1) g := by
  apply le_antisymm
  · exact (inf_le_inf le_rfl (show F.W ≤ F.U from inf_le_left)).trans
      (rankTwo_conjugate_center_inf_U h F d hne g hgP hgH).le
  · apply le_inf (map_mono (F.point_le_ZU (by decide)))
    have hp : conjugate (F.Vi 1) g ≤ F.Vi 2 := by
      rw [F.plane_eq_point_join_conjugate (by decide) L h.L_normalizes_seed g hgP hgH]
      exact le_sup_right
    exact hp.trans ((F.le_seed 2).trans F.seed_le_W)

theorem rankTwo_center_commutator_le_conjugate_point (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ⁅F.W,conjugate F.ZU g⁆ ≤ conjugate (F.Vi 1) g := by
  have hg := F.P_le_G₂ (by decide) L h.L_normalizes_seed hgP
  have hWZ : F.W ≤ normalizer (conjugate F.ZU g : Set G) :=
    (show F.W ≤ centralizer (F.Vi 2 : Set G) from inf_le_right).trans
      (F.plane_centralizer_normalizes_actors g hg).2
  have hZU : conjugate F.ZU g ≤ normalizer (F.U : Set G) :=
    (F.conjugate_ZU_le_X g).trans (F.X_normalizes_U g hg)
  apply (le_inf (le_normalizer_iff_commutator_le_right.mp hWZ)
    ((commutator_mono (show F.W ≤ F.U from inf_le_left) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hZU))).trans
    (rankTwo_conjugate_center_inf_U h F d hne g hgP hgH).le

theorem rankTwo_conjugate_center_normal_in_Tdot (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.terminalDot (conjugate F.ZU g) ≤ F.terminalDot (T : Subgroup G) ∧
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf
        (F.terminalDot (T : Subgroup G))).Normal := by
  let : IsElementaryAbelian 2 (F.Vi 2) := IsElementaryAbelian.of_injective
    (inclusion (F.le_seed 2)) (inclusion_injective _)
  have hnat : 3 ≤ 2 → Nonempty (AmbientNaturalMarking L h.L_normalizes_seed 2) := by omega
  obtain ⟨hcomm,hsquare⟩ := F.localKernel_commutator_squares h.simpleQTKE L M (by decide)
    h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat (h.flag_escape F)
  have hspan : F.U = conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  obtain ⟨e,_,hgen,_,hIG,hIN,_,_,hfactor,hPH,hcore,hindex,_⟩ :=
    F.binary_generation (by decide) L h.L_normalizes_seed
      (h.binarySeedAction_surjective F) h.centralizer hcomm hsquare hspan hne g hgP hgH
  have hcore' := F.binary_core_factorization L g hgP hfactor hPH hgen.symm e hcore hindex
  have hXT := F.X_le_T_of_parabolic_core L g hIG
    ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN) hcore'
  have hle : F.terminalDot (conjugate F.ZU g) ≤ F.terminalDot (T : Subgroup G) :=
    map_mono (comap_mono ((F.conjugate_ZU_le_X g).trans hXT))
  obtain ⟨z,hz,hzp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hn := actors_normal_in_dot_H2 F (by decide) z hzp hz
    (F.binary_point_commutator (by decide) hcomm hindex) g
    (F.P_le_G₂ (by decide) L h.L_normalizes_seed hgP)
    F.terminalHatAction F.terminalHatAction_apply_mk
  refine ⟨hle,(normal_subgroupOf_iff_le_normalizer hle).mpr ?_⟩
  have hT : (T : Subgroup G) ≤ F.H ⊓ F.Gi 2 := le_inf (F.invariant 1) (F.invariant 2)
  exact (map_mono (comap_mono hT)).trans
    ((normal_subgroupOf_iff_le_normalizer hn.2.2.1).mp hn.2.2.2)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
