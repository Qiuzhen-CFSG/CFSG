module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalNormalization
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicKernelTransport
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ElementaryKernelModel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneComparison
import all CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicAttachmentMovement

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.WholeCoreMovement
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalAlignment

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaGeneration

/-!
# Full critical kernels on overlapping original distance-four paths

For the original paths d--a--c and a--c--z, the full kernels
Z_d intersect Q_c and Z_z intersect Q_a normalize one another. Their
commutator is unchanged when either full seed is replaced by its moving
subgroup, so both possible central attachments are retained.

The full reverse omega kernel also normalizes the shifted kernel. The
noncentral omega-extension calculation consequently proves the inequality
from MS93 (5.12)(1) with the left actor strengthened from the restricted
seed to full X, for U_d intersect Q_c under the small critical image
assumption. The alternative is central generation of full omega.
For the full shifted kernel, normalization by X_z is equivalent to
normalization by Z_z. If it fails, central generation and X=Z follow at
every component vertex; the displacement is an order-two subgroup of
both full moving covers, aligned with the critical line modulo the whole
central attachment and noncentral at z. A small image on the overlapping
path also gives noncentrality at d and trivial intersections with both
endpoint centers. The full-radius bound places the critical line in the
midpoint omega subgroup. Central generation and transport of the full
central attachment then place the failure line in the midpoint seed.

Radius escape supplies an actual backward overlap for every small critical
path. OriginalSylowExceptional applies these comparisons to the literal
c.L,d.S source. The original graph, projection kernel E and odd E/Q are
unchanged. The central-generation branch, large critical images and the
terminal distance-four contradiction still require their source arguments;
this module does not assert CoreExhaustion or block reconstruction.

The internal imports reuse the full-cover calculations while preserving
their existing public boundaries. The local versions of the restricted
kernel estimates use distance greater than two, so they apply at four
without changing the older terminal APIs.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), (5.2)(iii), (5.12)(1), printed pp.866--867,914,924--925;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h e hz hk in
/-- Failure of endpoint normalization makes the restricted kernel displacement
an order-two subgroup of the same restricted seed. -/
private theorem restricted_kernel_line
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (Y : Subgroup (FreeAmalgam Rg)) [IsElementaryAbelian 2 Y]
    (hYV : Y ≤ V Rg a)
    (htrap : Y ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hYN : Z Rg z ⊓ Q Rg a ≤ normalizer (Y : Set (FreeAmalgam Rg)))
    (hnorm : ¬ Z Rg z ≤ normalizer
      ((Y ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg))) :
    Nat.card (⁅Y,Z Rg z ⊓ Q Rg a⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      ⁅Y,Z Rg z ⊓ Q Rg a⁆ ≤ Y := by
  let F := Z Rg z ⊓ Q Rg a
  let K := ⁅Y,F⁆
  have hb2 := distance_gt_two h e hz hk
  have hYQ : Y ≤ Q Rg a := hYV.trans ((sourceGeometry h).V_le_Q hb2 a p.start_color)
  have hYG : Y ≤ stabilizer Rg z := htrap.trans (terminal_last_edge_inputs h p hb2).2.2
  have hKG : K ≤ Y := le_normalizer_iff_commutator_le_left.mp hYN
  have hcrit : ⁅Z Rg a,Z Rg z⁆ ≤ Z Rg a := critical_seed_commutator_le h p
  have contradiction_of_control (hcontrol : ⁅Y,Z Rg z⁆ ≤ Z Rg a ⊔ K) : False := by
    apply hnorm
    have hZnorm : Z Rg z ≤ normalizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      le_normalizer_iff_commutator_le_left.mpr hcrit
    apply le_normalizer_iff.mpr
    intro x hx v hv
    have hm : (Y ⊔ Z Rg a).map (MulAut.conj x).toMonoidHom ≤ Y ⊔ Z Rg a := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ((mem_normalizer_iff_map_conj_eq.mp (hZnorm hx)).le.trans le_sup_right)
      rintro _ ⟨y,hy,rfl⟩
      have hh := (Y ⊔ Z Rg a).mul_mem
        ((hcontrol.trans (sup_le le_sup_right (hKG.trans le_sup_left)))
          (by rw [commutator_comm]; exact commutator_mem_commutator hx hy))
        (mem_sup_left hy)
      simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
    exact hm (mem_map_of_mem (MulAut.conj x).toMonoidHom hv)
  have hbound : Nat.card K ≤ 2 := by
    rcases borel_elementary_reverse_kernel_control_or_card h e hz hk u hR p hp Y htrap hYQ with hc | hc
    · change ⁅Y,Z Rg z⁆ ≤ Z Rg a ⊔ ⁅F,Y⁆ at hc
      rw [commutator_comm F Y] at hc
      exact (contradiction_of_control hc).elim
    · change Nat.card (⁅Y,F⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2
      rw [commutator_comm]
      exact hc
  have hne : K ≠ ⊥ := by
    intro hzero
    have hc := small_critical_kernel_commutator h e hz hk p hp Y hYG
      (commutator_eq_bot_iff_le_centralizer.mp hzero)
    exact contradiction_of_control (hc.trans (hcrit.trans le_sup_left))
  let := finite_stabilizer Rg a
  let : Finite Y := Finite.of_injective
    (inclusion (hYV.trans ((sourceGeometry h).V_local a p.start_color (by
      rw [(sourceGeometry h).distance_constant a p.start_color]; exact hb2)))) (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion hKG) (inclusion_injective _)
  have hpos : 1 < Nat.card K := (one_lt_card_iff_ne_bot K).mpr hne
  exact ⟨by change Nat.card K = 2; omega,hKG⟩

include h e hz hk in
/-- The full restricted commutator in the nonnormalizing alternative lies
in the reverse critical line plus the entire endpoint central attachment. -/
private theorem restricted_kernel_alignment
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (Y : Subgroup (FreeAmalgam Rg)) [IsElementaryAbelian 2 Y]
    (hYV : Y ≤ V Rg a)
    (htrap : Y ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hYN : Z Rg z ⊓ Q Rg a ≤ normalizer (Y : Set (FreeAmalgam Rg)))
    (hnorm : ¬ Z Rg z ≤ normalizer
      ((Y ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg))) :
    ⁅Y,Z Rg z ⊓ Q Rg a⁆ ≤ ⁅Z Rg a,Z Rg z⁆ ⊔
      (U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) := by
  have hb2 := distance_gt_two h e hz hk
  let F := Z Rg z ⊓ Q Rg a
  let P := Y ⊔ Z Rg a
  let H := ⁅Y,F⁆
  have hYQ : Y ≤ Q Rg a := hYV.trans ((sourceGeometry h).V_le_Q hb2 a p.start_color)
  have hAC : Z Rg a ≤ centralizer (Y : Set (FreeAmalgam Rg)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color)).trans
      (centralizer_le hYQ)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.sup_of_le_centralizer hAC
  have hYG : Y ≤ stabilizer Rg z := htrap.trans (terminal_last_edge_inputs h p hb2).2.2
  let pr : CriticalPath Rg (sourceGeometry h) z a :=
    CriticalPath.ofPair p.end_color (reverse_pair h e p)
  have hAG : Z Rg a ≤ stabilizer Rg z :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) z p.end_color
      (by rw [(sourceGeometry h).distance_constant _ p.end_color]; exact sourceDistance_pos h)
      pr.critical
  have hPG : P ≤ stabilizer Rg z := sup_le hYG hAG
  have hAF : Z Rg a ≤ centralizer (F : Set (FreeAmalgam Rg)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color)).trans
      (centralizer_le inf_le_right)
  have hPF : ⁅P,F⁆ = H := commutator_sup_fixed Y (Z Rg a) F
    (hAC.trans (Subgroup.centralizer_le_normalizer _)) hAF
  have hfixed : ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),P⁆ = H := by
    have hAF' : Z Rg a ≤ centralizer
        (U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) : Set _) :=
      le_centralizer_iff.mpr inf_le_right
    rw [commutator_comm,commutator_sup_fixed Y (Z Rg a) _
      (hAC.trans (Subgroup.centralizer_le_normalizer _)) hAF',commutator_comm]
    rw [←critical_moving_kernel_eq_fixed h e p]
    rw [←(critical_kernel_predecessor_moving h e hz hb2 p).2.2 Y htrap,commutator_comm]
  have hs : (Q Rg a).relIndex (Z Rg z) < 4 := by
    rw [(small_critical_indices h e hz hk p hp).2]
    decide
  have hD : ⁅U Rg z,Z Rg a⁆ = ⁅Z Rg a,Z Rg z⁆ := by
    rw [small_critical_moving_commutator_eq h e hz hk pr hs,commutator_comm]
  have hHY : H ≤ Y := le_normalizer_iff_commutator_le_left.mp hYN
  have hcrit := critical_seed_commutator_le h p
  have hfail : ¬ ⁅U Rg z,P⁆ ≤ H ⊔ ⁅Z Rg a,Z Rg z⁆ := by
    intro hh
    apply hnorm
    have hYmove : ⁅Y,Z Rg z⁆ ≤ H ⊔ ⁅Z Rg a,Z Rg z⁆ := by
      rw [commutator_comm,critical_predecessor_seed_movement h e hz hb2 p Y htrap]
      exact (commutator_mono le_rfl le_sup_left).trans hh
    have hZnorm : Z Rg z ≤ normalizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      le_normalizer_iff_commutator_le_left.mpr hcrit
    apply le_normalizer_iff.mpr
    intro x hx v hv
    have hm : (Y ⊔ Z Rg a).map (MulAut.conj x).toMonoidHom ≤ Y ⊔ Z Rg a := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ((mem_normalizer_iff_map_conj_eq.mp (hZnorm hx)).le.trans le_sup_right)
      rintro _ ⟨y,hy,rfl⟩
      have hh := (Y ⊔ Z Rg a).mul_mem
        ((hYmove.trans (sup_le (hHY.trans le_sup_left) (hcrit.trans le_sup_right)))
          (by rw [commutator_comm]; exact commutator_mem_commutator hx hy))
        (mem_sup_left hy)
      simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
    exact hm (mem_map_of_mem (MulAut.conj x).toMonoidHom hv)
  let := h.relative_normal
  obtain ⟨i,hi,hir,hiQ,hiE,hiU,_⟩ := graph_cover h e hz hk z p.end_color
  let A := (Z Rg a).comap i
  let P₀ := P.comap i
  let : IsElementaryAbelian 2 P₀ := IsElementaryAbelian.comap_of_injective i hi P
  have hmA : A.map i = Z Rg a := map_comap_eq_self (hAG.trans_eq hir.symm)
  have hmP : P₀.map i = P := map_comap_eq_self (hPG.trans_eq hir.symm)
  have hnA : ¬ A ≤ extensionKernel h :=
    critical_comap_not_le_extension h e hz pr i hi (hAG.trans_eq hir.symm) hiQ
  have hidx : (centralizer (A : Set M)).relIndex W₀ ≤ 2 := by
    rw [←inf_relIndex_right,inf_comm,←relIndex_map_map_of_injective _ _ hi,
      ←map_inf_centralizer_of_injective i hi,hiU,hmA,inf_relIndex_left]
    let := finite_Z Rg z
    let : Finite (U Rg z) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z Rg z)) (inclusion_injective _)
    have hQC : Q Rg a ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk p hp).2
  have hmH : (⁅W₀ ⊓ centralizer (A : Set M),P₀⁆).map i = H := by
    rw [map_commutator,←map_inf_centralizer_of_injective i hi,hiU,hmA,hmP,hfixed]
  have hmD : (⁅W₀,A⁆).map i = ⁅Z Rg a,Z Rg z⁆ := by
    rw [map_commutator,hiU,hmA,hD]
  have hmC : (W₀ ⊓ center M).map i =
      U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
    have hh := map_inf_centralizer_of_injective i hi W₀ ⊤
    simpa only [←MonoidHom.range_eq_map,hir,hiU,coe_top,centralizer_univ] using hh.symm
  have hh := terminal_cover_kernel_small_aligned h e hz hk A P₀
    (comap_mono (show Z Rg a ≤ P from le_sup_right)) inferInstance hnA hidx (by
      intro hh
      apply hfail
      have hm := map_mono (f := i) hh
      rwa [Subgroup.map_sup,hmH,hmD,map_commutator,hiU,hmP] at hm)
  have hm := map_mono (f := i) hh.2
  rwa [hmH,Subgroup.map_sup,hmD,hmC] at hm


include h e hz hk in
/-- A nonzero restricted critical-kernel displacement cannot be central
at the endpoint. This uses the full cubic cover, including its attachment. -/
private theorem restricted_kernel_noncentral
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (Y : Subgroup (FreeAmalgam Rg)) [IsElementaryAbelian 2 Y]
    (hYV : Y ≤ V Rg a)
    (htrap : Y ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hne : ⁅Y,Z Rg z ⊓ Q Rg a⁆ ≠ ⊥) :
    ¬ ⁅Y,Z Rg z ⊓ Q Rg a⁆ ≤
      centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
  intro hcentral
  have hb2 := distance_gt_two h e hz hk
  let F := Z Rg z ⊓ Q Rg a
  let P := Y ⊔ Z Rg a
  let H := ⁅Y,F⁆
  have hYQ : Y ≤ Q Rg a := hYV.trans ((sourceGeometry h).V_le_Q hb2 a p.start_color)
  have hAC : Z Rg a ≤ centralizer (Y : Set (FreeAmalgam Rg)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color)).trans
      (centralizer_le hYQ)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.sup_of_le_centralizer hAC
  have hYG : Y ≤ stabilizer Rg z := htrap.trans (terminal_last_edge_inputs h p hb2).2.2
  let pr : CriticalPath Rg (sourceGeometry h) z a :=
    CriticalPath.ofPair p.end_color (reverse_pair h e p)
  have hAG : Z Rg a ≤ stabilizer Rg z :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) z p.end_color
      (by rw [(sourceGeometry h).distance_constant _ p.end_color]; exact sourceDistance_pos h)
      pr.critical
  have hPG : P ≤ stabilizer Rg z := sup_le hYG hAG
  have hAF : Z Rg a ≤ centralizer (F : Set (FreeAmalgam Rg)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color)).trans
      (centralizer_le inf_le_right)
  have hPF : ⁅P,F⁆ = H := commutator_sup_fixed Y (Z Rg a) F
    (hAC.trans (Subgroup.centralizer_le_normalizer _)) hAF
  have hfixed : ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),P⁆ = H := by
    have hAF' : Z Rg a ≤ centralizer
        (U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) : Set _) :=
      le_centralizer_iff.mpr inf_le_right
    rw [commutator_comm,commutator_sup_fixed Y (Z Rg a) _
      (hAC.trans (Subgroup.centralizer_le_normalizer _)) hAF',commutator_comm]
    rw [←critical_moving_kernel_eq_fixed h e p]
    rw [←(critical_kernel_predecessor_moving h e hz hb2 p).2.2 Y htrap,commutator_comm]
  let := h.relative_normal
  obtain ⟨i,hi,hir,hiQ,hiE,hiU,_⟩ := graph_cover h e hz hk z p.end_color
  let A := (Z Rg a).comap i
  let P₀ := P.comap i
  let : IsElementaryAbelian 2 P₀ := IsElementaryAbelian.comap_of_injective i hi P
  have hmA : A.map i = Z Rg a := map_comap_eq_self (hAG.trans_eq hir.symm)
  have hmP : P₀.map i = P := map_comap_eq_self (hPG.trans_eq hir.symm)
  have hnA : ¬ A ≤ pCore 2 M := by
    intro hh
    have he := map_mono (f := i) hh
    rw [hmA,hiQ] at he
    exact p.critical.2 he
  have hidx : (centralizer (A : Set M)).relIndex W₀ ≤ 2 := by
    rw [←inf_relIndex_right,inf_comm,←relIndex_map_map_of_injective _ _ hi,
      ←map_inf_centralizer_of_injective i hi,hiU,hmA,inf_relIndex_left]
    let := finite_Z Rg z
    let : Finite (U Rg z) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z Rg z)) (inclusion_injective _)
    have hQC : Q Rg a ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk p hp).2
  have hmH : (⁅W₀ ⊓ centralizer (A : Set M),P₀⁆).map i = H := by
    rw [map_commutator,←map_inf_centralizer_of_injective i hi,hiU,hmA,hmP,hfixed]
  have hcF : ⁅W₀ ⊓ centralizer (A : Set M),P₀⁆ ≤ center M := by
    intro x hx
    apply mem_center_iff.mpr
    intro m
    apply hi
    simp only [map_mul]
    apply hcentral
    · have hh := mem_map_of_mem i hx
      rwa [hmH] at hh
    · rw [←hir]
      exact ⟨m,rfl⟩
  have hzero := congrArg (Subgroup.map i)
    (cover_fixed_central_commutator_eq_bot h e hz hk A P₀
      (comap_mono (show Z Rg a ≤ P from le_sup_right))
      (((sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color).isPGroup.comap_of_injective i hi)
      hnA hidx hcF)
  rw [hmH,Subgroup.map_bot] at hzero
  exact hne hzero



include h e hz hk in
/-- Overlapping four-edge paths give mutual normalization of their full
critical kernels. Removing either central edge attachment does not change
their commutator. -/
theorem four_overlapping_kernel_pair
    (hb : sourceDistance h = 4)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a) :
    let c := p.walk.getVert 2
    let K := Z Rg d ⊓ Q Rg c
    let F := Z Rg z ⊓ Q Rg a
    F ≤ normalizer (K : Set (FreeAmalgam Rg)) ∧
      K ≤ normalizer (F : Set (FreeAmalgam Rg)) ∧
      ⁅U Rg d ⊓ Q Rg c,F⁆ = ⁅K,F⁆ ∧
      ⁅K,U Rg z ⊓ Q Rg a⁆ = ⁅K,F⁆ ∧
      ⁅U Rg d ⊓ Q Rg c,U Rg z ⊓ Q Rg a⁆ = ⁅K,F⁆ ∧
      ⁅K,F⁆ ≤ U Rg d ⊓ U Rg z := by
  let c := p.walk.getVert 2
  let t := q.walk.getVert 1
  let K := Z Rg d ⊓ Q Rg c
  let F := Z Rg z ⊓ Q Rg a
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hdt : Adjacent Rg d t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent Rg a t := by
    rw [←hqa]
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hdt
    rw [q.start_color] at hh
    cases he : color Rg t <;> simp_all
  have hFt : F ≤ Q Rg t := inf_le_right.trans (Q_le_adjacent_h Rg ht hat)
  have hFd : F ≤ stabilizer Rg d :=
    hFt.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hdt))
  have hZc : Z Rg z ≤ Q Rg c := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.end_color)
    rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    change 4 - 2 < sourceDistance h
    omega
  have hFc : F ≤ stabilizer Rg c := (inf_le_left.trans hZc).trans (fun _ hx => hx.1)
  have hFN : F ≤ normalizer (K : Set (FreeAmalgam Rg)) :=
    (le_inf (hFd.trans (Z_normalized Rg d)) (hFc.trans (Q_normalized Rg c))).trans
      inf_normalizer_le_normalizer_inf
  have hKG : K ≤ stabilizer Rg z := by
    have hh := (terminal_last_edge_inputs h p (distance_gt_two h e hz hk)).2.2
    simpa only [hl,Nat.reduceSub] using inf_le_right.trans hh
  have hdV : Z Rg d ≤ V Rg a := terminal_neighbor_seed_radius hat hdt
  have hKa : K ≤ Q Rg a := (inf_le_left.trans hdV).trans
    ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) a p.start_color)
  have hKN : K ≤ normalizer (F : Set (FreeAmalgam Rg)) :=
    (le_inf (hKG.trans (Z_normalized Rg z))
      (hKa.trans (Q Rg a).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hAt : Z Rg c ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ q.end_color)
    rw [(sourceGeometry h).distance_constant _ q.end_color,SimpleGraph.dist_comm,q.dist_end,hql]
    change 4 - 1 < sourceDistance h
    omega
  let qr := CriticalPath.ofPair (geometry := sourceGeometry h) q.end_color (reverse_pair h e q)
  have hfixed : K = Z Rg d ⊓ centralizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    (critical_seed_centralizer_intersection h e q).symm
  have hUF : ⁅U Rg d ⊓ Q Rg c,F⁆ = ⁅K,F⁆ := by
    rw [critical_moving_kernel_eq_fixed h e qr]
    rw [←full_fixed_seed_edge_commutator h e hz q.start_color hdt
      (Z Rg c) hAt F hFt,←hfixed]
  have hstrip (D : Subgroup (FreeAmalgam Rg)) (hDK : D ≤ K) :
      ⁅D,U Rg z ⊓ Q Rg a⁆ = ⁅D,F⁆ := by
    rw [commutator_comm D,commutator_comm D]
    exact ((critical_kernel_predecessor_moving h e hz
      (distance_gt_two h e hz hk) p).2.2 D (by
        simpa only [hl,Nat.reduceSub] using hDK.trans inf_le_right)).symm
  have hKF := hstrip K le_rfl
  have hUU := (hstrip _ (inf_le_inf_right _ (DistanceEight.U_le_Z Rg d))).trans hUF
  refine ⟨hFN,hKN,hUF,hKF,hUU,le_inf ?_ ?_⟩
  · rw [←hUF]
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hFd.trans (U_normalized d)))
  · rw [←hKF]
    exact (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp (hKG.trans (U_normalized z)))

include h e hz hk in
/-- At distance four, failure of normalization of the full shifted kernel
produces an actual noncentral moving line at the endpoint. -/
theorem borel_four_kernel_failure_line
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hnorm : ¬ Z Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _)) :
    let H := ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆
    Nat.card H = 2 ∧ H ≤ U Rg d ⊓ U Rg z ∧
      H ≤ ⁅Z Rg a,Z Rg z⁆ ⊔
        (U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) ∧
      ¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  let K := Z Rg d ⊓ Q Rg (p.walk.getVert 2)
  have hpair := four_overlapping_kernel_pair h e hz hk hb p q hqa
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) d q.start_color
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.of_le inf_le_left
  have hda : (cosetGraph Rg).dist d a ≤ 2 := by rw [←hqa,q.dist_start (by omega)]
  have hKV : K ≤ V Rg a := inf_le_left.trans
    ((Z_le_localZSpan Rg d a).trans (localZSpan_le_V Rg hda))
  have htrap : K ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    simpa only [hl,Nat.reduceSub] using (inf_le_right : K ≤ Q Rg (p.walk.getVert 2))
  have hline := restricted_kernel_line h e hz hk u hR p hp K hKV htrap hpair.1 hnorm
  have hne : ⁅K,Z Rg z ⊓ Q Rg a⁆ ≠ ⊥ := by
    intro he
    have hh := hline.1
    rw [he,card_bot] at hh
    omega
  exact ⟨hline.1,hpair.2.2.2.2.2,
    restricted_kernel_alignment h e hz hk p hp K hKV htrap hpair.1 hnorm,
    restricted_kernel_noncentral h e hz hk p hp K hKV htrap hne⟩

include h in
/-- The full reverse omega kernel normalizes the shifted critical kernel.
This uses the actual distance-four overlap, not a larger-distance estimate. -/
theorem four_overlapping_omega_kernel_normalizes
    (hb : sourceDistance h = 4)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a) :
    X Rg z ⊓ Q Rg a ≤ normalizer
      ((Z Rg d ⊓ Q Rg (p.walk.getVert 2) : Subgroup (FreeAmalgam Rg)) : Set _) := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hdt : Adjacent Rg d (q.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent Rg a (q.walk.getVert 1) := by
    simpa only [hqa] using adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg (q.walk.getVert 1) = true := by
    have hh := adjacent_color_ne Rg hdt
    rw [q.start_color] at hh
    cases he : color Rg (q.walk.getVert 1) <;> simp_all
  have hXd : X Rg z ⊓ Q Rg a ≤ stabilizer Rg d :=
    (inf_le_right.trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hdt))
  have hdist : (cosetGraph Rg).dist z (p.walk.getVert 2) = 2 := by
    rw [SimpleGraph.dist_comm,p.dist_end,hl]
  have hXc : X Rg z ⊓ Q Rg a ≤ stabilizer Rg (p.walk.getVert 2) :=
    ((inf_le_left.trans (omegaCenter_le (Q Rg z))).trans
      (Q_le_stabilizer_of_dist_two Rg z _ p.end_color hdist))
  exact (le_inf (hXd.trans (Z_normalized Rg d))
    (hXc.trans (Q_normalized Rg _))).trans inf_normalizer_le_normalizer_inf

include h e hz hk in
private theorem restricted_omega_generation_or_control
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (K : Subgroup (FreeAmalgam Rg)) (hKV : K ≤ V Rg a)
    (htrap : K ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hNK : X Rg z ⊓ Q Rg a ≤ normalizer (K : Set (FreeAmalgam Rg))) :
    (X Rg z = U Rg z ⊔
      (X Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)))) ∨
      (⁅K,X Rg z⁆ ≤ ⁅Z Rg a,Z Rg z⁆ ⊔ ⁅K,X Rg z ⊓ Q Rg a⁆ ∧
        X Rg z ≤ normalizer ((K ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set _)) := by
  let N := K ⊔ Z Rg a
  have hKG := htrap.trans (terminal_last_edge_inputs h p (distance_gt_two h e hz hk)).2.2
  have hKQ := hKV.trans ((sourceGeometry h).V_le_Q
    (distance_gt_two h e hz hk) a p.start_color)
  have hZX : Z Rg z ≤ X Rg z := (sourceGeometry h).omega_bound z p.end_color (by
    rw [(sourceGeometry h).distance_constant _ p.end_color]; exact sourceDistance_pos h)
  let pr : CriticalPath Rg (sourceGeometry h) z a :=
    CriticalPath.ofPair p.end_color (reverse_pair h e p)
  have hs : (Q Rg a).relIndex (Z Rg z) < 4 := by
    rw [(small_critical_indices h e hz hk p hp).2]
    decide
  have halt : (X Rg z = U Rg z ⊔
      (X Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)))) ∨
      (⁅K,X Rg z⁆ ≤ ⁅Z Rg a,Z Rg z⁆ ⊔ ⁅K,X Rg z ⊓ Q Rg a⁆ ∧
        X Rg z ≤ normalizer (N : Set (FreeAmalgam Rg))) := by
    rcases small_critical_omega_generation_or_control_at h e hz hk pr hs with hh | hc
    · exact Or.inl hh
    right
    have hXN : X Rg z ≤ normalizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      (critical_X_le_vertex h e z p.end_color a pr.critical).trans (Z_normalized Rg a)
    have hRZ : ⁅X Rg z,Z Rg a⁆ ≤ Z Rg a := le_normalizer_iff_commutator_le_right.mp hXN
    have hKR : K ≤ centralizer ((⁅X Rg z,Z Rg a⁆ :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) :=
      (hKQ.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg a p.start_color)))).trans (centralizer_le hRZ)
    have hZaX : Z Rg a ≤ X Rg a := (sourceGeometry h).omega_bound a p.start_color (by
      rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
    have hRline : ⁅X Rg z,Z Rg a⁆ = ⁅Z Rg a,Z Rg z⁆ := by
      rw [commutator_comm (X Rg z)]
      apply le_antisymm _ (commutator_mono le_rfl hZX)
      exact (commutator_mono hZaX le_rfl).trans_eq
        (small_critical_omega_commutator h e hz hk p hp)
    refine ⟨by simpa only [hRline] using hc K hKG hKR,?_⟩
    have hbound : ⁅X Rg z,K⁆ ≤ N := by
      rw [commutator_comm]
      exact (hc K hKG hKR).trans (sup_le (hRZ.trans le_sup_right)
        ((le_normalizer_iff_commutator_le_left.mp hNK).trans le_sup_left))
    apply le_normalizer_iff.mpr
    intro x hx y hy
    have hm : N.map (MulAut.conj x).toMonoidHom ≤ N := by
      rw [show N = K ⊔ Z Rg a from rfl,Subgroup.map_sup]
      refine sup_le ?_ ((mem_normalizer_iff_map_conj_eq.mp (hXN hx)).le.trans le_sup_right)
      rintro _ ⟨k,hkK,rfl⟩
      have hh := N.mul_mem (hbound (commutator_mem_commutator hx hkK)) (mem_sup_left hkK)
      simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
    exact hm (mem_map_of_mem (MulAut.conj x).toMonoidHom hy)
  exact halt

include h e hz hk in
/-- The noncentral full-omega extension satisfies a strengthening of the
commutator inequality in MS93 (5.12)(1), on the full shifted critical kernel.
Otherwise full omega is generated by its moving subgroup and central part. -/
theorem four_overlapping_omega_generation_or_control
    (hb : sourceDistance h = 4)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4) :
    let K := Z Rg d ⊓ Q Rg (p.walk.getVert 2)
    let N := K ⊔ Z Rg a
    (X Rg z = U Rg z ⊔
      (X Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)))) ∨
      (⁅K,X Rg z⁆ ≤ ⁅Z Rg a,Z Rg z⁆ ⊔ ⁅K,X Rg z ⊓ Q Rg a⁆ ∧
        X Rg z ≤ normalizer (N : Set (FreeAmalgam Rg))) := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  let K := Z Rg d ⊓ Q Rg (p.walk.getVert 2)
  have hdV : Z Rg d ≤ V Rg a := by
    apply (Z_le_localZSpan Rg d a).trans
    apply localZSpan_le_V Rg
    rw [←hqa,q.dist_start (by omega)]
  exact restricted_omega_generation_or_control h e hz hk p hp K
    (inf_le_left.trans hdV)
    (by simpa only [hl,Nat.reduceSub] using (inf_le_right : K ≤ Q Rg (p.walk.getVert 2)))
    (four_overlapping_omega_kernel_normalizes h hb p q hqa)

include h e hz hk in
/-- The full-X normalization comparison is equivalent to the seed
comparison on the actual overlap. Failure forces X=Z at every component
vertex, retaining the entire central attachment. -/
theorem borel_four_kernel_omega_control
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4) :
    let N := (Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a
    (X Rg z ≤ normalizer (N : Set (FreeAmalgam Rg)) ↔
      Z Rg z ≤ normalizer (N : Set (FreeAmalgam Rg))) ∧
    ((¬ X Rg z ≤ normalizer (N : Set (FreeAmalgam Rg))) →
      ∀ w : Vertex Rg, color Rg w = false →
        X Rg w = U Rg w ⊔
          (X Rg w ⊓ centralizer (stabilizer Rg w : Set (FreeAmalgam Rg))) ∧
        X Rg w = Z Rg w) := by
  have halt := four_overlapping_omega_generation_or_control h e hz hk
    (borel_distance_eq_four h e hz hk u hR) p q hqa hp
  have hZX : Z Rg z ≤ X Rg z := (sourceGeometry h).omega_bound z p.end_color (by
    rw [(sourceGeometry h).distance_constant _ p.end_color]; exact sourceDistance_pos h)
  constructor
  · constructor
    · exact fun hn => hZX.trans hn
    · intro hn
      rcases halt with hg | hx
      · rwa [omega_eq_seed_of_central_generation h z p.end_color hg]
      · exact hx.2
  · intro hn w hw
    have hg := halt.resolve_right (fun hx => hn hx.2)
    have hwgen := omega_generation_transport p.end_color hw hg
    exact ⟨hwgen,omega_eq_seed_of_central_generation h w hw hwgen⟩

include h e hz hk in
/-- On the actual distance-four overlap, the noncentral omega extension
satisfies a full-X strengthening of MS93 (5.12)(1) for U_d intersect Q_c.
The printed source uses the restricted seed on the left; this bound uses X.
The central-generation branch is retained for the remaining source proof. -/
theorem four_overlapping_moving_omega_generation_or_control
    (hb : sourceDistance h = 4)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4) :
    let Y := U Rg d ⊓ Q Rg (p.walk.getVert 2)
    (X Rg z = U Rg z ⊔
      (X Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)))) ∨
      (⁅Y,X Rg z⁆ ≤ ⁅Z Rg a,Z Rg z⁆ ⊔ ⁅Y,X Rg z ⊓ Q Rg a⁆ ∧
        X Rg z ≤ normalizer ((Y ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set _)) := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  let K := Z Rg d ⊓ Q Rg (p.walk.getVert 2)
  let Y := U Rg d ⊓ Q Rg (p.walk.getVert 2)
  have hda : (cosetGraph Rg).dist d a = 2 := by rw [←hqa,q.dist_start (by omega)]
  have hUdV : U Rg d ≤ V Rg a := (DistanceEight.U_le_Z Rg d).trans
    ((Z_le_localZSpan Rg d a).trans (localZSpan_le_V Rg hda.le))
  have hXd : X Rg z ⊓ Q Rg a ≤ stabilizer Rg d := inf_le_right.trans
    (Q_le_stabilizer_of_dist_two Rg a d p.start_color (by rwa [SimpleGraph.dist_comm]))
  have hNK := four_overlapping_omega_kernel_normalizes h hb p q hqa
  have hYN : X Rg z ⊓ Q Rg a ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    have he : Y = U Rg d ⊓ K := by
      rw [show K = Z Rg d ⊓ Q Rg (p.walk.getVert 2) from rfl,←inf_assoc,
        inf_eq_left.mpr (DistanceEight.U_le_Z Rg d)]
    rw [he]
    exact (le_inf (hXd.trans (U_normalized d)) hNK).trans inf_normalizer_le_normalizer_inf
  exact restricted_omega_generation_or_control h e hz hk p hp Y
    (inf_le_left.trans hUdV)
    (by simpa only [hl,Nat.reduceSub] using (inf_le_right : Y ≤ Q Rg (p.walk.getVert 2))) hYN

include h e hz hk in
/-- When both overlapping critical images are small, the failure line is
noncentral at both endpoints, on the original full moving covers. -/
theorem borel_four_kernel_failure_reciprocal
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hq : (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) < 4)
    (hnorm : ¬ Z Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _)) :
    let H := ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),Z Rg z ⊓ Q Rg a⁆
    ¬ H ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) ∧
      H ⊓ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) = ⊥ ∧
      H ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) = ⊥ := by
  let c := p.walk.getVert 2
  let F := Z Rg z ⊓ Q Rg a
  let K := Z Rg d ⊓ Q Rg c
  let H := ⁅K,F⁆
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hline := borel_four_kernel_failure_line h e hz hk u hR p q hqa hp hnorm
  have hcard : Nat.card H = 2 := hline.1
  have hne : ⁅F,K⁆ ≠ ⊥ := by
    rw [commutator_comm]
    intro he
    change H = ⊥ at he
    rw [he,card_bot] at hcard
    omega
  let qr : CriticalPath Rg (sourceGeometry h) c d :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      reverse_pair h e q⟩
  have hqrpre : qr.walk.getVert (qr.walk.length-2) = a := by
    change q.walk.reverse.getVert (q.walk.reverse.length-2) = a
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,hql]
    exact hqa
  have hFV : F ≤ V Rg c := by
    apply inf_le_left.trans
    apply (Z_le_localZSpan Rg z c).trans
    apply localZSpan_le_V Rg
    rw [SimpleGraph.dist_comm,p.dist_end,hl]
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le inf_le_left
  have hsmall : (Q Rg d).relIndex (Z Rg c) < 4 := by
    rw [(small_critical_indices h e hz hk q hq).2]
    decide
  have hnon : ¬ H ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) := by
    have hh := restricted_kernel_noncentral h e hz hk qr hsmall F hFV
      (by rw [hqrpre]; exact inf_le_right) hne
    change ¬ ⁅F,K⁆ ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) at hh
    rw [commutator_comm] at hh
    exact hh
  have disjoint_center (T : Subgroup (FreeAmalgam Rg))
      (hn : ¬ H ≤ centralizer (T : Set (FreeAmalgam Rg))) :
      H ⊓ centralizer (T : Set (FreeAmalgam Rg)) = ⊥ := by
    let : Finite H := Nat.finite_of_card_ne_zero (by omega)
    let : Finite (H ⊓ centralizer (T : Set (FreeAmalgam Rg)) : Subgroup _) :=
      Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
    by_contra he
    have hlo := (one_lt_card_iff_ne_bot _).mpr he
    have heq := eq_of_le_of_card_ge
      (show H ⊓ centralizer (T : Set (FreeAmalgam Rg)) ≤ H from inf_le_left) (by omega)
    exact hn (heq ▸ inf_le_right)
  exact ⟨hnon,disjoint_center _ hnon,disjoint_center _ hline.2.2.2⟩

include h e hz hk in
/-- Every small critical path in the original Borel graph has an actual
backward critical overlap. Its full shifted kernel is either normalized by
the endpoint seed or has the noncentral order-two displacement described
above; the reciprocal assertion retains the explicit second image bound. -/
private theorem borel_four_backward_kernel_alternatives
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
      q.walk.getVert 2 = a ∧
      (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
      let K := Z Rg d ⊓ Q Rg (p.walk.getVert 2)
      let F := Z Rg z ⊓ Q Rg a
      let H := ⁅K,F⁆
      F ≤ normalizer (K : Set (FreeAmalgam Rg)) ∧
      K ≤ normalizer (F : Set (FreeAmalgam Rg)) ∧
      ⁅U Rg d ⊓ Q Rg (p.walk.getVert 2),U Rg z ⊓ Q Rg a⁆ = H ∧
      (Z Rg z ≤ normalizer ((K ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set _) ∨
        (Nat.card H = 2 ∧ H ≤ U Rg d ⊓ U Rg z ∧
          H ≤ ⁅Z Rg a,Z Rg z⁆ ⊔
            (U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) ∧
          ¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)))) := by
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hback := (borel_critical_paths h e hz hk u hR p).2.1
  rw [hl] at hback
  obtain ⟨d,w,q,_,_,hverts⟩ := hback
  have hqa : q.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hverts 0 (by decide)
  have hpair := four_overlapping_kernel_pair h e hz hk hb p q hqa
  refine ⟨d,q,hqa,hverts,hpair.1,hpair.2.1,hpair.2.2.2.2.1,?_⟩
  by_cases hn : Z Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _)
  · exact Or.inl hn
  · exact Or.inr (borel_four_kernel_failure_line h e hz hk u hR p q hqa hp hn)

include h e hz hk in
/-- The original distance-four backward comparison uses the whole endpoint
omega group. If it fails, full and moving shifted kernels have the same
noncentral order-two displacement, and central generation is recovered at
every component vertex. No identification of X with Z is assumed. -/
theorem borel_four_backward_full_kernel_alternatives
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
      q.walk.getVert 2 = a ∧
      (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
      let K := Z Rg d ⊓ Q Rg (p.walk.getVert 2)
      let F := X Rg z ⊓ Q Rg a
      let H := ⁅K,F⁆
      F ≤ normalizer (K : Set (FreeAmalgam Rg)) ∧
      (X Rg z ≤ normalizer ((K ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set _) ∨
        (Nat.card H = 2 ∧ H ≤ U Rg d ⊓ U Rg z ∧
          ⁅U Rg d ⊓ Q Rg (p.walk.getVert 2),F⁆ = H ∧
          H ≤ ⁅Z Rg a,Z Rg z⁆ ⊔
            (U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) ∧
          (¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) ∧
          (∀ w : Vertex Rg, color Rg w = false →
            X Rg w = U Rg w ⊔
              (X Rg w ⊓ centralizer (stabilizer Rg w : Set (FreeAmalgam Rg))) ∧
            X Rg w = Z Rg w) ∧
          ((Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) < 4 →
            H ⊓ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) = ⊥))) := by
  have hb := borel_distance_eq_four h e hz hk u hR
  obtain ⟨d,q,hqa,hverts,_⟩ := borel_four_backward_kernel_alternatives h e hz hk u hR p hp
  have homega := borel_four_kernel_omega_control h e hz hk u hR p q hqa hp
  refine ⟨d,q,hqa,hverts,four_overlapping_omega_kernel_normalizes h hb p q hqa,?_⟩
  by_cases hn : X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _)
  · exact Or.inl hn
  · have hnZ := fun hZ => hn (homega.1.mpr hZ)
    have hgen := homega.2 hn
    have heq := (hgen z p.end_color).2
    have hline := borel_four_kernel_failure_line h e hz hk u hR p q hqa hp hnZ
    have hpair := four_overlapping_kernel_pair h e hz hk hb p q hqa
    right
    rw [heq]
    exact ⟨hline.1,hline.2.1,hpair.2.2.1,hline.2.2.1,hline.2.2.2,hgen,
      fun hq => (borel_four_kernel_failure_reciprocal h e hz hk u hR p q hqa hp hq hnZ).2.1⟩

include h e hz hk in
/-- In the failure branch of the full-omega comparison, the order-two
line lies in both endpoint seeds and in the midpoint seed. The midpoint
placement uses the proved full-radius bound and transports the entire
central attachment across the actual last two edges. -/
theorem borel_four_kernel_failure_midpoint
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hnorm : ¬ X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _)) :
    let H := ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆
    H ≤ Z Rg d ⊓ Z Rg (p.walk.getVert 2) ⊓ Z Rg z := by
  let c := p.walk.getVert 2
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hcontrol := borel_four_kernel_omega_control h e hz hk u hR p q hqa hp
  have hnZ := fun hh => hnorm (hcontrol.1.mpr hh)
  have hgen := hcontrol.2 hnorm
  have hline := borel_four_kernel_failure_line h e hz hk u hR p q hqa hp hnZ
  have hZaV : Z Rg a ≤ V Rg c :=
    (Z_le_localZSpan Rg a c).trans (localZSpan_le_V Rg (by
      rw [p.dist_start (by omega)]))
  have hZzV : Z Rg z ≤ V Rg c :=
    (Z_le_localZSpan Rg z c).trans (localZSpan_le_V Rg (by
      rw [SimpleGraph.dist_comm,p.dist_end,hl]))
  have hRline : ⁅Z Rg a,Z Rg z⁆ ≤ Z Rg c := by
    rw [←(hgen c hc).2]
    exact (commutator_mono hZaV hZzV).trans
      (radius_bounds_at h e hz hk c hc a z).2.1
  have hdist : (cosetGraph Rg).dist z c = 2 := by
    rw [SimpleGraph.dist_comm,p.dist_end,hl]
  obtain ⟨t,hzt,hct⟩ := exists_common_neighbor_of_dist_two Rg z c hdist
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hZX : Z Rg z ≤ X Rg z := (sourceGeometry h).omega_bound z p.end_color (by
    rw [(sourceGeometry h).distance_constant _ p.end_color]
    exact sourceDistance_pos h)
  have hC : U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) ≤
      Z Rg c := by
    apply le_trans _ (adjacent_Z_le Rg hc hct)
    intro x hx
    have hxX := mem_omegaCenter_iff.mp (hZX (DistanceEight.U_le_Z Rg z hx.1))
    rw [Z,if_neg (by simp [ht])]
    exact mem_omegaCenter_iff.mpr ⟨(Q_le_adjacent_h Rg ht hzt) hxX.1,
      hxX.2.1,fun y hy => hx.2 y (hy.2 _ (adjacent_symm Rg hzt))⟩
  rw [(hgen z p.end_color).2]
  exact le_inf
    (le_inf (hline.2.1.trans inf_le_left |>.trans (DistanceEight.U_le_Z Rg d))
      (hline.2.2.1.trans (sup_le hRline hC)))
    (hline.2.1.trans inf_le_right |>.trans (DistanceEight.U_le_Z Rg z))

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
