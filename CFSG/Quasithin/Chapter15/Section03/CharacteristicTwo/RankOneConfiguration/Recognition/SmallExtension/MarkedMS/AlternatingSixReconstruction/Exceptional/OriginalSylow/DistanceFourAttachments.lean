module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourStabilizers
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelFixed
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels


import all CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardKernel
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Failure-line stabilizers with the full central attachment

On the original distance-four Borel overlap, failed kernel normalization
produces an order-two line H contained in the critical line D times the
endpoint's full moving central attachment C. Both H and D miss C. Their
joins with C therefore have the same order and are equal. Since the
endpoint stabilizer fixes C pointwise, it has identical pointwise fixers
and identical commutators on H and D. Combining this with the actual
critical-kernel calculation identifies the relative normalizer of H
with that of the full reverse critical kernel.

On the compatible three-path configuration, the right edge fixes H,
while H is noncentral at both incident component vertices. Local
residual/edge generation consequently shows that neither residual
normalizes H. This is the precise residual-invariance obstruction in the
remaining distinct-mover branch of MS93 (5.12)(1). The result does not
assert that the source selectors supply that invariance.

OriginalSylowExceptional applies the results to the literal c.L,d.S
configuration. Both full covers, all central attachments, the actual
transporters and the cubic kernel E with its odd quotient E/Q remain.
Equal movers, large critical images, compatible selection and the terminal
contradiction are still needed before CoreExhaustion and reconstruction.

The internal ForwardKernel import reuses only its general group identity
for a commutator after adjoining a fixed factor; it transports no graph
or source theorem from the natural replacement.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), (5.5)--(5.6), and (5.12)(1), printed pp.866--867,
915--918,924--925; Aschbacher--Smith C.1.31--32, printed pp.135--136.
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
open CFSG.Quasithin.ChapterB.Offenders.Six
local notation "borel" => Theory.SpecificGroups.SymmetricSix.borel
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits

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

private theorem line_disjoint_fixed {F : Type*} [Group F]
    (H C J : Subgroup F) (hH : Nat.card H = 2)
    (hC : C ≤ centralizer (J : Set F))
    (hn : ¬ H ≤ centralizer (J : Set F)) : Disjoint H C := by
  let : Finite H := Nat.finite_of_card_ne_zero (by omega)
  let : Finite (H ⊓ C : Subgroup F) := Finite.of_injective
    (inclusion inf_le_left) (inclusion_injective _)
  apply disjoint_iff.mpr
  by_contra he
  have hlo := (one_lt_card_iff_ne_bot (H ⊓ C)).mpr he
  have heq := eq_of_le_of_card_ge (show H ⊓ C ≤ H from inf_le_left) (by omega)
  exact hn (heq ▸ inf_le_right.trans hC)

private theorem aligned_lines_sup_fixed {F : Type*} [Group F]
    (H D C J : Subgroup F) [Finite (D ⊔ C : Subgroup F)]
    (hH : Nat.card H = 2) (hD : Nat.card D = 2)
    (hHJ : H ≤ J) (hDJ : D ≤ J) (hC : C ≤ centralizer (J : Set F))
    (hnH : ¬ H ≤ centralizer (J : Set F))
    (hnD : ¬ D ≤ centralizer (J : Set F)) (hHD : H ≤ D ⊔ C) :
    H ⊔ C = D ⊔ C := by
  have hHC : C ≤ normalizer (H : Set F) :=
    (hC.trans (centralizer_le hHJ)).trans (Subgroup.centralizer_le_normalizer _)
  have hDC : C ≤ normalizer (D : Set F) :=
    (hC.trans (centralizer_le hDJ)).trans (Subgroup.centralizer_le_normalizer _)
  apply eq_of_le_of_card_ge (sup_le hHD le_sup_right)
  rw [card_sup_eq_mul_of_normalizes_of_disjoint H C hHC
      (line_disjoint_fixed H C J hH hC hnH),
    card_sup_eq_mul_of_normalizes_of_disjoint D C hDC
      (line_disjoint_fixed D C J hD hC hnD),hH,hD]

private theorem aligned_lines_centralizer {F : Type*} [Group F]
    (H D C J : Subgroup F) (hC : C ≤ centralizer (J : Set F))
    (he : H ⊔ C = D ⊔ C) :
    J ⊓ centralizer (H : Set F) = J ⊓ centralizer (D : Set F) := by
  have one_way (A B : Subgroup F) (hBA : B ≤ A ⊔ C) :
      J ⊓ centralizer (A : Set F) ≤ centralizer (B : Set F) := by
    apply le_centralizer_iff.mpr
    exact hBA.trans (sup_le (le_centralizer_iff.mpr inf_le_right)
      (hC.trans (centralizer_le inf_le_left)))
  exact le_antisymm (le_inf inf_le_left (one_way H D (he ▸ le_sup_left)))
    (le_inf inf_le_left (one_way D H (he.symm ▸ le_sup_left)))

include h e hz hk in
/-- Failure and critical lines generate the same subgroup after restoring
 the entire endpoint central attachment. The two lines need not be equal. -/
theorem borel_four_failure_same_central_extension
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hnorm : ¬ X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _)) :
    let H := ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆
    let D := ⁅Z Rg a,Z Rg z⁆
    let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
    H ⊔ C = D ⊔ C := by
  let H := ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆
  let D := ⁅Z Rg a,Z Rg z⁆
  let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
  have hcontrol := borel_four_kernel_omega_control h e hz hk u hR p q hqa hp
  have hxz := (hcontrol.2 hnorm z p.end_color).2
  have hline := borel_four_kernel_failure_line h e hz hk u hR p q hqa hp
    (fun hh => hnorm (hcontrol.1.mpr hh))
  have hHG : H ≤ stabilizer Rg z := by
    dsimp only [H]
    rw [hxz]
    exact hline.2.1.trans inf_le_right |>.trans (DistanceEight.U_le_Z Rg z) |>.trans
      (Z_le_stabilizer Rg z)
  let pr := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color (reverse_pair h e p)
  have hDZ : D ≤ Z Rg z := by
    dsimp only [D]
    rw [commutator_comm]
    exact critical_seed_commutator_le h pr
  have hDCZ : D ⊔ C ≤ Z Rg z := sup_le hDZ
    (inf_le_left.trans (DistanceEight.U_le_Z Rg z))
  let := finite_Z Rg z
  let : Finite (D ⊔ C : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion hDCZ) (inclusion_injective _)
  apply aligned_lines_sup_fixed H D C (stabilizer Rg z)
    (by simpa only [H,hxz] using hline.1)
    (small_critical_commutator_card h e hz hk p hp)
    hHG (hDZ.trans (Z_le_stabilizer Rg z)) inf_le_right
  · simpa only [H,hxz] using hline.2.2.2
  · have hh := critical_commutator_not_central h e hz hk pr
    simpa only [commutator_comm,D] using hh
  · simpa only [H,D,C,hxz] using hline.2.2.1

include h e hz hk in
/-- The full endpoint stabilizer fixes the failure line exactly when it
 fixes the critical line, including on the order-thirty-two cover. -/
theorem borel_four_failure_endpoint_centralizer
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hnorm : ¬ X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _)) :
    stabilizer Rg z ⊓ centralizer
        ((⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆ :
          Subgroup (FreeAmalgam Rg)) : Set _) =
      stabilizer Rg z ⊓ centralizer
        ((⁅Z Rg a,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) : Set _) :=
  aligned_lines_centralizer _ _
    (U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)))
    (stabilizer Rg z) inf_le_right
    (borel_four_failure_same_central_extension h e hz hk u hR p q hqa hp hnorm)

include h e hz hk in
/-- The failure line has exactly the same stabilizer as the full reverse
 critical kernel, relative to the original endpoint stabilizer. -/
theorem borel_four_failure_endpoint_kernel_normalizer
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hnorm : ¬ X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _)) :
    stabilizer Rg z ⊓ normalizer
        ((⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆ :
          Subgroup (FreeAmalgam Rg)) : Set _) =
      stabilizer Rg z ⊓ normalizer
        ((Z Rg z ⊓ Q Rg a : Subgroup (FreeAmalgam Rg)) : Set _) := by
  let H := ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆
  have hcontrol := borel_four_kernel_omega_control h e hz hk u hR p q hqa hp
  have hxz := (hcontrol.2 hnorm z p.end_color).2
  have hline := borel_four_kernel_failure_line h e hz hk u hR p q hqa hp
    (fun hh => hnorm (hcontrol.1.mpr hh))
  have hcard : Nat.card H = 2 := by simpa only [H,hxz] using hline.1
  have hNC : normalizer (H : Set (FreeAmalgam Rg)) = centralizer (H : Set _) :=
    le_antisymm (normalizer_le_centralizer_of_card_two H hcard)
      (Subgroup.centralizer_le_normalizer _)
  change stabilizer Rg z ⊓ normalizer (H : Set _) = _
  rw [hNC]
  rw [borel_four_failure_endpoint_centralizer h e hz hk u hR p q hqa hp hnorm]
  let pr := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color (reverse_pair h e p)
  have hr : (Q Rg a).relIndex (Z Rg z) < 4 := by
    rw [(small_critical_indices h e hz hk p hp).2]
    decide
  simpa only [commutator_comm] using
    (small_critical_kernel_normalizer_eq_line_centralizer h e hz hk pr hr).symm
include h e hz hk in
/-- Every actor in the endpoint stabilizer has the same whole commutator
 on the failure and critical lines. This keeps the full central attachment. -/
theorem borel_four_failure_endpoint_movement
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hnorm : ¬ X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _))
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ stabilizer Rg z) :
    ⁅⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆,A⁆ =
      ⁅⁅Z Rg a,Z Rg z⁆,A⁆ := by
  let H := ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆
  let D := ⁅Z Rg a,Z Rg z⁆
  let C := U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
  have hcontrol := borel_four_kernel_omega_control h e hz hk u hR p q hqa hp
  have hxz := (hcontrol.2 hnorm z p.end_color).2
  have hline := borel_four_kernel_failure_line h e hz hk u hR p q hqa hp
    (fun hh => hnorm (hcontrol.1.mpr hh))
  have hHG : H ≤ stabilizer Rg z := by
    dsimp only [H]
    rw [hxz]
    exact hline.2.1.trans inf_le_right |>.trans (DistanceEight.U_le_Z Rg z) |>.trans
      (Z_le_stabilizer Rg z)
  have hDG : D ≤ stabilizer Rg z := by
    dsimp only [D]
    rw [commutator_comm]
    exact (critical_seed_commutator_le h
      (CriticalPath.ofPair p.end_color (reverse_pair h e p))).trans (Z_le_stabilizer Rg z)
  have hCA : C ≤ centralizer (A : Set (FreeAmalgam Rg)) :=
    inf_le_right.trans (centralizer_le hA)
  have hCH : C ≤ normalizer (H : Set (FreeAmalgam Rg)) :=
    (inf_le_right.trans (centralizer_le hHG)).trans (Subgroup.centralizer_le_normalizer _)
  have hCD : C ≤ normalizer (D : Set (FreeAmalgam Rg)) :=
    (inf_le_right.trans (centralizer_le hDG)).trans (Subgroup.centralizer_le_normalizer _)
  calc
    ⁅H,A⁆ = ⁅H ⊔ C,A⁆ := (commutator_sup_fixed H C A hCH hCA).symm
    _ = ⁅D ⊔ C,A⁆ := congrArg (fun T => ⁅T,A⁆)
      (borel_four_failure_same_central_extension h e hz hk u hR p q hqa hp hnorm)
    _ = ⁅D,A⁆ := commutator_sup_fixed D C A hCD hCA

include h in
private theorem line_moved_by_residual
    {a t : Vertex Rg} (ha : color Rg a = false) (hat : Adjacent Rg a t)
    (H : Subgroup (FreeAmalgam Rg)) (hHt : H ≤ Z Rg t) (hH : Nat.card H = 2)
    (hn : ¬ H ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) :
    ¬ Ltilde Rg a ≤ normalizer (H : Set (FreeAmalgam Rg)) := by
  intro hN
  apply hn
  apply le_centralizer_iff.mpr
  rw [←CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
    (by rw [h.relative_residual]; exact (codisjoint_subgroupOf_sup L R).eq_top) ha hat]
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [ha] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  exact sup_le (hN.trans (normalizer_le_centralizer_of_card_two H hH))
    (le_centralizer_iff.mpr (hHt.trans (terminal_edge_seed_central ht)))

include h e hz hk in
/-- In the compatible distinct-mover failure, both residuals incident with
 the right edge move the same failure line. The entire edge fixes it, so
 residual normalization would force the forbidden whole-stabilizer centrality.
 This identifies the residual invariance still needed in MS93 (5.12)(1). -/
theorem borel_four_failure_right_residuals_move
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d y : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a)
    (r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y)
    (hrz : r.walk.getVert 2 = z)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2))
    (hgen' : Q Rg (q.walk.getVert 1) ⊔ Z Rg z = stabilizer Rg a)
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg a)
    (hxd : act Rg x (p.walk.getVert 2) = d)
    (hxt : act Rg x (p.walk.getVert 1) = q.walk.getVert 1)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hq : (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) < 4)
    (hnorm : ¬ X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _))
    (hne : edgeOffenderJoin a (p.walk.getVert 1) ≠
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1)) :
    let H := ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆
    (¬ Ltilde Rg (p.walk.getVert 2) ≤ normalizer (H : Set (FreeAmalgam Rg))) ∧
      ¬ Ltilde Rg z ≤ normalizer (H : Set (FreeAmalgam Rg)) := by
  let H := ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),X Rg z ⊓ Q Rg a⁆
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hab : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcb : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hJa := remaining_edge_join_act h e hz hk u (Or.inr hR) p.start_color hab x
  have hJc := remaining_edge_join_act h e hz hk u (Or.inr hR) q.end_color hcb x
  rw [show act Rg x a = a from hx,hxt] at hJa
  rw [hxd,hxt] at hJc
  have hne' : edgeOffenderJoin a (q.walk.getVert 1) ≠
      edgeOffenderJoin d (q.walk.getVert 1) := by
    intro he
    apply hne
    exact (map_injective (MulAut.conj x⁻¹).injective)
      (hJa.symm.trans (he.trans hJc))
  have hHc := borel_four_failure_not_central_middle h e hz hk u hR
    p q hqa hgen' x hx hxd hp hq hnorm hne'
  have hHt := (borel_four_failure_middle_central h e hz hk u hR
    p q hqa r hrz hgen hp hnorm hne).2
  have hcontrol := borel_four_kernel_omega_control h e hz hk u hR p q hqa hp
  have hxz := (hcontrol.2 hnorm z p.end_color).2
  have hline := borel_four_kernel_failure_line h e hz hk u hR p q hqa hp
    (fun hh => hnorm (hcontrol.1.mpr hh))
  have hHcard : Nat.card H = 2 := by simpa only [H,hxz] using hline.1
  have hHz : ¬ H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
    simpa only [H,hxz] using hline.2.2.2
  have hct : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z (p.walk.getVert 3) := by
    have hh := (cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 3) (by omega))
    change Adjacent Rg (p.walk.getVert 3) (p.walk.getVert 4) at hh
    rw [←hl,SimpleGraph.Walk.getVert_length] at hh
    exact adjacent_symm Rg hh
  exact ⟨line_moved_by_residual h q.end_color hct H hHt hHcard hHc,
    line_moved_by_residual h p.end_color hzt H hHt hHcard hHz⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
