module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusAlignment
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneCoreAction
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneShiftedSlice
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward

/-!
# Choice independence for the full cubic plane kernel

The aligned actor calculation fixes the moving part of a critical kernel.
The original full seed is the join of its moving cover and the incident
edge seed; the latter centralizes every actor inside that edge. Restoring
this attachment makes the entire critical kernel fixed.

Two nonzero aligned full-kernel commutators on one plane edge therefore
coincide: a larger joined commutator would force aligned whole-cover
movement and hence zero kernel movement. If another actor escapes this
line, the alignment alternative is impossible, giving full endpoint
control by its kernel commutator and the original critical line.

Both full covers and their attachments remain on the original cubic graph,
with projection kernel E and its odd quotient E/Q. These local comparison
theorems do not assert the remaining shifted-span or terminal exclusions.
The narrow private imports reuse established full-cover comparisons within
this reconstruction implementation without widening their public interfaces.

Source: MS93 (3.3), (5.9), printed pp.866--867,920--922.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative Pointwise
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e in
private theorem full_reverse_kernel_eq_fixed {a z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z) :
    Z Rg z ⊓ Q Rg a = Z Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) := by
  let q := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      a p.start_color (by
        rw [(sourceGeometry h).distance_constant a p.start_color]
        exact sourceDistance_pos h) z p.end_color p.critical)
  exact (critical_seed_centralizer_intersection h e q).symm

include h e hz hk in
/-- The aligned moving-kernel calculation fixes the entire original seed
kernel once its edge attachment is restored. -/
theorem critical_aligned_edge_actor_fixes_full_kernel
    {a z t : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hsmall : (Q Rg z).relIndex (Z Rg a) < 4)
    (hzt : Adjacent Rg z t) (hAt : Z Rg a ≤ Q Rg t)
    (P : Subgroup (FreeAmalgam Rg)) (hPt : P ≤ Q Rg t)
    (hmove : ⁅U Rg z,P⁆ ≤ ⁅Z Rg a,Z Rg z⁆ ⊔
      (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)))) :
    ⁅Z Rg z ⊓ Q Rg a,P⁆ = ⊥ := by
  have htG : Q Rg t ≤ stabilizer Rg z :=
    fun _ hx => hx.2 _ (adjacent_symm Rg hzt)
  have hmoving := critical_aligned_actor_fixes_moving_kernel h e hz hk p hsmall
    P (hPt.trans htG) hmove
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg t <;> simp_all
  have hseed : Z Rg t ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hseedA := hseed.trans (centralizer_le hAt)
  have hseedN : Z Rg t ≤ normalizer (U Rg z : Set (FreeAmalgam Rg)) :=
    ((adjacent_Z_le Rg p.end_color hzt).trans (Z_le_stabilizer Rg z)).trans (U_normalized z)
  let F := U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg))
  have hfull : Z Rg z ⊓ Q Rg a = F ⊔ Z Rg t := by
    rw [full_reverse_kernel_eq_fixed h e p,
      vertex_seed_eq_moving_sup_edge h e hz p.end_color hzt,
      sup_comm (U Rg z),inf_centralizer_sup_of_centralizing _ _ _ hseedN hseedA]
    exact sup_comm _ _
  have hNF : Z Rg t ≤ normalizer (F : Set (FreeAmalgam Rg)) :=
    (le_inf hseedN (hseedA.trans (centralizer (Z Rg a : Set (FreeAmalgam Rg))).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  rw [hfull,commutator_sup_of_central_attachment F _ P hNF
    (hseed.trans (centralizer_le hPt))]
  change ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),P⁆ = ⊥
  rw [←critical_moving_kernel_eq_fixed h e p]
  exact hmoving

include h e hz hk in
/-- Nonzero aligned commutators of the same full reverse kernel with two
actors in the same original plane edge are the same order-two line. -/
theorem plane_aligned_kernel_line_unique
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z t : Vertex Rg}
    (q : CriticalPath Rg (sourceGeometry h) a z)
    (hsmall : (Q Rg z).relIndex (Z Rg a) < 4)
    (hzt : Adjacent Rg z t) (hAt : Z Rg a ≤ Q Rg t)
    (P₁ P₂ : Subgroup (FreeAmalgam Rg))
    (hP₁ : P₁ ≤ Q Rg t) (hP₂ : P₂ ≤ Q Rg t)
    (hn₁ : ⁅Z Rg z ⊓ Q Rg a,P₁⁆ ≠ ⊥)
    (hn₂ : ⁅Z Rg z ⊓ Q Rg a,P₂⁆ ≠ ⊥)
    (ha₁ : ⁅Z Rg z ⊓ Q Rg a,P₁⁆ ≤
      ⁅Z Rg a,Z Rg z⁆ ⊔
        (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))))
    (ha₂ : ⁅Z Rg z ⊓ Q Rg a,P₂⁆ ≤
      ⁅Z Rg a,Z Rg z⁆ ⊔
        (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)))) :
    ⁅Z Rg z ⊓ Q Rg a,P₁⁆ = ⁅Z Rg z ⊓ Q Rg a,P₂⁆ := by
  let F := Z Rg z ⊓ Q Rg a
  let C := stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
  let T := ⁅Z Rg a,Z Rg z⁆ ⊔ C
  let P := P₁ ⊔ P₂
  let K := ⁅F,P⁆
  have hPt : P ≤ Q Rg t := sup_le hP₁ hP₂
  have htG : Q Rg t ≤ stabilizer Rg z :=
    fun _ hx => hx.2 _ (adjacent_symm Rg hzt)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [q.end_color] at hh
    cases he : color Rg t <;> simp_all
  have heC : Z Rg t ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
    intro v hv
    rw [Z,if_neg (by simp [ht])] at hv
    exact (mem_omegaCenter_iff.mp hv).2.2
  have hcrit : ⁅Z Rg a,Z Rg z⁆ ≤ Z Rg t := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hAt).trans
      (plane_edge_seed_commutator h e hz hk u hR q.end_color hzt)
  have hTC : T ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) :=
    sup_le (hcrit.trans heC) (inf_le_right.trans (centralizer_le htG))
  have hTN : Q Rg t ≤ normalizer (T : Set (FreeAmalgam Rg)) :=
    (le_centralizer_iff.mp hTC).trans (Subgroup.centralizer_le_normalizer _)
  have hKT : K ≤ T := by
    change ⁅F,P₁ ⊔ P₂⁆ ≤ T
    rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal (Q Rg t) P₁ P₂ F T hTN hP₁ hP₂
      (by rwa [commutator_comm]) (by rwa [commutator_comm])
  have hTG : T ≤ stabilizer Rg z :=
    sup_le (hcrit.trans ((adjacent_Z_le Rg q.end_color hzt).trans
      (Z_le_stabilizer Rg z))) inf_le_left
  let := finite_stabilizer Rg z
  let : Finite K := Finite.of_injective (inclusion (hKT.trans hTG)) (inclusion_injective _)
  have hfixed : F = Z Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    full_reverse_kernel_eq_fixed h e q
  let := finite_Z Rg z
  let : Finite (U Rg z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg z)) (inclusion_injective _)
  have hQC : Q Rg a ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a q.start_color))
  have hindex : (centralizer (Z Rg a : Set (FreeAmalgam Rg))).relIndex
      (U Rg z) ≤ 2 :=
    ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk q hsmall).2
  have hcard : Nat.card K ≤ 2 := by
    by_contra! hlarge
    have hlarge' : 2 < Nat.card (⁅Z Rg z ⊓ centralizer
        (Z Rg a : Set (FreeAmalgam Rg)),P⁆ : Subgroup (FreeAmalgam Rg)) := by
      simpa only [K,hfixed] using hlarge
    have hcontrol := plane_edge_large_fixed_commutator h e hz hk u hR.le q.end_color hzt
      (Z Rg a) P hAt hPt q.critical.2 hindex hlarge'
    have hwhole : ⁅U Rg z,P⁆ ≤ T :=
      (commutator_mono (DistanceEight.U_le_Z Rg z) le_rfl).trans
        (hcontrol.trans (sup_le (hfixed ▸ hKT)
          (by rw [commutator_comm]; exact le_sup_left)))
    have hbot := critical_aligned_edge_actor_fixes_full_kernel h e hz hk q hsmall hzt hAt P hPt hwhole
    change K = ⊥ at hbot
    rw [hbot,card_bot] at hlarge
    omega
  have h₁ : ⁅F,P₁⁆ ≤ K := commutator_mono le_rfl le_sup_left
  have h₂ : ⁅F,P₂⁆ ≤ K := commutator_mono le_rfl le_sup_right
  let : Finite (⁅F,P₁⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion h₁) (inclusion_injective _)
  let : Finite (⁅F,P₂⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion h₂) (inclusion_injective _)
  have hc₁ := (one_lt_card_iff_ne_bot ⁅F,P₁⁆).mpr hn₁
  have hc₂ := (one_lt_card_iff_ne_bot ⁅F,P₂⁆).mpr hn₂
  exact (eq_of_le_of_card_ge h₁ (by omega)).trans (eq_of_le_of_card_ge h₂ (by omega)).symm

include h e hz hk in
/-- Escape from the selected aligned full-kernel line forces the literal
full endpoint commutator into the source control alternative. -/
theorem plane_edge_control_of_kernel_escape
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {c z t : Vertex Rg}
    (q : CriticalPath Rg (sourceGeometry h) c z)
    (hsmall : (Q Rg z).relIndex (Z Rg c) < 4)
    (hzt : Adjacent Rg z t) (hct : Z Rg c ≤ Q Rg t)
    (D P : Subgroup (FreeAmalgam Rg))
    (hDt : D ≤ Q Rg t) (hPt : P ≤ Q Rg t)
    (hne : ⁅D,Z Rg z ⊓ Q Rg c⁆ ≠ ⊥)
    (halign : ⁅D,Z Rg z ⊓ Q Rg c⁆ ≤
      ⁅Z Rg c,Z Rg z⁆ ⊔
        (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))))
    (hnot : ¬ ⁅P,Z Rg z ⊓ Q Rg c⁆ ≤ ⁅D,Z Rg z ⊓ Q Rg c⁆) :
    ⁅P,Z Rg z⁆ ≤ ⁅P,Z Rg z ⊓ Q Rg c⁆ ⊔
      ⁅Z Rg c,Z Rg z⁆ := by
  let K := Z Rg z ⊓ Q Rg c
  have hfixed : K = Z Rg z ⊓ centralizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    full_reverse_kernel_eq_fixed h e q
  let := finite_Z Rg z
  let : Finite (U Rg z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg z)) (inclusion_injective _)
  have hQC : Q Rg c ≤ centralizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg c q.start_color))
  have hindex : (centralizer (Z Rg c : Set (FreeAmalgam Rg))).relIndex
      (U Rg z) ≤ 2 :=
    ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk q hsmall).2
  rcases plane_edge_alignment_or_control h e hz hk u hR.le q.end_color hzt
    (Z Rg c) P hct hPt q.critical.2 hindex with hA | hC
  · have hPe : ⁅K,P⁆ ≠ ⊥ := by
      intro he
      apply hnot
      rw [commutator_comm]
      exact he ▸ bot_le
    have hDe : ⁅K,D⁆ ≠ ⊥ := by rwa [commutator_comm]
    have hDalign : ⁅K,D⁆ ≤ ⁅Z Rg c,Z Rg z⁆ ⊔
        (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) := by
      rwa [commutator_comm]
    have heq := plane_aligned_kernel_line_unique h e hz hk u hR q hsmall hzt hct
      D P hDt hPt hDe hPe hDalign (by
        simpa only [←hfixed,commutator_comm (Z Rg z) (Z Rg c)] using hA)
    exact False.elim (hnot (by rw [commutator_comm P,commutator_comm D]; exact heq.symm.le))
  · simpa only [←hfixed,commutator_comm (Z Rg z) P,commutator_comm K P,
      commutator_comm (Z Rg z) (Z Rg c)] using hC

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
