module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneCoreAction
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSelectedFour
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaGeneration

/-!
# Common fixed kernels of the paired cubic plane selectors

For two trapped backward candidates on the original cubic graph, the common
fixed subgroup of their reverse seed kernels lies in the starting Baumann
slice. The plane edge acts abelianly on the whole seed, so it preserves this
fixed subgroup. Each actual critical endpoint controls its commutator modulo
the starting seed. The retained two-seed generation identity and the original
cubic normal-section theorem then put the common fixer in the slice.

A strict slice therefore forces the two full reverse omega kernels to move
the entire moving cover by more than a line. Their full-seed commutator is
the join of their individual commutators, lies in the shared edge seed, and
is fixed by the whole edge kernel. In particular the two commutators cannot
both lie in one subgroup of order two.

The same trapped configuration excludes the noncentral omega-extension
alternative. Otherwise the full-omega control at both endpoints makes the
whole backward seed product normal and fixed modulo the starting seed,
contradicting the strict slice. Thus X is centrally generated and X = Z at
every component vertex in this remaining branch. This equality is proved
from the trapped configuration, never assumed from an edge intersection.

The final application constructs the normalized selectors and transports the
strict slice with the same neighbor conjugator. It retains the component
switch, both generation identities, every switched-path vertex and both
possible backward walks. The only remaining trapped case has the proved
omega equality and separated full-kernel commutators. The comparison of the
same-switch commutators, complete plane/Borel exclusions, terminal argument
and both whole-core reconstructions remain open.

Only the abelian-action argument is shared with the natural branch's
SectionFive.CubePairedKernel. All groups, quotient actions and embeddings here
are those of the original cubic graph; ker(pi) = E and the nontrivial odd
quotient E/Q are retained. Both moving covers of orders sixteen and thirty-two
and the full central attachments are used.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii) and (5.7), printed pp.866--867,919;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem plane_edge_preserves_fixer (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hc : color Rg c = false) (hct : Adjacent Rg c t)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ Q Rg t) :
    Q Rg t ≤ normalizer ((Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)) :
      Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
  let : IsElementaryAbelian 2 D := by
    rw [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq]
    exact CFSG.Quasithin.ChapterB.Offenders.Six.elementary_disjointTranspositions (3 : Fin 4)
  let : IsElementaryAbelian 2 (D.map (MulAut.conj u).toMonoidHom) := IsElementaryAbelian.map _
  have hab : ⁅(Rg).map π,(Rg).map π⁆ = ⊥ := by
    rw [hR]
    exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer _)
  have hderived := edge_derived_le_core_of_abelian_image h e hz hk hab hc hct
  have htG : Q Rg t ≤ stabilizer Rg c := fun _ hx => hx.2 _ (adjacent_symm Rg hct)
  exact abelian_action_preserves_fixed _ _ A (htG.trans (Z_normalized Rg c)) hA
    (hderived.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg c hc))))

include h e hz hk in
/-- Both trapped critical seeds normalize the common-fixer product with the
starting seed. Their actual generation identity puts the common fixer in the
starting Baumann slice, retaining the full central attachments. -/
theorem plane_paired_trapped_fixer_le_slice
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hq : (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2))) :
    Z Rg c ⊓ centralizer
      ((Z Rg z ⊓ Q Rg (alpha Rg) ⊔ Z Rg z' ⊓ Q Rg (alpha Rg) :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ≤
      B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
  have hb := distance_gt_two h e hz hk
  let A := Z Rg z ⊓ Q Rg (alpha Rg) ⊔ Z Rg z' ⊓ Q Rg (alpha Rg)
  let F := Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg))
  let Y := F ⊔ Z Rg (alpha Rg)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  have hdist : (cosetGraph Rg).dist c (alpha Rg) ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hct)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat))
    have hh := (cosetGraph_connected Rg).dist_triangle (u := c) (v := t) (w := alpha Rg)
    omega
  have hZV : Z Rg c ≤ V Rg (alpha Rg) :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hdist)
  have hFt := plane_edge_preserves_fixer h e hz hk u hR hc hct A
    ((sup_le inf_le_right inf_le_right).trans (Q_le_adjacent_h Rg ht hat))
  have hmove {w : Vertex Rg}
      (r : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hr : (Q Rg w).relIndex (Z Rg (alpha Rg)) < 4)
      (hrbad : Z Rg c ≤ Q Rg (r.walk.getVert (r.walk.length-2)))
      (hA : Z Rg w ⊓ Q Rg (alpha Rg) ≤ A) :
      ⁅Y,Z Rg w⁆ ≤ Z Rg (alpha Rg) := by
    have hFmove := small_critical_predecessor_commutator h e hz hk hb r hr F
      (inf_le_left.trans hrbad) (inf_le_right.trans (centralizer_le hA))
    apply commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      F (Z Rg (alpha Rg)) (Z Rg w) (Z Rg (alpha Rg))
      (Z_normalized Rg _) ((inf_le_left.trans hZV).trans
        ((sourceGeometry h).V_local _ rfl hb)) (Z_le_stabilizer Rg _) hFmove
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
        (sourceDistance_pos h) r.critical).trans (Z_normalized Rg _))
  have hpY := hmove p hp hbad le_sup_left
  have hqY := hmove q hq hbad' le_sup_right
  have hYN : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    refine sup_le (sup_le ?_ (le_normalizer_iff_commutator_le_left.mpr
      (hpY.trans le_sup_right))) (le_normalizer_iff_commutator_le_left.mpr
        (hqY.trans le_sup_right))
    rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat]
    exact (le_inf hFt ((show Q Rg t ≤ stabilizer Rg (alpha Rg) from
      fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans (Z_normalized Rg _))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact le_sup_left.trans (normalized_radius_le_slice_of_critical_commutator h e hz hb p Y
    (sup_le (inf_le_left.trans hZV) (Z_le_VBall Rg _ 2)) hYN hpY)

include h e hz hk in
/-- With the strict source slice, the two full reverse omega kernels move
the entire moving cover by more than a line. The two kernels are taken on
the same trapped paths used in the generation identity. -/
theorem plane_paired_trapped_joint_movement_gt_two
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hq : (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2)))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c)) :
    2 < Nat.card (⁅U Rg c,
      X Rg z ⊓ Q Rg (alpha Rg) ⊔ X Rg z' ⊓ Q Rg (alpha Rg)⁆ :
        Subgroup (FreeAmalgam Rg)) := by
  by_contra! hcard
  let A := X Rg z ⊓ Q Rg (alpha Rg) ⊔ X Rg z' ⊓ Q Rg (alpha Rg)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  have hAG : A ≤ stabilizer Rg c :=
    ((sup_le inf_le_right inf_le_right).trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hi := moving_small_commutator_fixed_index h e hz hk hc A hAG hcard
  have hseed (w : Vertex Rg) (hw : color Rg w = false) : Z Rg w ≤ X Rg w := by
    apply (sourceGeometry h).omega_bound w hw
    rw [(sourceGeometry h).distance_constant w hw]
    exact sourceDistance_pos h
  have hFA : Z Rg z ⊓ Q Rg (alpha Rg) ⊔ Z Rg z' ⊓ Q Rg (alpha Rg) ≤ A :=
    sup_le_sup (inf_le_inf_right _ (hseed z p.end_color))
      (inf_le_inf_right _ (hseed z' q.end_color))
  have hFB : Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)) ≤
      B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    (inf_le_inf_left _ (centralizer_le hFA)).trans
      (plane_paired_trapped_fixer_le_slice h e hz hk u hR p q hp hq hat hct hgen hbad hbad')
  let := finite_Z Rg c
  let : Finite (U Rg c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg c)) (inclusion_injective _)
  have hh := relIndex_le_of_le_left
    ((inf_le_inf_right _ (DistanceEight.U_le_Z Rg c)).trans hFB)
    (index_ne_zero_of_finite (H := (U Rg c ⊓ centralizer
      (A : Set (FreeAmalgam Rg))).subgroupOf (U Rg c)))
  rw [inf_relIndex_left] at hh
  exact (Nat.not_le_of_gt hs) (hh.trans hi)

include h e hz hk in
/-- Two trapped full reverse omega kernels have distinct joint movement
beyond any single line. Their full-seed commutator is the literal join of
the individual commutators, and the whole join is fixed by the shared edge. -/
theorem plane_paired_trapped_commutator_comparison
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hq : (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2)))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c)) :
    let A := X Rg z ⊓ Q Rg (alpha Rg)
    let A' := X Rg z' ⊓ Q Rg (alpha Rg)
    let H := ⁅A,Z Rg c⁆
    let H' := ⁅A',Z Rg c⁆
    ⁅A ⊔ A',Z Rg c⁆ = H ⊔ H' ∧
      H ⊔ H' ≤ Z Rg t ∧ ⁅H ⊔ H',Q Rg t⁆ = ⊥ ∧
      2 < Nat.card (H ⊔ H' : Subgroup (FreeAmalgam Rg)) ∧
      (Nat.card H ≤ 2 → ¬ H' ≤ H) ∧ (Nat.card H' ≤ 2 → ¬ H ≤ H') := by
  let A := X Rg z ⊓ Q Rg (alpha Rg)
  let A' := X Rg z' ⊓ Q Rg (alpha Rg)
  let H := ⁅A,Z Rg c⁆
  let H' := ⁅A',Z Rg c⁆
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  have he := plane_reverse_kernel_edge_control h e hz hk u hR rfl hc hat hct (z := z)
  have he' := plane_reverse_kernel_edge_control h e hz hk u hR rfl hc hat hct (z := z')
  have hsum : H ⊔ H' ≤ Z Rg t := sup_le he.1 he'.1
  have hfix : H ⊔ H' ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) :=
    sup_le (commutator_eq_bot_iff_le_centralizer.mp he.2.2)
      (commutator_eq_bot_iff_le_centralizer.mp he'.2.2)
  have hN : Q Rg t ≤ normalizer ((H ⊔ H' : Subgroup (FreeAmalgam Rg)) :
      Set (FreeAmalgam Rg)) :=
    (le_centralizer_iff.mp hfix).trans (Subgroup.centralizer_le_normalizer _)
  have heq : ⁅A ⊔ A',Z Rg c⁆ = H ⊔ H' := by
    apply le_antisymm
    · exact commutator_sup_le_of_relative_normal (Q Rg t) A A' (Z Rg c) (H ⊔ H') hN
        (inf_le_right.trans (Q_le_adjacent_h Rg ht hat))
        (inf_le_right.trans (Q_le_adjacent_h Rg ht hat)) le_sup_left le_sup_right
    · exact sup_le (commutator_mono le_sup_left le_rfl) (commutator_mono le_sup_right le_rfl)
  let := finite_Z Rg t
  let : Finite (H ⊔ H' : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion hsum) (inclusion_injective _)
  have hbig : 2 < Nat.card (H ⊔ H' : Subgroup (FreeAmalgam Rg)) := by
    have hl := plane_paired_trapped_joint_movement_gt_two h e hz hk u hR
      p q hp hq hat hct hgen hbad hbad' hs
    have hle : ⁅U Rg c,A ⊔ A'⁆ ≤ H ⊔ H' := by
      rw [commutator_comm]
      exact (commutator_mono le_rfl (DistanceEight.U_le_Z Rg c)).trans_eq heq
    exact hl.trans_le (card_le_of_le hle)
  refine ⟨heq,hsum,commutator_eq_bot_iff_le_centralizer.mpr hfix,hbig,?_,?_⟩
  · intro hcard hle
    rw [sup_of_le_left hle] at hbig
    omega
  · intro hcard hle
    rw [sup_of_le_right hle] at hbig
    omega

include h e hz hk in
/-- If both small backward candidates are trapped at a strict slice, the
noncentral omega-extension alternative is impossible. The full omega layer
is centrally generated at every original component vertex and equals its
seed. This conclusion uses both endpoint controls, not an identification of
X with Z in the input. -/
theorem plane_paired_trapped_omega_generation
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hq : (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2)))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c)) :
    ∀ a : Vertex Rg, color Rg a = false →
      (X Rg a = U Rg a ⊔
        (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))) ∧
      X Rg a = Z Rg a := by
  have hb := distance_gt_two h e hz hk
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  have hdist : (cosetGraph Rg).dist c (alpha Rg) ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hct)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat))
    have hh := (cosetGraph_connected Rg).dist_triangle (u := c) (v := t) (w := alpha Rg)
    omega
  have hZV : Z Rg c ≤ V Rg (alpha Rg) :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hdist)
  have hZQ : Z Rg c ≤ Q Rg (alpha Rg) :=
    hZV.trans ((sourceGeometry h).V_le_Q hb _ rfl)
  have hcase {w : Vertex Rg}
      (r : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hr : (Q Rg w).relIndex (Z Rg (alpha Rg)) < 4)
      (hrbad : Z Rg c ≤ Q Rg (r.walk.getVert (r.walk.length-2))) :
      (X Rg w = U Rg w ⊔
        (X Rg w ⊓ centralizer (stabilizer Rg w : Set (FreeAmalgam Rg)))) ∨
      ⁅Z Rg c,Z Rg w⁆ ≤ Z Rg (alpha Rg) := by
    have hrev := critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      (alpha Rg) rfl (sourceDistance_pos h) w r.end_color r.critical
    let rr : CriticalPath Rg (sourceGeometry h) w (alpha Rg) :=
      CriticalPath.ofPair r.end_color hrev
    have hrs : (Q Rg (alpha Rg)).relIndex (Z Rg w) < 4 := by
      rw [(small_critical_indices h e hz hk r hr).2]
      decide
    rcases small_critical_omega_generation_or_control_at h e hz hk rr hrs with hcentral | hcontrol
    · exact Or.inl hcentral
    right
    have hl : 2 < r.walk.length := r.length_eq_b ▸ hb
    let last := r.walk.getVert (r.walk.length-1)
    have hwlast : Adjacent Rg w last := by
      have hh := r.walk.adj_getVert_succ (i := r.walk.length-1) (by omega)
      rw [show r.walk.length-1+1=r.walk.length by omega,r.walk.getVert_length] at hh
      exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
    have hlast : color Rg last = true := by
      have hh := adjacent_color_ne Rg hwlast
      rw [r.end_color] at hh
      cases he : color Rg last <;> simp_all
    have hprevlast : Adjacent Rg (r.walk.getVert (r.walk.length-2)) last := by
      have hh := r.walk.adj_getVert_succ (i := r.walk.length-2) (by omega)
      rw [show r.walk.length-2+1=r.walk.length-1 by omega] at hh
      exact (cosetGraph_adj Rg _ _).mp hh
    have hlocal : Z Rg c ≤ stabilizer Rg w :=
      (hrbad.trans (Q_le_adjacent_h Rg hlast hprevlast)).trans
        (fun _ hx => hx.2 _ (adjacent_symm Rg hwlast))
    have hline : ⁅X Rg w,Z Rg (alpha Rg)⁆ ≤ Z Rg (alpha Rg) :=
      le_normalizer_iff_commutator_le_right.mp
        ((critical_X_le_vertex h e w r.end_color (alpha Rg) hrev).trans (Z_normalized Rg _))
    have hfixed : Z Rg c ≤ centralizer
        ((⁅X Rg w,Z Rg (alpha Rg)⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) :=
      (hZQ.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg (alpha Rg) rfl)))).trans (centralizer_le hline)
    have hkernel : ⁅Z Rg c,X Rg w ⊓ Q Rg (alpha Rg)⁆ ≤ Z Rg (alpha Rg) := by
      rw [commutator_comm]
      exact (plane_reverse_kernel_edge_control h e hz hk u hR rfl hc hat hct (z := w)).2.1.trans inf_le_left
    have hZX : Z Rg w ≤ X Rg w := (sourceGeometry h).omega_bound w r.end_color (by
      rw [(sourceGeometry h).distance_constant w r.end_color]
      exact sourceDistance_pos h)
    exact (commutator_mono le_rfl hZX).trans
      ((hcontrol (Z Rg c) hlocal hfixed).trans (sup_le hline hkernel))
  have finish (w : Vertex Rg) (hw : color Rg w = false)
      (hcentral : X Rg w = U Rg w ⊔
        (X Rg w ⊓ centralizer (stabilizer Rg w : Set (FreeAmalgam Rg)))) :
      ∀ a : Vertex Rg, color Rg a = false →
        (X Rg a = U Rg a ⊔
          (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))) ∧
        X Rg a = Z Rg a := by
    intro a ha
    have hh := omega_generation_transport hw ha hcentral
    exact ⟨hh,omega_eq_seed_of_central_generation h a ha hh⟩
  rcases hcase p hp hbad with hcentral | hcomm
  · exact finish z p.end_color hcentral
  rcases hcase q hq hbad' with hcentral | hcomm'
  · exact finish z' q.end_color hcentral
  exfalso
  let Y := Z Rg c ⊔ Z Rg (alpha Rg)
  have hmove {w : Vertex Rg}
      (r : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hm : ⁅Z Rg c,Z Rg w⁆ ≤ Z Rg (alpha Rg)) :
      ⁅Y,Z Rg w⁆ ≤ Z Rg (alpha Rg) := by
    apply commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      (Z Rg c) (Z Rg (alpha Rg)) (Z Rg w) (Z Rg (alpha Rg))
      (Z_normalized Rg _) (hZV.trans ((sourceGeometry h).V_local _ rfl hb))
      (Z_le_stabilizer Rg _) hm
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
        (sourceDistance_pos h) r.critical).trans (Z_normalized Rg _))
  have hpY := hmove p hcomm
  have hqY := hmove q hcomm'
  have hYN : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen,plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat]
    refine sup_le (sup_le ?_ (le_normalizer_iff_commutator_le_left.mpr
      (hpY.trans le_sup_right))) (le_normalizer_iff_commutator_le_left.mpr
        (hqY.trans le_sup_right))
    exact (le_inf ((show Q Rg t ≤ stabilizer Rg c from
      fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans (Z_normalized Rg c))
      ((show Q Rg t ≤ stabilizer Rg (alpha Rg) from
        fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans (Z_normalized Rg _))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hUB : U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    (DistanceEight.U_le_Z Rg c).trans (le_sup_left.trans
      (normalized_radius_le_slice_of_critical_commutator h e hz hb p Y
        (sup_le hZV (Z_le_VBall Rg _ 2)) hYN hpY))
  have hi := relIndex_eq_one.mpr hUB
  omega

include h e hz hk in
/-- Apply the paired-kernel comparison to the original normalized selectors
and the same transported strict slice. Either actual backward walk is built
with every overlap vertex, or their full reverse-kernel commutators cannot
fit in one line. The original component switch and both generation identities
are retained. -/
theorem plane_small_critical_backward_separation
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hd : Adjacent Rg delta (p.walk.getVert 1))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta)) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
      let x := (embedM Rg r)⁻¹
      ∃ q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4 ∧
        (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ∧
        ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
          let c := act Rg g delta
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ∧
          ((∃ b : CriticalPath Rg (sourceGeometry h) c (p.walk.getVert (p.walk.length-2)),
              b.walk.getVert 1 = t ∧
              ∀ i ≤ p.walk.length-2, b.walk.getVert (i+2) = p.walk.getVert i) ∨
           (∃ b : CriticalPath Rg (sourceGeometry h) c (q.walk.getVert (q.walk.length-2)),
              b.walk.getVert 1 = t ∧
              ∀ i ≤ q.walk.length-2, b.walk.getVert (i+2) = q.walk.getVert i) ∨
           (Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) ∧
            Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2)) ∧
            (∀ a : Vertex Rg, color Rg a = false →
              (X Rg a = U Rg a ⊔
                (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))) ∧
              X Rg a = Z Rg a) ∧
            let A := X Rg z ⊓ Q Rg (alpha Rg)
            let A' := X Rg (act Rg x z) ⊓ Q Rg (alpha Rg)
            let H := ⁅A,Z Rg c⁆
            let H' := ⁅A',Z Rg c⁆
            ⁅A ⊔ A',Z Rg c⁆ = H ⊔ H' ∧
              H ⊔ H' ≤ Z Rg t ∧ ⁅H ⊔ H',Q Rg t⁆ = ⊥ ∧
              2 < Nat.card (H ⊔ H' : Subgroup (FreeAmalgam Rg)) ∧
              (Nat.card H ≤ 2 → ¬ H' ≤ H) ∧
              (Nat.card H' ≤ 2 → ¬ H ≤ H'))) := by
  obtain ⟨t,hat,r,hr,q,hqverts,hqs,hgen,hpair,hnorm,hinside,_,_,_,_,_,_,_,htransport⟩ :=
    remaining_small_critical_paired_kernel_selectors h e hz hk u (Or.inl hR) p hp
  obtain ⟨g,hg,hgt,hstrict,_⟩ := htransport delta hd hs
  let c := act Rg g delta
  have hct : Adjacent Rg c t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g _ _).mpr hd
  have hc : color Rg c = false := by
    have h₁ := adjacent_color_ne Rg hat
    have h₂ := adjacent_color_ne Rg hct
    change false ≠ color Rg t at h₁
    cases he : color Rg c <;> cases he' : color Rg t <;> simp_all
  have hb := distance_gt_two h e hz hk
  have extend (w : Vertex Rg) (s : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hn : ¬ Z Rg c ≤ Q Rg (s.walk.getVert (s.walk.length-2))) :
      ∃ b : CriticalPath Rg (sourceGeometry h) c (s.walk.getVert (s.walk.length-2)),
        b.walk.getVert 1 = t ∧ ∀ i ≤ s.walk.length-2, b.walk.getVert (i+2) = s.walk.getVert i := by
    let v : (cosetGraph Rg).Walk c (alpha Rg) :=
      .cons ((cosetGraph_adj Rg _ _).mpr hct)
        (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
    have hv : v.length = 2 := rfl
    let b := s.prepend_two (Nat.le_of_lt hb) hc v hv hn
    refine ⟨b,?_,fun i hi => s.prepend_two_overlap _ _ _ _ _ hi⟩
    simp only [b,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hv,show 1<2 from by decide,ite_true,v,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  refine ⟨t,hat,r,hr,q,hqverts,hqs,hgen,hpair,hnorm,hinside,g,hg,hgt,hstrict,?_⟩
  by_cases hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2))
  · by_cases hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2))
    · right; right
      exact ⟨hbad,hbad',plane_paired_trapped_omega_generation h e hz hk u hR
        p q hp hqs hat hct hgen hbad hbad' hstrict,
        plane_paired_trapped_commutator_comparison h e hz hk u hR
        p q hp hqs hat hct hgen hbad hbad' hstrict⟩
    · exact Or.inr (Or.inl (extend _ q hbad'))
  · exact Or.inl (extend _ p hbad)

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
