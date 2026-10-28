module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.ForwardLines
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicLargeClosure
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSliceShift
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicForwardClosure
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FullSeed
import all Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits

/-!
# Shifted whole-seed control for the original Borel graph

The forward line is central at the start for both critical image sizes.
Normal generation identifies the whole selected span's kernel commutator
with that line. On an actual overlapping forward path a single residual
conjugator produces the source shifted line and span. Above distance four
the span fixes both inner layers, lies in the old endpoint two-core, and
the old endpoint seed lies in the shifted center two-core. Both complete
centralizer orbits lie in that old endpoint core, and both shifted critical
images have order two, by choosing a controlled restricted actor.

The proof retains the whole Baumann slice, both moving covers, and the
original cubic projection. These are the first shifted-control steps of
MS93 (5.9), pp.920--921, adapted from CubicLargeClosure to the Borel
inclusion proved in ForwardLines. The strict-slice contradiction and
terminal distance exclusions remain open.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
open Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "π" => CubicAction.projection h e hz hk
local notation "Rg" => edge L R

include h e hz hk in
/-- Normal generation identifies the entire selected span commutator with
the forward line for both critical image sizes. -/
theorem borel_selected_span_forward_commutator
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (u : S6) (hfull : (Rg).map π = Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
    let T := Q Rg (alpha Rg) ⊓ centralizer
      (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
        ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
    let H := ⁅U Rg (p.walk.getVert 2),Q Rg (alpha Rg) ⊓ centralizer
      (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
        ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))⁆
    ⁅P,T⁆ = H ∧ ⁅P,P⁆ ≤ H ∧
      H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q Rg (alpha Rg) ⊓ centralizer
    (U Rg c ⊓ B Rg (alpha Rg)
      ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
  let H := ⁅U Rg c,T⁆
  let P := localZSpan Rg c (alpha Rg)
  have hfixed : H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
    borel_forward_line_central h e hz hk hb p u hfull hslice
  have hHN : stabilizer Rg (alpha Rg) ≤ normalizer (H : Set (FreeAmalgam Rg)) :=
    (le_centralizer_iff.mp hfixed).trans (Subgroup.centralizer_le_normalizer _)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hTQt : T ≤ Q Rg t := inf_le_left.trans (Q_le_adjacent_h Rg ht hat)
  have hseed : Z Rg t ≤ centralizer (T : Set (FreeAmalgam Rg)) := by
    intro z hz x hx
    rw [Z,if_neg (by simp [ht])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2 x (hTQt hx)
  have hTN : stabilizer Rg (alpha Rg) ≤ normalizer (T : Set (FreeAmalgam Rg)) :=
    selected_forward_kernel_normalized (h := h) hb rfl hat hct
  have hZcG : Z Rg c ≤ stabilizer Rg (alpha Rg) :=
    ((Z_le_localZSpan Rg c (alpha Rg)).trans (localZSpan_le_V Rg (by
      rw [SimpleGraph.dist_comm,p.dist_start (by omega)]))).trans
      ((sourceGeometry h).V_local _ rfl hb)
  have hZc : ⁅Z Rg c,T⁆ ≤ H := by
    rw [vertex_seed_eq_moving_sup_edge h e hz hcol hct]
    apply commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      _ _ T _ hHN ((DistanceEight.U_le_Z Rg c).trans hZcG)
      ((adjacent_Z_le Rg rfl hat).trans (Z_le_stabilizer Rg _)) le_rfl
    exact (commutator_eq_bot_iff_le_centralizer.mpr hseed).le.trans bot_le
  have hPT : ⁅P,T⁆ ≤ H := by
    dsimp only [P]
    rw [localZSpan_eq_conjugates]
    apply commutator_iSup_le_of_relative_normal (stabilizer Rg (alpha Rg)) T _ _ hHN
    · intro g
      have hgmap : (stabilizer Rg (alpha Rg)).map
          (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom = stabilizer Rg (alpha Rg) :=
        mem_normalizer_iff_map_conj_eq.mp ((stabilizer Rg (alpha Rg)).le_normalizer
          ((stabilizer Rg (alpha Rg)).inv_mem g.property))
      exact (map_mono hZcG).trans_eq hgmap
    · intro g
      have hm := map_mono (f := (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom) hZc
      have hTm : T.map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom = T :=
        mem_normalizer_iff_map_conj_eq.mp (hTN ((stabilizer Rg (alpha Rg)).inv_mem g.property))
      have hHm : H.map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom = H :=
        mem_normalizer_iff_map_conj_eq.mp (hHN ((stabilizer Rg (alpha Rg)).inv_mem g.property))
      rwa [map_commutator,hTm,hHm] at hm
  have hPP : ⁅P,P⁆ ≤ H :=
    (commutator_mono le_rfl (selected_span_le_forward_kernel (h := h) hb p)).trans hPT
  exact ⟨le_antisymm hPT (commutator_mono
    ((DistanceEight.U_le_Z Rg c).trans (Z_le_localZSpan Rg _ _)) le_rfl),hPP,hfixed⟩
include h e hz hk in
/-- Forward radius escape supplies a critical path with the literal initial overlap. -/
private theorem borel_forward_critical_path
    (hb : 2 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π = Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a') :
    ∃ z, ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) z,
      ∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2) := by
  have hl : 2 ≤ p.walk.length := by have he := p.length_eq_b; change p.walk.length = sourceDistance h at he; omega
  let rev : CriticalPath Rg (sourceGeometry h) a' a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        a p.start_color (by
          rw [(sourceGeometry h).distance_constant a p.start_color]
          exact sourceDistance_pos h) a' p.end_color p.critical⟩
  have hend : rev.walk.getVert (rev.walk.length-2) = p.walk.getVert 2 := by
    change p.walk.reverse.getVert (p.walk.reverse.length-2) = _
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,Nat.sub_sub_self hl]
  have hs : ∃ z, ∃ q : CriticalPath Rg (sourceGeometry h) z
      (rev.walk.getVert (rev.walk.length-2)),
      ∀ i ≤ rev.walk.length-2, q.walk.getVert (i+2) = rev.walk.getVert i := by
    obtain ⟨z,w,q,hw,hq,hover⟩ := (borel_critical_paths h e hz hk u hfull rev).2.1
    exact ⟨z,q,hover⟩
  rw [hend] at hs
  obtain ⟨z,q,hover⟩ := hs
  let fwd : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) z :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        _ q.start_color (by
          rw [(sourceGeometry h).distance_constant _ q.start_color]
          exact sourceDistance_pos h) _ q.end_color q.critical⟩
  have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
  refine ⟨z,fwd,?_⟩
  intro i hi
  change q.walk.reverse.getVert i = _
  rw [SimpleGraph.Walk.getVert_reverse,hlen]
  have hi' : p.walk.length-i = (p.walk.length-i-2)+2 := by omega
  rw [hi',hover (p.walk.length-i-2) (by
    change p.walk.length-i-2 ≤ p.walk.reverse.length-2
    rw [SimpleGraph.Walk.length_reverse]
    omega)]
  change p.walk.reverse.getVert (p.walk.length-i-2) = _
  rw [SimpleGraph.Walk.getVert_reverse]
  congr 1
  omega

include h e hz hk in
/-- Radius escape and the marked cover construct equation (**) of (5.9).
No independent displacement or generating-centralizer premise is assumed. -/
private theorem borel_exists_slice_shift
    (hb : 2 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π = Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    Nonempty (SmallSliceShift h p) := by
  obtain ⟨z,q,hover⟩ := borel_forward_critical_path h e hz hk hb u hfull p
  have hline := forward_slice_noncentral_line h e hz hk hb p hslice heligible
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hTG : forwardSliceKernel h (alpha Rg) c ≤ stabilizer Rg c :=
    (inf_le_left.trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hHU : forwardSliceLine h (alpha Rg) c ≤ U Rg c :=
    le_normalizer_iff_commutator_le_left.mp (hTG.trans (U_normalized c))
  obtain ⟨g,hg,hgen,hmove⟩ := exists_cover_line_generator h e hz hk q
    (forwardSliceLine h (alpha Rg) c) hHU hline.1 hline.2.2
  exact ⟨⟨z,q,hover,g,hg,hgen,hmove⟩⟩
end AlternatingSixReconstruction.Exceptional.OriginalSylow
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open AlternatingSixReconstruction.Exceptional.OriginalSylow
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "π" => CubicAction.projection h e hz hk
local notation "Rg" => edge L R

namespace SmallSliceShift
variable {h} {a' : Vertex (edge L R)}
  {p : CriticalPath (edge L R) (sourceGeometry h) (alpha (edge L R)) a'}
  (s : SmallSliceShift h p)

include e hz hk in
/-- The original Borel argument transports the span commutator without
a small-critical-image assumption. -/
theorem borel_span_commutator
    (hb : 2 < sourceDistance h) (u : S6)
    (hfull : (Rg).map π = Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) : ⁅s.span,s.kernel⁆ = s.line := by
  have hh := congrArg (Subgroup.map (MulAut.conj s.conjugator).toMonoidHom)
    (borel_selected_span_forward_commutator h e hz hk hb p u hfull hslice).1
  rw [map_commutator,←s.span_map] at hh
  exact hh

include e hz hk in
/-- The shifted line has order two and is central at its own center
for both critical image sizes. -/
theorem borel_line_facts
    (hb : 2 < sourceDistance h) (u : S6)
    (hfull : (Rg).map π = Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    Nat.card s.line = 2 ∧
      s.line ≤ centralizer (stabilizer Rg s.centerVertex : Set (FreeAmalgam Rg)) := by
  have hel := (borel_critical_paths h e hz hk u hfull p).2.2.2
  have hh := forward_slice_noncentral_line h e hz hk hb p hslice hel
  refine ⟨(card_map_of_injective (MulAut.conj s.conjugator).injective).trans hh.1,?_⟩
  have hm := map_mono (f := (MulAut.conj s.conjugator).toMonoidHom)
    (borel_forward_line_central h e hz hk hb p u hfull hslice)
  rw [Theory.GroupTheory.map_centralizer_equiv,
    show (MulAut.conj s.conjugator : FreeAmalgam Rg → FreeAmalgam Rg) =
      (MulAut.conj s.conjugator).toMonoidHom from rfl,←Subgroup.coe_map] at hm
  have he := stabilizer_act Rg s.conjugator⁻¹ (alpha Rg)
  rw [inv_inv] at he
  rwa [←he] at hm

include e hz hk in
/-- The shifted span fixes the predecessor seed and full reverse kernel,
with its predecessor-core placement retained. -/
theorem borel_inner_control (hb : 4 < sourceDistance h)
    (u : S6) (hfull : (Rg).map π = Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
:
    s.span ≤ Q Rg (p.walk.getVert (p.walk.length-2)) ∧
      s.span ≤ stabilizer Rg a' ∧
      ⁅s.span,Z Rg (p.walk.getVert (p.walk.length-2)) ⊔ (Z Rg a' ⊓ Q Rg s.centerVertex)⁆ = ⊥ := by
  have hcard := (s.borel_line_facts e hz hk (by omega) u hfull hslice).1
  have hcomm := s.borel_span_commutator e hz hk (by omega) u hfull hslice
  have hinner := s.inner_le_kernel hb
  have hkill (D : Subgroup (FreeAmalgam Rg)) (hD : D ≤ s.line)
      (hDZ : D ≤ centralizer (Z Rg s.endpoint : Set (FreeAmalgam Rg))) : D = ⊥ := by
    by_contra hn
    have hfinite : Finite s.line := Nat.finite_of_card_ne_zero (by omega)
    let := hfinite
    let : Finite D := Finite.of_injective (inclusion hD) (inclusion_injective _)
    have hp := (one_lt_card_iff_ne_bot D).mpr hn
    have he : D = s.line := eq_of_le_of_card_ge hD (by omega)
    apply s.moves
    change s.line ≤ _
    rwa [he] at hDZ
  have hpre : ⁅s.span,Z Rg (p.walk.getVert (p.walk.length-2))⁆ = ⊥ := by
    apply hkill _ ((commutator_mono le_rfl (le_sup_left.trans hinner)).trans_eq hcomm)
    exact (le_normalizer_iff_commutator_le_right.mp
      ((s.span_le_predecessor_stabilizer hb).trans (Z_normalized Rg _))).trans
        (le_sup_left.trans (s.inner_seed_centralizes_endpoint hb))
  have hpreQ : s.span ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    apply two_subgroup_seed_centralizer_le_core h e hz (predecessor_color (h := h) (p := p)) s.span
      ((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le
        s.centerVertex s.center_color).to_le (s.span_le_core (by omega)))
    exact le_inf (s.span_le_predecessor_stabilizer hb) (commutator_eq_bot_iff_le_centralizer.mp hpre)
  have hGe : s.span ≤ stabilizer Rg a' := by
    have hl : 4 < p.walk.length := p.length_eq_b ▸ hb
    let t := p.walk.getVert (p.walk.length-1)
    have hta : Adjacent Rg a' t := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
      rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
      exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
    have hpt : Adjacent Rg (p.walk.getVert (p.walk.length-2)) t := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
      rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
      exact (cosetGraph_adj Rg _ _).mp hh
    have ht : color Rg t = true := by
      have hh := adjacent_color_ne Rg hta
      rw [p.end_color] at hh
      cases he : color Rg t <;> simp_all
    exact (hpreQ.trans (Q_le_adjacent_h Rg ht hpt)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hta))
  have hK : ⁅s.span,Z Rg a' ⊓ Q Rg s.centerVertex⁆ = ⊥ := by
    apply hkill _ ((commutator_mono le_rfl (le_sup_right.trans hinner)).trans_eq hcomm)
    exact ((commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp (hGe.trans (Z_normalized Rg a')))).trans
        (le_sup_right.trans (s.inner_seed_centralizes_endpoint hb))
  refine ⟨hpreQ,hGe,commutator_eq_bot_iff_le_centralizer.mpr ?_⟩
  apply le_centralizer_iff.mpr
  exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hpre))
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hK))

include e hz hk in
/-- The shifted center is either critical with the old endpoint, or the
entire shifted span lies in that endpoint's two-core. -/
theorem borel_old_endpoint_alternative (hb : 4 < sourceDistance h)
    (u : S6) (hfull : (Rg).map π = Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
:
    CriticalPair Rg s.centerVertex a' ((sourceGeometry h).exists_critical _ s.center_color) ∨
      (Z Rg a' ≤ Q Rg s.centerVertex ∧ s.span ≤ Q Rg a') := by
  have hi := s.borel_inner_control e hz hk hb u hfull hslice
  by_cases he : Z Rg a' ≤ Q Rg s.centerVertex
  · refine Or.inr ⟨he,?_⟩
    apply two_subgroup_seed_centralizer_le_core h e hz p.end_color s.span
      ((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le
        s.centerVertex s.center_color).to_le (s.span_le_core (by omega)))
    refine le_inf hi.2.1 ?_
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    apply (commutator_mono le_rfl (show Z Rg a' ≤
      Z Rg (p.walk.getVert (p.walk.length-2)) ⊔ (Z Rg a' ⊓ Q Rg s.centerVertex) from
        (le_inf le_rfl he).trans le_sup_right)).trans_eq hi.2.2
  · have hd : (cosetGraph Rg).dist a' s.centerVertex ≤ sourceDistance h := by
      have hh := (cosetGraph_connected Rg).dist_triangle (u := s.centerVertex)
        (v := p.walk.getVert 2) (w := a')
      rw [s.center_distance (by omega),p.dist_end] at hh
      rw [SimpleGraph.dist_comm]
      have hl : p.walk.length = sourceDistance h := p.length_eq_b
      omega
    have hlo := criticalDistance_le Rg a' ((sourceGeometry h).exists_critical _ p.end_color) he
    have hc : CriticalPair Rg a' s.centerVertex ((sourceGeometry h).exists_critical _ p.end_color) := by
      refine ⟨?_,he⟩
      rw [(sourceGeometry h).distance_constant _ p.end_color] at hlo ⊢
      exact le_antisymm hd hlo
    exact Or.inl (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      a' p.end_color (by
        rw [(sourceGeometry h).distance_constant _ p.end_color]
        exact sourceDistance_pos h) s.centerVertex s.center_color hc)
include e hz hk in
theorem borel_not_critical_old_endpoint (hb : 4 < sourceDistance h)
    (u : S6) (hfull : (Rg).map π = Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    ¬ CriticalPair Rg s.centerVertex a' ((sourceGeometry h).exists_critical _ s.center_color) := by
  intro hc
  let q : CriticalPath Rg (sourceGeometry h) s.centerVertex a' :=
    CriticalPath.ofPair s.center_color hc
  have hi := s.borel_inner_control e hz hk hb u hfull hslice
  have hDV : s.span ≤ V Rg s.centerVertex := by
    apply localZSpan_le_V
    rw [SimpleGraph.dist_comm]
    change (cosetGraph Rg).dist (act Rg s.conjugator⁻¹ (alpha Rg)) (p.walk.getVert 2) ≤ 2
    rw [←s.fixes_second,dist_act]
    rw [p.dist_start (by have hl : p.walk.length = sourceDistance h := p.length_eq_b; omega)]
  have hfix : s.span ≤ centralizer (Z Rg a' ⊓ Q Rg s.centerVertex : Set (FreeAmalgam Rg)) := by
    intro x hx z hz
    have hz' : z ∈ (Z Rg (p.walk.getVert (p.walk.length-2)) ⊔
        (Z Rg a' ⊓ Q Rg s.centerVertex) : Subgroup (FreeAmalgam Rg)) :=
      Subgroup.mem_sup_right hz
    exact (commutator_eq_bot_iff_le_centralizer.mp hi.2.2) hx z hz'
  exact s.span_not_le_slice (by omega) heligible
    (critical_kernel_normal_radius_le_slice h e hz hk (by omega) q s.span hDV
      (localZSpan_normalized Rg _ _) hi.2.1 hfix)

include e hz hk in
/-- The entire shifted span lies in the old endpoint's two-core, with the
full old endpoint seed in the shifted center's two-core. This discharges
the critical-pair alternative in the saved (5.9) shift. -/
theorem borel_old_endpoint_core (hb : 4 < sourceDistance h)
    (u : S6) (hfull : (Rg).map π = Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    Z Rg a' ≤ Q Rg s.centerVertex ∧ s.span ≤ Q Rg a' :=
  (s.borel_old_endpoint_alternative e hz hk hb u hfull hslice).resolve_left
    (s.borel_not_critical_old_endpoint e hz hk hb u hfull hslice heligible)

include e hz hk in
private theorem borel_conjugated_span_le_old_endpoint_core
    (hb : 4 < sourceDistance h)
    (u : S6) (hfull : (Rg).map π = Theory.SpecificGroups.SymmetricSix.borel.map
      (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    (y : FreeAmalgam Rg) (hy : y ∈ stabilizer Rg (p.walk.getVert 2))
    (hline : (forwardSliceLine h (alpha Rg) (p.walk.getVert 2)).map
      (MulAut.conj y).toMonoidHom = s.line) :
    Z Rg (act Rg y⁻¹ (alpha Rg)) ≤ Q Rg a' ∧
      (localZSpan Rg (p.walk.getVert 2) (alpha Rg)).map
        (MulAut.conj y).toMonoidHom ≤ Q Rg a' := by
  let a := act Rg y⁻¹ (alpha Rg)
  let c := p.walk.getVert 2
  let v := p.walk.getVert (p.walk.length-2)
  let f := (MulAut.conj y).toMonoidHom
  let Y := (localZSpan Rg c (alpha Rg)).map f
  let T := (forwardSliceKernel h (alpha Rg) c).map f
  have hb2 : 2 < sourceDistance h := by omega
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have ha : color Rg a = false := action_preserves_color Rg y⁻¹ (alpha Rg)
  have hc : color Rg c = false := s.path.start_color
  have hv : color Rg v = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    omega
  have hfix : act Rg y⁻¹ c = c := (stabilizer Rg c).inv_mem hy
  have hac : (cosetGraph Rg).dist a c = 2 := by
    change (cosetGraph Rg).dist (act Rg y⁻¹ (alpha Rg)) c = 2
    rw [←hfix,dist_act]
    exact p.dist_start (by omega)
  have hcv : (cosetGraph Rg).dist c v ≤ p.walk.length-4 := by
    have hh := SimpleGraph.dist_le ((p.walk.drop 2).take (p.walk.length-4))
    rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
      inf_eq_left.mpr (by omega : p.walk.length-4 ≤ p.walk.length-2),
      SimpleGraph.Walk.drop_getVert,
      show 2+(p.walk.length-4)=p.walk.length-2 by omega] at hh
    exact hh
  have hav : (cosetGraph Rg).dist a v ≤ sourceDistance h-2 := by
    have hh := (cosetGraph_connected Rg).dist_triangle (u := a) (v := c) (w := v)
    omega
  have hae : (cosetGraph Rg).dist a a' ≤ sourceDistance h := by
    have hh := (cosetGraph_connected Rg).dist_triangle (u := a) (v := c) (w := a')
    have hce : (cosetGraph Rg).dist c a' = p.walk.length-2 := p.dist_end 2
    omega
  have hYV : Y ≤ V Rg a := by
    have hh : localZSpan Rg c (alpha Rg) ≤ V Rg (alpha Rg) :=
      localZSpan_le_V Rg (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
    change Y ≤ V Rg (act Rg y⁻¹ (alpha Rg))
    rw [V_act,inv_inv]
    exact map_mono hh
  have hYQ := hYV.trans ((sourceGeometry h).V_le_Q hb2 a ha)
  have hYtwo : IsPGroup 2 Y :=
    (Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le a ha).to_le hYQ
  have hYN : stabilizer Rg a ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [stabilizer_act,inv_inv]
    exact (map_mono (localZSpan_normalized Rg c (alpha Rg))).trans
      (le_normalizer_map f)
  have hB := Escape.PairingControl.FirstPairing.B_act
    (geometry := sourceGeometry h) hb2 y⁻¹ (alpha Rg) rfl
  rw [inv_inv] at hB
  have hYB : ¬ Y ≤ B Rg a ((sourceGeometry h).Z_normal _) := by
    intro hh
    rw [hB] at hh
    have hh' := (map_le_map_iff_of_injective (MulAut.conj y).injective).mp hh
    exact heligible ((DistanceEight.U_le_Z Rg c).trans ((Z_le_localZSpan Rg c _).trans hh'))
  have hT : T = forwardSliceKernel h a c := by
    have hU : (U Rg c).map f = U Rg c :=
      mem_normalizer_iff_map_conj_eq.mp (U_normalized c hy)
    have hUB : (U Rg c ⊓ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map f =
        U Rg c ⊓ B Rg a ((sourceGeometry h).Z_normal _) := by
      rw [map_inf _ _ f (MulAut.conj y).injective,hU,←hB]
    have hm := map_inf_centralizer_of_injective f (MulAut.conj y).injective
      (Q Rg (alpha Rg)) (U Rg c ⊓ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    have hQ : (Q Rg (alpha Rg)).map f = Q Rg a := by
      simpa only [inv_inv] using (Q_act Rg y⁻¹ (alpha Rg)).symm
    rw [hUB,hQ] at hm
    simpa only [forwardSliceKernel,Q_act,inv_inv,coe_inf,Set.inf_eq_inter,T,f] using hm.symm
  have hcomm : ⁅Y,T⁆ = s.line := by
    have hh := congrArg (Subgroup.map f)
      (borel_selected_span_forward_commutator h e hz hk hb2 p u hfull hslice).1
    rw [map_commutator] at hh
    exact hh.trans hline
  have hvQc : Z Rg v ≤ Q Rg c := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ hv)
    rw [(sourceGeometry h).distance_constant _ hv,SimpleGraph.dist_comm]
    change (cosetGraph Rg).dist c v < sourceDistance h
    omega
  have heQc : Z Rg a' ≤ Q Rg c := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.end_color)
    rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end]
    change p.walk.length-2 < sourceDistance h
    omega
  have hvQa : Z Rg v ≤ Q Rg a := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ hv)
    rw [(sourceGeometry h).distance_constant _ hv,SimpleGraph.dist_comm]
    change (cosetGraph Rg).dist a v < sourceDistance h
    omega
  have hQcC : Q Rg c ≤ centralizer
      (U Rg c ⊓ B Rg a ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg c hc))).trans
      (centralizer_le (inf_le_left.trans (DistanceEight.U_le_Z Rg c)))
  have hinner : Z Rg v ⊔ (Z Rg a' ⊓ Q Rg a) ≤ T := by
    rw [hT]
    exact le_inf (sup_le hvQa inf_le_right)
      ((sup_le hvQc (inf_le_left.trans heQc)).trans hQcC)
  have hez : (cosetGraph Rg).dist a' s.endpoint = 2 := by
    have hh := s.path.dist_end (p.walk.length-2)
    have hlen : s.path.walk.length = sourceDistance h := s.path.length_eq_b
    rw [s.overlap _ (Nat.le_refl _),show p.walk.length-2+2=p.walk.length by omega,
      p.walk.getVert_length,hlen] at hh
    exact hh.trans (by omega)
  have hvz : (cosetGraph Rg).dist v s.endpoint ≤ 4 := by
    have hh := (cosetGraph_connected Rg).dist_triangle (u := v) (v := a') (w := s.endpoint)
    have hve : (cosetGraph Rg).dist v a' = 2 := by
      change (cosetGraph Rg).dist (p.walk.getVert (p.walk.length-2)) a' = 2
      rw [p.dist_end]
      omega
    omega
  have hZz (w : Vertex Rg) (hw : color Rg w = false)
      (hd : (cosetGraph Rg).dist w s.endpoint < sourceDistance h) :
      Z Rg w ≤ centralizer (Z Rg s.endpoint : Set (FreeAmalgam Rg)) := by
    apply le_trans _ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg _ s.path.end_color)))
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ hw)
    rwa [(sourceGeometry h).distance_constant _ hw]
  have hvC := hZz v hv (lt_of_le_of_lt hvz hb)
  have heC := hZz a' p.end_color (hez.symm ▸ hb2)
  have hcard := (s.borel_line_facts e hz hk hb2 u hfull hslice).1
  let : Finite s.line := Nat.finite_of_card_ne_zero (by omega)
  have hkill (D : Subgroup (FreeAmalgam Rg)) (hD : D ≤ s.line)
      (hDC : D ≤ centralizer (Z Rg s.endpoint : Set (FreeAmalgam Rg))) : D = ⊥ := by
    by_contra hn
    let : Finite D := Finite.of_injective (inclusion hD) (inclusion_injective _)
    have hp := (one_lt_card_iff_ne_bot D).mpr hn
    have he : D = s.line := eq_of_le_of_card_ge hD (by omega)
    apply s.moves
    change s.line ≤ _
    rwa [he] at hDC
  have hYGv : Y ≤ stabilizer Rg v := by
    apply hYV.trans
    apply (V_le_iff Rg ha _).mpr
    intro w hw hd
    apply Z_le_stabilizer_of_dist_le w ((sourceGeometry h).exists_critical w hw)
    rw [(sourceGeometry h).distance_constant w hw]
    have hh := (cosetGraph_connected Rg).dist_triangle (u := w) (v := a) (w := v)
    change (cosetGraph Rg).dist w v ≤ sourceDistance h
    omega
  have hYv : ⁅Y,Z Rg v⁆ = ⊥ :=
    hkill _ ((commutator_mono le_rfl (le_sup_left.trans hinner)).trans_eq hcomm)
      ((le_normalizer_iff_commutator_le_right.mp (hYGv.trans (Z_normalized Rg v))).trans hvC)
  have hYQv : Y ≤ Q Rg v := two_subgroup_seed_centralizer_le_core h e hz hv Y hYtwo
    (le_inf hYGv (commutator_eq_bot_iff_le_centralizer.mp hYv))
  have hYGe : Y ≤ stabilizer Rg a' := by
    let t := p.walk.getVert (p.walk.length-1)
    have het : Adjacent Rg a' t := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
      rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
      exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
    have hvt : Adjacent Rg v t := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
      rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
      exact (cosetGraph_adj Rg _ _).mp hh
    have ht : color Rg t = true := by
      have hh := adjacent_color_ne Rg het
      rw [p.end_color] at hh
      cases he : color Rg t <;> simp_all
    exact (hYQv.trans (Q_le_adjacent_h Rg ht hvt)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg het))
  have hYK : ⁅Y,Z Rg a' ⊓ Q Rg a⁆ = ⊥ :=
    hkill _ ((commutator_mono le_rfl (le_sup_right.trans hinner)).trans_eq hcomm)
      (((commutator_mono le_rfl inf_le_left).trans
        (le_normalizer_iff_commutator_le_right.mp (hYGe.trans (Z_normalized Rg a')))).trans heC)
  have heQa : Z Rg a' ≤ Q Rg a := by
    by_contra hn
    have hlo := criticalDistance_le Rg a' ((sourceGeometry h).exists_critical _ p.end_color) hn
    rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm] at hlo
    have hp : CriticalPair Rg a' a ((sourceGeometry h).exists_critical _ p.end_color) := by
      refine ⟨?_,hn⟩
      rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm]
      exact le_antisymm hae hlo
    let q : CriticalPath Rg (sourceGeometry h) a a' := CriticalPath.ofPair ha
      (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) a' p.end_color
        (by rw [(sourceGeometry h).distance_constant _ p.end_color]; exact sourceDistance_pos h) a ha hp)
    exact hYB (critical_kernel_normal_radius_le_slice h e hz hk hb2 q Y hYV hYN hYGe
      (commutator_eq_bot_iff_le_centralizer.mp hYK))
  have hYe : ⁅Y,Z Rg a'⁆ = ⊥ := by
    simpa only [inf_eq_left.mpr heQa] using hYK
  have hYQe := two_subgroup_seed_centralizer_le_core h e hz p.end_color Y hYtwo
    (le_inf hYGe (commutator_eq_bot_iff_le_centralizer.mp hYe))
  refine ⟨?_,hYQe⟩
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a ha
  apply two_subgroup_seed_centralizer_le_core h e hz p.end_color (Z Rg a)
    (IsElementaryAbelian.isPGroup 2 _)
  refine le_inf ?_ ?_
  · apply Z_le_stabilizer_of_dist_le a ((sourceGeometry h).exists_critical _ ha)
    rwa [(sourceGeometry h).distance_constant _ ha]
  · exact (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a ha)).trans
      (centralizer_le heQa)

include e hz hk in
/-- Both complete centralizer orbits lie in the old endpoint's two-core.
The conjugator ranges over the whole line centralizer, not only its residual. -/
theorem borel_centralizer_orbits_le_old_endpoint_core
    (hb : 4 < sourceDistance h)
    (u : S6) (hfull : (Rg).map π = Theory.SpecificGroups.SymmetricSix.borel.map
      (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    s.seedOrbit ≤ Q Rg a' ∧ s.spanOrbit ≤ Q Rg a' := by
  have hmap (A : Subgroup (FreeAmalgam Rg)) (x : FreeAmalgam Rg) :
      (A.map (MulAut.conj s.conjugator).toMonoidHom).map (MulAut.conj x).toMonoidHom =
        A.map (MulAut.conj (x*s.conjugator)).toMonoidHom := by
    rw [map_map]
    congr 1
    apply MonoidHom.ext
    intro z
    change x*(s.conjugator*z*s.conjugator⁻¹)*x⁻¹ =
      (x*s.conjugator)*z*(x*s.conjugator)⁻¹
    group
  have hconj (x : s.lineCentralizer) :
      (Z Rg s.centerVertex).map (MulAut.conj (x : FreeAmalgam Rg)).toMonoidHom ≤ Q Rg a' ∧
      s.span.map (MulAut.conj (x : FreeAmalgam Rg)).toMonoidHom ≤ Q Rg a' := by
    have hxH : s.line.map (MulAut.conj (x : FreeAmalgam Rg)).toMonoidHom = s.line :=
      mem_normalizer_iff_map_conj_eq.mp ((Subgroup.centralizer_le_normalizer _) x.property.2)
    have hxy : (x : FreeAmalgam Rg)*s.conjugator ∈ stabilizer Rg (p.walk.getVert 2) :=
      (stabilizer Rg _).mul_mem x.property.1 (Ltilde_le_stabilizer _ s.residual)
    have hh := s.borel_conjugated_span_le_old_endpoint_core e hz hk hb u hfull hslice heligible
      ((x : FreeAmalgam Rg)*s.conjugator) hxy (by rw [←hmap]; exact hxH)
    rw [centerVertex,Z_act,inv_inv,hmap,s.span_map,hmap]
    simpa only [Z_act,inv_inv] using hh
  constructor
  · rw [seedOrbit,conjugateSpanBy_eq_iSup_conj]
    exact iSup_le (fun x => (hconj x).1)
  · rw [spanOrbit,conjugateSpanBy_eq_iSup_conj]
    exact iSup_le (fun x => (hconj x).2)

include e hz hk in
/-- Both shifted critical images have order two, for either entire cover.
If a shifted image were large, choose the shift using its controlled
restricted actor. Its centralizer orbit would then be a normal radius
subgroup modulo the seed and lie in the forbidden Baumann slice. -/
theorem borel_shifted_indices
    (hb : 4 < sourceDistance h)
    (u : S6) (hfull : (Rg).map π = Theory.SpecificGroups.SymmetricSix.borel.map
      (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) = 2 ∧
      (Q Rg (p.walk.getVert 2)).relIndex (Z Rg s.endpoint) = 2 := by
  have hb2 : 2 < sourceDistance h := by omega
  apply small_critical_indices h e hz hk s.path
  by_contra hn
  have hlarge : 4 ≤ (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) := by omega
  obtain ⟨A,hAU,hAn,hcontrol⟩ := large_critical_restricted_actor h e hz hk s.path hlarge
  let c := p.walk.getVert 2
  let v := s.path.walk.getVert (s.path.walk.length-2)
  let t := p.walk.getVert 1
  have hc : color Rg c = false := s.path.start_color
  have hAZ : A ≤ Z Rg s.endpoint := hAU.trans (DistanceEight.U_le_Z Rg s.endpoint)
  have hEC : Z Rg s.endpoint ≤ stabilizer Rg c :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) c hc
      (by rw [(sourceGeometry h).distance_constant c hc]; exact sourceDistance_pos h)
      s.path.critical
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) s.endpoint s.path.end_color
  have htwo : IsPGroup 2 A := (IsElementaryAbelian.isPGroup 2 (Z Rg s.endpoint)).to_le hAZ
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hTG : forwardSliceKernel h (alpha Rg) c ≤ stabilizer Rg c :=
    (inf_le_left.trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hHU : forwardSliceLine h (alpha Rg) c ≤ U Rg c :=
    le_normalizer_iff_commutator_le_left.mp (hTG.trans (U_normalized c))
  have hline := forward_slice_noncentral_line h e hz hk hb2 p hslice heligible
  obtain ⟨g,hg,hgen,hmove⟩ := exists_cover_line_generator_of_actor h e hz hk hc A
    (hAZ.trans hEC) htwo hAn (forwardSliceLine h (alpha Rg) c) hHU
    hline.1 hline.2.2
  let r : SmallSliceShift h p :=
    ⟨s.endpoint,s.path,s.overlap,g,hg,
      le_antisymm (sup_le inf_le_left hEC) (hgen.symm.le.trans (sup_le_sup_left hAZ _)),
      fun hh => hmove (hh.trans (centralizer_le hAZ))⟩
  have hrgen : r.lineCentralizer ⊔ A = stabilizer Rg c := hgen
  have hpre : v = a' := by
    dsimp only [v]
    have hq : s.path.walk.length = sourceDistance h := s.path.length_eq_b
    rw [show s.path.walk.length-2 = p.walk.length-2 by omega,
      s.overlap _ (Nat.le_refl _),show p.walk.length-2+2=p.walk.length by omega,
      p.walk.getVert_length]
  have hDpre : r.seedOrbit ≤ Q Rg v := by
    rw [hpre]
    exact (r.borel_centralizer_orbits_le_old_endpoint_core e hz hk hb u hfull hslice heligible).1
  have hDe : r.seedOrbit ≤ stabilizer Rg s.endpoint := by
    let t' := s.path.walk.getVert (s.path.walk.length-1)
    have hq : s.path.walk.length = sourceDistance h := s.path.length_eq_b
    have het : Adjacent Rg s.endpoint t' := by
      have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-1) (by omega)
      rw [show s.path.walk.length-1+1=s.path.walk.length by omega,
        s.path.walk.getVert_length] at hh
      exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
    have hvt : Adjacent Rg v t' := by
      have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-2) (by omega)
      rw [show s.path.walk.length-2+1=s.path.walk.length-1 by omega] at hh
      exact (cosetGraph_adj Rg _ _).mp hh
    have ht' : color Rg t' = true := by
      have hh := adjacent_color_ne Rg het
      rw [s.path.end_color] at hh
      cases he : color Rg t' <;> simp_all
    exact (hDpre.trans (Q_le_adjacent_h Rg ht' hvt)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg het))
  have hDV : r.seedOrbit ≤ V Rg c := (r.seedOrbit_radius_and_escape e hz hb2).1
  have hDA : ⁅r.seedOrbit,A⁆ ≤ Z Rg c :=
    hcontrol r.seedOrbit (hDV.trans ((sourceGeometry h).V_le_Q hb2 c hc)) hDe
  let D := r.seedOrbit ⊔ Z Rg c
  have hVG : V Rg c ≤ stabilizer Rg c := (sourceGeometry h).V_local c hc (by
    rw [(sourceGeometry h).distance_constant c hc]; exact hb2)
  have hDVA : D ≤ V Rg c := sup_le hDV (Z_le_VBall Rg c 2)
  have hZA : ⁅Z Rg c,A⁆ ≤ Z Rg c :=
    le_normalizer_iff_commutator_le_left.mp ((hAZ.trans hEC).trans (Z_normalized Rg c))
  have hcomm : ⁅D,A⁆ ≤ Z Rg c :=
    commutator_sup_le_of_relative_normal (stabilizer Rg c) r.seedOrbit (Z Rg c)
      A (Z Rg c) (Z_normalized Rg c) (hDV.trans hVG)
      (Z_le_stabilizer Rg c) hDA hZA
  have hDN : stabilizer Rg c ≤ normalizer (D : Set (FreeAmalgam Rg)) := by
    rw [←hrgen]
    apply sup_le
    · exact (le_inf r.centralizer_orbits_normalized.1
        (inf_le_left.trans (Z_normalized Rg c))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact le_normalizer_iff_commutator_le_left.mpr (hcomm.trans le_sup_right)
  have hDB := normalized_radius_le_slice_of_controlled_actor h e hz hb2 hc D A
    hDVA hDN (hAZ.trans hEC) htwo hAn hcomm
  exact (r.seedOrbit_radius_and_escape e hz hb2).2 (le_sup_left.trans hDB)

end SmallSliceShift
end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "π" => CubicAction.projection h e hz hk
local notation "Rg" => edge L R


include h e hz hk in
/-- The literal shifted configuration has a central line at its shifted
center and the full span commutator equals that line, for either critical
image size. Both moving covers and the original cubic kernel are retained. -/
theorem borel_small_slice_shift_control
    (hb : 2 < sourceDistance h) (u : S6)
    (hfull : (Rg).map π = Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    ∃ s : SmallSliceShift h p, ⁅s.span,s.kernel⁆ = s.line ∧
      Nat.card s.line = 2 ∧
      s.line ≤ centralizer (stabilizer Rg s.centerVertex : Set (FreeAmalgam Rg)) ∧
      (¬ s.span ≤ B Rg s.centerVertex ((sourceGeometry h).Z_normal _)) ∧
      (4 < sourceDistance h → Z Rg a' ≤ Q Rg s.centerVertex ∧ s.span ≤ Q Rg a' ∧
        s.seedOrbit ⊔ s.spanOrbit ≤ Q Rg a' ∧
        (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) = 2 ∧
        (Q Rg (p.walk.getVert 2)).relIndex (Z Rg s.endpoint) = 2) := by
  have hel := (borel_critical_paths h e hz hk u hfull p).2.2.2
  have hex := borel_exists_slice_shift h e hz hk hb u hfull p hslice hel
  obtain ⟨s⟩ := hex
  have hspan := borel_selected_span_forward_commutator h e hz hk hb p u hfull hslice
  have hline := forward_slice_noncentral_line h e hz hk hb p hslice hel
  refine ⟨s,?_,?_,?_,s.span_not_le_slice hb hel,?_⟩
  · have hh := congrArg (Subgroup.map (MulAut.conj s.conjugator).toMonoidHom) hspan.1
    rw [map_commutator,←s.span_map] at hh
    exact hh
  · exact (card_map_of_injective (MulAut.conj s.conjugator).injective).trans hline.1
  · have hm := map_mono (f := (MulAut.conj s.conjugator).toMonoidHom) hspan.2.2
    rw [Theory.GroupTheory.map_centralizer_equiv,
      show (MulAut.conj s.conjugator : FreeAmalgam Rg → FreeAmalgam Rg) =
        (MulAut.conj s.conjugator).toMonoidHom from rfl,←Subgroup.coe_map] at hm
    have he := stabilizer_act Rg s.conjugator⁻¹ (alpha Rg)
    rw [inv_inv] at he
    rwa [←he] at hm
  · intro hb4
    have hc := s.borel_old_endpoint_core e hz hk hb4 u hfull hslice hel
    have ho := s.borel_centralizer_orbits_le_old_endpoint_core e hz hk hb4 u hfull hslice hel
    exact ⟨hc.1,hc.2,sup_le ho.1 ho.2,
      s.borel_shifted_indices e hz hk hb4 u hfull hslice hel⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
