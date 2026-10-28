module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.PredecessorCore

/-!
# Endpoint control from consecutive small slices

Let a, m, a' be the even vertices of the original critical path of length
four. Suppose the actual radical image is the full marked point core and
the Baumann indices of U_m at a and U_a' at m are both at most two.
For P = localZSpan(m,a), Y = P intersect Q_m and K = Z_a' intersect Q_a,
the commutator [Y,K] lies in the forward line of order two. Forward escape
makes that line noncentral at m. The predecessor calculation places
[K,Q_m] in the center of the whole midpoint stabilizer, so [Y,K] is trivial.
The full-cover pointwise fixer then gives [Y,Z_a'] <= Z_a.

This supplies the endpoint premise of the actual selected natural quotient
and index-two derived transfer. A small predecessor slice alone supplies
selected-span nonabelianness: the large-forward-slice alternative already
has a nonzero backward critical line. Two consecutive small slices also
force the reverse first slice to be large, using the same original path.

No midpoint conjugacy is assumed, and both the order-sixteen and
order-thirty-two covers, including their central attachments, are retained.
The large-predecessor endpoint branches, whole opposite-core estimates,
other radical images and unconditional distance exclusions remain open.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.10) and the terminal selected-span argument of (5.12), printed
pp.879--881 and 924--927. The proof combines the original-cover ForwardSlice,
PredecessorCore and SmallKernel estimates.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- Consecutive small slices force the selected common kernel to fix the
full reverse critical kernel, with the central attachment retained. -/
theorem consecutive_small_slices_kernel_fixed_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hforward : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hpredecessor : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) :
    localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert 2) ≤ centralizer
        (Z d.radical a' ⊓ Q d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hi := (full_point_four_critical_indices_two_knownSimple hb u hfull p).1
  have hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by omega
  let c := p.walk.getVert 2
  let P := localZSpan d.radical c (alpha d.radical)
  let Y := P ⊓ Q d.radical c
  let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let D := ⁅U d.radical c,T⁆
  let H := ⁅Y,K⁆
  have hline := small_forward_slice_line_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 p hforward hsmall
    (critical_forward_not_le_slice_of_escape s hc hb2
      (full_point_criticalEscape s hc hb2 u hf) p)
  have hspan := small_selected_span_forward_kernel_commutator_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 p hsmall hforward
  have hKT : K ≤ T := le_sup_right.trans
    (selected_forward_kernel_contains_inner_layers (h := h) hb2 p)
  have hHD : H ≤ D := (commutator_mono (inf_le_left : Y ≤ P) hKT).trans_eq hspan.1
  have hHC : H ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
    dsimp only [H]
    rw [commutator_comm]
    exact (commutator_mono le_rfl (inf_le_right : Y ≤ Q d.radical c)).trans
      (predecessor_slice_kernel_core_commutator s hc hb u hf.le p hpredecessor).2.2.2
  let := finite_Z d.radical (p.walk.getVert 1)
  let : Finite D := Finite.of_injective (inclusion hline.2.2.1) (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion hHD) (inclusion_injective _)
  change Y ≤ centralizer (K : Set (FreeAmalgam d.radical))
  apply commutator_eq_bot_iff_le_centralizer.mp
  by_contra hne
  have hlo := (one_lt_card_iff_ne_bot H).mpr hne
  have hcard : Nat.card D = 2 := hline.2.1
  have he : H = D := eq_of_le_of_card_ge hHD (by omega)
  apply hline.2.2.2.2
  change D ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical))
  rw [←he]
  exact hHC

/-- The literal selected-span endpoint estimate follows from the two
consecutive small slices; no endpoint conjugacy is assumed. -/
theorem consecutive_small_slices_endpoint_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hforward : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hpredecessor : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) :
    ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hi := (full_point_four_critical_indices_two_knownSimple hb u hfull p).1
  exact selected_span_endpoint_commutator_of_kernel_fixed s hc hb p (by omega)
    (consecutive_small_slices_kernel_fixed_knownSimple hb u hfull p hforward hpredecessor)

/-- A small predecessor slice suffices for nonabelianness of the selected
span: a large forward slice has its own backward critical line, and a small
forward slice now has the endpoint estimate. -/
theorem small_predecessor_selected_span_nonabelian_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hpredecessor : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) :
    ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ := by
  by_cases hf : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2
  · exact (full_point_four_selected_span_of_endpoint_knownSimple hb u hfull p
      (consecutive_small_slices_endpoint_knownSimple hb u hfull p hf hpredecessor)).1
  · have hd := (full_point_four_large_slice_derived_knownSimple hb u hfull p (by omega)).2.1
    intro he
    rw [he,card_bot] at hd
    omega

/-- Consecutive small slices give the actual moved natural quotient and
its index-two derived transfer, with the original projection and full cover. -/
theorem consecutive_small_slices_natural_quotient_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hforward : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hpredecessor : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) :
    ∃ (E : ((forwardMovedSpan d.radical (p.walk.getVert 2)) ⧸
          center (forwardMovedSpan d.radical (p.walk.getVert 2))) ≃*
        Multiplicative (BinaryPermutation.natural (Fin 6)))
      (τ : Equiv.Perm (Fin 6) ≃* Equiv.Perm (Fin 6)),
      (∀ (m : d.overgroup) (x : forwardMovedSpan d.radical (p.walk.getVert 2)),
        (E (QuotientGroup.mk' _ (forwardMovedSpanAction d.radical (p.walk.getVert 2) m x))).toAdd =
          BinaryPermutation.naturalRepresentation (Fin 6)
            (τ (SourceReduction.projection h e hz hn d m))
            (E (QuotientGroup.mk' _ x)).toAdd) ∧
      (center (forwardMovedSpan d.radical (p.walk.getVert 2))).index = 16 ∧
      Nat.card (⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ :
          Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ∀ A : Subgroup (FreeAmalgam d.radical),
        A ≤ localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) →
        A.relIndex (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2 →
        ⁅A,A⁆ = ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
          localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ := by
  exact selected_natural_quotient_and_transfer_of_full_point_four_endpoint_knownSimple
    hb u hfull p (consecutive_small_slices_endpoint_knownSimple hb u hfull p hforward hpredecessor)

/-- Two consecutive small slices force the reverse of the first slice to
be large. The critical path and the reverse slice use the same vertices. -/
theorem consecutive_small_slices_reverse_large_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hforward : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hpredecessor : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical a') ≤ 2) :
    2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (alpha d.radical)) := by
  exact full_point_four_endpoint_small_slice_reciprocal_large_knownSimple hb u hfull p
    (consecutive_small_slices_endpoint_knownSimple hb u hfull p hforward hpredecessor) hforward

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS


