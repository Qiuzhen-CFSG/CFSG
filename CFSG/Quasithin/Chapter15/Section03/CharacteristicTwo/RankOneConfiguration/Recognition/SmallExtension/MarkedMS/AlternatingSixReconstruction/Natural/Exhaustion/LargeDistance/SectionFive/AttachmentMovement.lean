module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MidpointCoreLine

/-!
# Movement of the forced endpoint attachment

At critical distance four with the literal full point-core image, a large
forward slice forces the midpoint core's endpoint image to have order greater
than two. Otherwise that image would equal the critical transposition image,
so the whole midpoint core would fix the reverse critical kernel, contradicting
the previously constructed nonzero backward line. This concerns the whole
midpoint core; the midpoint radius still has image of order two.

The endpoint's central attachment is noncentral at the starting vertex.
Indeed, the backward line is central at the start and noncentral at the
endpoint. It lies in the plane spanned by the critical line and the endpoint
attachment. Exchange of the two distinct lines puts the critical line in the
span of the backward line and the attachment. If the attachment were central
at the start, the critical line would be central there as well.

Consequently every generating first edge moves this attachment and its seed
does not contain the attachment. The final consumer constructs such an edge
on the actual replacement graph. Both full covers and the original nonsylow
radical are retained. These constrain the forced order-32 configuration;
they do not exclude it, select two small slices, or prove the opposite-core
endpoint containment. The unconditional distance bound and other radical
images remain obligations of the same large-distance owner.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the normalization and selection argument in (5.12)(1)--(3), printed
pp.924--927. This extends the original-cover BackwardAttachment and
MidpointCoreLine arguments without suppressing the central attachment.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


private theorem two_line_exchange {F : Type*} [Group F]
    (H D C : Subgroup F) [Finite D] (hd : Nat.card D = 2)
    (hHD : H ≤ D ⊔ C) (hCN : C ≤ normalizer (D : Set F))
    (hne : ¬ H ≤ C) : D ≤ H ⊔ C := by
  obtain ⟨x,hx,hxC⟩ : ∃ x, x ∈ H ∧ x ∉ C := by
    by_contra hno
    apply hne
    intro x hx
    by_contra hxC
    exact hno ⟨x,hx,hxC⟩
  have hp : x ∈ (D : Set F) * (C : Set F) := by
    rw [←coe_mul_of_right_le_normalizer_left D C hCN]
    exact hHD hx
  obtain ⟨z,hz,c,hc,hzc⟩ := hp
  change z*c=x at hzc
  have hzJ : z ∈ H ⊔ C := by
    have hh := (H ⊔ C).mul_mem (mem_sup_left hx) ((H ⊔ C).inv_mem (mem_sup_right hc))
    rwa [←hzc,mul_inv_cancel_right] at hh
  have hzne : z ≠ 1 := by
    intro he
    rw [he,one_mul] at hzc
    exact hxC (hzc ▸ hc)
  let J := D ⊓ (H ⊔ C)
  let : Finite J := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hJne : J ≠ ⊥ := by
    intro he
    exact hzne (mem_bot.mp (he ▸ (show z ∈ J from ⟨hz,hzJ⟩)))
  have hJcard := (one_lt_card_iff_ne_bot J).mpr hJne
  have heq : J = D := eq_of_le_of_card_ge inf_le_left (by omega)
  exact heq ▸ (inf_le_right : J ≤ H ⊔ C)

include s in
/-- A nonzero reverse-kernel commutator forces a midpoint core image
larger than the critical transposition. -/
theorem four_midpoint_core_large_of_kernel_nonzero
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hne : ⁅Z d.radical a' ⊓ Q d.radical a,Q d.radical (p.walk.getVert 2)⁆ ≠ ⊥) :
    2 < (Q d.radical a').relIndex (Q d.radical (p.walk.getVert 2)) := by
  by_contra! hindex
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let c := p.walk.getVert 2
  let K := Z d.radical a' ⊓ Q d.radical a
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hdist : (cosetGraph d.radical).dist c a' = 2 := by rw [p.dist_end,hl]
  have hQG : Q d.radical c ≤ stabilizer d.radical a' :=
    Q_le_stabilizer_of_dist_two d.radical c a' hcol hdist
  have hZaQ : Z d.radical a ≤ Q d.radical c := by
    apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a p.start_color)
    rw [(replacementGeometry h d).distance_constant _ p.start_color,p.dist_start (by omega)]
    exact hb2
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a' p.end_color
  let A := (Z d.radical a).comap i
  let B := (Q d.radical c).comap i
  have hmA : A.map i = Z d.radical a := map_comap_eq_self ((hZaQ.trans hQG).trans_eq hir.symm)
  have hmB : B.map i = Q d.radical c := map_comap_eq_self (hQG.trans_eq hir.symm)
  have hAcard : Nat.card (A.map s.projection) = 2 := by
    rw [←relIndex_ker,s.projection_kernel,←relIndex_map_map_of_injective _ _ hi,hmA,hiQ]
    exact (small_critical_indices s hc p hsmall).1
  have hBcard : Nat.card (B.map s.projection) ≤ 2 := by
    rw [←relIndex_ker,s.projection_kernel,←relIndex_map_map_of_injective _ _ hi,hmB,hiQ]
    exact hindex
  have heq : A.map s.projection = B.map s.projection :=
    eq_of_le_of_card_ge (map_mono (comap_mono hZaQ)) (hBcard.trans_eq hAcard.symm)
  have hB : B ≤ pCore 2 d.overgroup ⊔ A := by
    have hh := le_comap_map s.projection B
    rw [←heq,Subgroup.comap_map_eq,s.projection_kernel] at hh
    exact hh.trans_eq (sup_comm _ _)
  have hQ : Q d.radical c ≤ Q d.radical a' ⊔ Z d.radical a := by
    have hh := map_mono (f := i) hB
    rwa [hmB,Subgroup.map_sup,hiQ,hmA] at hh
  apply hne
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  apply hQ.trans
  apply sup_le
  · exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color))).trans (centralizer_le inf_le_left)
  · exact (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color)).trans (centralizer_le inf_le_right)

/-- The forced endpoint attachment is noncentral at the starting vertex.
Both lines and the attachment are on the original critical path. -/
theorem full_point_four_large_slice_attachment_noncentral_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ¬ U d.radical a' ⊓ centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical)) ≤
      centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
  let H := ⁅K,Q d.radical (p.walk.getVert 2)⁆
  let D := ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆
  let C := U d.radical a' ⊓ centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical))
  have hi := (full_point_four_critical_indices_two_knownSimple hb u hfull p).1
  have hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by omega
  have hline := full_point_four_large_slice_core_line_knownSimple hb u hfull p hlarge
  have hne : H ≠ ⊥ := by
    intro he
    have hh : Nat.card H = 2 := hline.1
    rw [he,card_bot] at hh
    omega
  have hHnotC : ¬ H ≤ C := fun hh =>
    four_kernel_core_noncentral s hc hb p hsmall hne (hh.trans inf_le_right)
  have hHD : H ≤ D ⊔ C := by
    have hh := small_critical_kernel_predecessor_le_commutator_sup_attachment s hc hb2 u hf.le p hsmall
    have hl : p.walk.length = 4 := p.length_eq_b.trans hb
    simpa only [hl,Nat.reduceSub] using hh
  have hDZ : D ≤ Z d.radical a' :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical a')
  have hCN : C ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    ((inf_le_right : C ≤ centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical))).trans
      (centralizer_le (hDZ.trans (Z_le_stabilizer d.radical a')))).trans
      (Subgroup.centralizer_le_normalizer _)
  let := finite_Z d.radical a'
  let : Finite D := Finite.of_injective (inclusion hDZ) (inclusion_injective _)
  have hD : D ≤ H ⊔ C := two_line_exchange H D C
    (small_critical_commutator_card s hc p hsmall) hHD hCN hHnotC
  intro hC
  exact critical_commutator_not_central s hc p (hD.trans (sup_le hline.2.2.2 hC))

/-- The same large-slice branch has a midpoint core image strictly larger
than the radius image of order two. -/
theorem full_point_four_large_slice_midpoint_core_large_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    2 < (Q d.radical a').relIndex (Q d.radical (p.walk.getVert 2)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hi := (full_point_four_critical_indices_two_knownSimple hb u hfull p).1
  apply four_midpoint_core_large_of_kernel_nonzero s hc hb p (by omega)
  intro he
  have hh := (full_point_four_large_slice_core_line_knownSimple hb u hfull p hlarge).1
  rw [he,card_bot] at hh
  omega

/-- The actual endpoint attachment escapes every first edge whose kernel
and the endpoint seed generate the starting stabilizer. -/
theorem full_point_four_large_slice_attachment_generating_edge_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hat : Adjacent d.radical (alpha d.radical) t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical)) :
    let C := U d.radical a' ⊓ centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical))
    ⁅C,Q d.radical t⁆ ≠ ⊥ ∧ ¬ C ≤ Z d.radical t := by
  let C := U d.radical a' ⊓ centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical))
  have hnon := full_point_four_large_slice_attachment_noncentral_knownSimple hb u hfull p hlarge
  have hmove : ⁅C,Q d.radical t⁆ ≠ ⊥ := by
    intro he
    apply hnon
    apply le_centralizer_iff.mp
    rw [←hgen]
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
      (le_centralizer_iff.mp ((inf_le_right : C ≤ centralizer
        (stabilizer d.radical a' : Set (FreeAmalgam d.radical))).trans
          (centralizer_le (Z_le_stabilizer d.radical a'))))
  refine ⟨hmove,?_⟩
  intro hCZ
  apply hmove
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply hCZ.trans
  intro z hz
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  rw [Z,if_neg (by simp [ht])] at hz
  exact (mem_omegaCenter_iff.mp hz).2.2

/-- Construct a generating edge with nontrivial movement of the forced
attachment. This is a constraint on the remaining order-32 configuration. -/
theorem full_point_four_large_slice_moving_attachment_edge_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      ⁅U d.radical a' ⊓ centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical)),
        Q d.radical t⁆ ≠ ⊥ ∧
      ¬ U d.radical a' ⊓ centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical)) ≤
        Z d.radical t := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨t,hat,hgen⟩ := full_point_generating_neighbor s hc u hf p
  exact ⟨t,hat,hgen,full_point_four_large_slice_attachment_generating_edge_knownSimple
    hb u hfull p hlarge hat hgen⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
