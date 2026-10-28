module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EndpointAttachment

/-!
# Endpoint control, nonabelianness and reciprocal slices

The literal endpoint estimate for the selected orbit span P forces P outside
its midpoint two-core. Otherwise the whole normal span has endpoint
commutator inside the starting seed, so the section-fixed argument puts P
in the starting Baumann subgroup, contradicting the proved forward escape.
An abelian P would centralize its generating seed and hence lie in that
midpoint core. Thus the endpoint estimate also supplies nonabelianness.

At distance four with full point-core image, the previously proved radius
and derived bounds now give exact midpoint index two and derived order two.
The actual natural quotient and its index-two derived transfer consequently
need only the endpoint estimate. The application to P intersect Q_mid
retains precisely P's derived subgroup; it asserts no bound on the derived
subgroup of the whole opposite core.

For midpoint-conjugate critical paths, the existing common-kernel estimate
supplies endpoint control. The two reciprocal Baumann slices therefore
cannot both be small, with no separate nonabelianness assumption. Transport
uses the original graph, path and conjugator. Applying this obstruction to
the conjugate critical path shows that a small forward slice satisfying the
endpoint estimate has a large reciprocal slice. If both original slices
are small, the endpoint's actual central attachment has order two and lies
in the starting seed.

Both cover orders and the original nonsylow radical remain intact. The
endpoint estimate, opposite-core bounds, remaining radical images and final
large-distance exclusion remain with this task's assembly owner. These
local implications do not establish MS93 (5.12).

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.10), (5.8) and (5.12), printed pp.879--881,919--920,924--927.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- Endpoint control prevents the whole selected normal span from lying
in its midpoint two-core, by the original forward escape. -/
theorem selected_span_not_le_midpoint_of_endpoint
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (hesc : Factorization.CriticalEscape d.radical (replacementGeometry h d))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    ¬ localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ≤ Q d.radical (p.walk.getVert 2) := by
  intro hPQ
  let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hPV : P ≤ V d.radical (alpha d.radical) := localZSpan_le_V d.radical (by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  have hPB := normalized_radius_le_slice_of_critical_commutator s hc hb p P hPV
    (localZSpan_normalized d.radical _ _) (by simpa only [inf_eq_left.mpr hPQ] using hcomm)
  exact critical_forward_not_le_slice_of_escape s hc hb hesc p
    ((DistanceEight.U_le_Z d.radical _).trans ((Z_le_localZSpan d.radical _ _).trans hPB))

include s in
/-- An abelian selected span centralizes its own seed and lies in the
midpoint core, contradicting the endpoint estimate and forward escape. -/
theorem selected_span_nonabelian_of_endpoint
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (hesc : Factorization.CriticalEscape d.radical (replacementGeometry h d))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ := by
  intro he
  apply selected_span_not_le_midpoint_of_endpoint s hc hb hesc p hcomm
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let P := localZSpan d.radical c (alpha d.radical)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases hh' : color d.radical t <;> simp_all
  have hPG : P ≤ stabilizer d.radical c :=
    (((selected_span_le_forward_kernel (h := h) hb p).trans inf_le_left).trans
      (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  rw [←C_eq_Q s hc c hcol]
  refine le_inf hPG ?_
  exact (commutator_eq_bot_iff_le_centralizer.mp he).trans
    (centralizer_le (Z_le_localZSpan d.radical c (alpha d.radical)))


/-- The endpoint estimate supplies nonabelianness, the exact midpoint index,
and the derived order in the actual full-point distance-four branch. -/
theorem full_point_four_selected_span_of_endpoint_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
    ⁅P,P⁆ ≠ ⊥ ∧ (Q d.radical (p.walk.getVert 2)).relIndex P = 2 ∧
      Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hesc := full_point_criticalEscape s hc hb2 u hf
  have hnon := selected_span_nonabelian_of_endpoint s hc hb2 hesc p hcomm
  have hnot := selected_span_not_le_midpoint_of_endpoint s hc hb2 hesc p hcomm
  let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
  have hPG : P ≤ stabilizer d.radical (alpha d.radical) :=
    ((selected_span_le_forward_kernel (h := h) hb2 p).trans inf_le_left).trans
      (fun _ hx => hx.1)
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  let : Finite (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion (Subgroup.commutator_le_sup P P |>.trans (sup_idem P).le)) (inclusion_injective _)
  have hip : 0 < (Q d.radical (p.walk.getVert 2)).relIndex P :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hine : (Q d.radical (p.walk.getVert 2)).relIndex P ≠ 1 :=
    fun he => hnot (relIndex_eq_one.mp he)
  have hi := full_point_four_selected_span_index_knownSimple hb u hfull p
  have hd := (full_point_four_selected_span_derived_bound_knownSimple hb u hfull p).1
  change (Q d.radical (p.walk.getVert 2)).relIndex P ≤ 2 at hi
  change Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 at hd
  have hp := (one_lt_card_iff_ne_bot (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical))).mpr hnon
  exact ⟨hnon,by change (Q d.radical (p.walk.getVert 2)).relIndex P = 2; omega,by
    change Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) = 2
    omega⟩

/-- The literal endpoint bound alone now supplies all selected-span premises
of the natural quotient and index-two derived transfer. The full point-core
branch is retained, and the original central cover is not split. -/
theorem selected_natural_quotient_and_transfer_of_full_point_four_endpoint_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    ∃ (E : ((forwardMovedSpan d.radical (p.walk.getVert 2)) ⧸
          center (forwardMovedSpan d.radical (p.walk.getVert 2))) ≃*
        Multiplicative (BinaryPermutation.natural (Fin 6)))
      (τ : S ≃* S),
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
  have hs := full_point_four_selected_span_of_endpoint_knownSimple hb u hfull p hcomm
  have hi := (full_point_four_critical_indices_two_knownSimple hb u hfull p).1
  have hd := full_point_four_selected_span_derived_bound_knownSimple hb u hfull p
  exact selected_natural_quotient_and_transfer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) p
    (by omega) hs.1 (hd.2.trans (centralizer_le (Ltilde_le_stabilizer _))) hs.2.1.le hcomm

/-- Actual source intersection: the midpoint-core kernel has index two in
the selected span and retains its nontrivial derived line. -/
theorem full_point_four_endpoint_kernel_derived_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical)) :
    let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
    let Y := P ⊓ Q d.radical (p.walk.getVert 2)
    Y.relIndex P = 2 ∧ ⁅Y,Y⁆ = ⁅P,P⁆ ∧
      Nat.card (⁅Y,Y⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by
  have hs := full_point_four_selected_span_of_endpoint_knownSimple hb u hfull p hcomm
  obtain ⟨E,τ,hE,hcenter,hcard,htransfer⟩ :=
    selected_natural_quotient_and_transfer_of_full_point_four_endpoint_knownSimple hb u hfull p hcomm
  let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
  let Y := P ⊓ Q d.radical (p.walk.getVert 2)
  have hi : Y.relIndex P = 2 := by
    dsimp only [Y]
    rw [inf_relIndex_left]
    exact hs.2.1
  have he : ⁅Y,Y⁆ = ⁅P,P⁆ := htransfer Y inf_le_left hi.le
  exact ⟨hi,he,he ▸ hcard⟩


/-- On an actual midpoint-conjugate critical path, the two forward Baumann
slices cannot both have index at most two. Midpoint kernel control supplies
the endpoint estimate, which now proves the needed nonabelianness. -/
theorem full_point_four_midpoint_slice_alternative_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (p.walk.getVert 2))
    (he : act d.radical g (alpha d.radical) = a') :
    2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) ∨
      2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical a') := by
  by_contra! hsmall
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hPQ := (selected_span_le_forward_kernel (h := h) hb2 p).trans inf_le_left
  have hk := (midpoint_common_kernel_endpoint_commutator s hc hb p g hg he hsmall.2).2.le
  have hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) :=
    (commutator_mono (inf_le_inf_right _ hPQ) le_rfl).trans
      (hk.trans (((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
        (DistanceEight.U_le_Z d.radical _)))
  have hnon := selected_span_nonabelian_of_endpoint s hc hb2
    (full_point_criticalEscape s hc hb2 u hf) p hcomm
  exact selected_terminal_false_of_full_seed_slices_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hnon hsmall.1 g hg he hsmall.2


/-- The midpoint slice obstruction transports along the original graph,
retaining the same critical path and its actual conjugator. -/
theorem full_point_four_midpoint_slice_alternative_at_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (p.walk.getVert 2))
    (he : act d.radical g a = a') :
    2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) ∨
      2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical a') := by
  obtain ⟨x,rfl⟩ := exists_mVertex_of_color d.radical p.start_color
  have hxbase : act d.radical x⁻¹ (mVertex d.radical x) = alpha d.radical := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  have base := full_point_four_midpoint_slice_alternative_knownSimple hb u hfull
    (a' := act d.radical x⁻¹ a')
  rw [←hxbase] at base
  let k := x*g*x⁻¹
  have hrestore (v : Vertex d.radical) : act d.radical x (act d.radical x⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hkg : k ∈ stabilizer d.radical ((p.act x⁻¹).walk.getVert 2) := by
    change k ∈ stabilizer d.radical ((actWalk d.radical x⁻¹ p.walk).getVert 2)
    rw [actWalk_getVert,stabilizer_act]
    exact ⟨g,hg,by simp only [inv_inv]; rfl⟩
  have hke : act d.radical k (act d.radical x⁻¹ (mVertex d.radical x)) = act d.radical x⁻¹ a' := by
    simp only [k,act_mul]
    rw [hrestore,he]
  have hci : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by have hl : p.walk.length = replacementDistance h d := p.length_eq_b; omega)).mpr (by decide)
  have hh := base (p.act x⁻¹) k hkg hke
  change 2 < (B d.radical (act d.radical x⁻¹ (mVertex d.radical x))
      ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical ((actWalk d.radical x⁻¹ p.walk).getVert 2)) ∨
    2 < (B d.radical ((actWalk d.radical x⁻¹ p.walk).getVert 2)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (act d.radical x⁻¹ a')) at hh
  rw [actWalk_getVert,
    Escape.PairingControl.FirstPairing.B_act (by omega : 2 < replacementDistance h d) _ _ p.start_color,
    Escape.PairingControl.FirstPairing.B_act (by omega : 2 < replacementDistance h d) _ _ hci,
    U_act,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective,
    relIndex_map_map_of_injective _ _ (MulAut.conj _).injective] at hh
  exact hh

/-- On a small forward slice satisfying the actual endpoint estimate,
the reciprocal slice is necessarily large. The conjugate critical path
and its nonabelianness are constructed, rather than supplied as premises. -/
theorem full_point_four_endpoint_small_slice_reciprocal_large_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical))
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2) :
    2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (alpha d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hnon := (full_point_four_selected_span_of_endpoint_knownSimple hb u hfull p hcomm).1
  obtain ⟨_,x,hx,q,_,hq,_⟩ := selected_span_conjugate_critical_path (h := h) hb2 p hnon
  have hxq : x ∈ stabilizer d.radical (q.walk.getVert 2) := hq.symm ▸ hx
  have hBm : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (geometry := replacementGeometry h d)
        hb2 (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hx))
  have hi : (B d.radical (q.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical x (p.walk.getVert 2))) ≤ 2 := by
    rw [hq,U_act,←hBm,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hslice
  have hh := full_point_four_midpoint_slice_alternative_at_knownSimple hb u hfull q x hxq rfl
  have hlo := hh.resolve_right (Nat.not_lt_of_ge hi)
  simpa only [hq] using hlo

/-- If both literal reciprocal slices are small, the endpoint estimate
cannot hold: the remaining alternative is the actual endpoint central
attachment of order two inside the starting seed. -/
theorem full_point_four_small_slices_force_attachment_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hopposite : (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (alpha d.radical)) ≤ 2) :
    U d.radical a' ⊓ centralizer (stabilizer d.radical a' : Set (FreeAmalgam d.radical)) ≤
        Z d.radical (alpha d.radical) ∧
      Nat.card (U d.radical a' ⊓ centralizer
        (stabilizer d.radical a' : Set (FreeAmalgam d.radical)) : Subgroup (FreeAmalgam d.radical)) = 2 := by
  rcases full_point_four_endpoint_or_central_attachment_knownSimple hb u hfull p hslice with hc | hc
  · exact (Nat.not_lt_of_ge hopposite
      (full_point_four_endpoint_small_slice_reciprocal_large_knownSimple hb u hfull p hc hslice)).elim
  · exact hc

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
