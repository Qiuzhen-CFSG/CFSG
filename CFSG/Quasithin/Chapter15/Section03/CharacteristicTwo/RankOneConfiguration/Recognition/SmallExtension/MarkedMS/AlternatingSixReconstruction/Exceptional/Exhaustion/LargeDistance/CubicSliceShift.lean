module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRadiusEscape

/-!
# Shifted small slices on the original cubic graph

In the full point-core branch, reverse radius escape constructs a forward
critical path with the original overlap. A small eligible slice has an
order-two commutator, central at the start and noncentral at the second
vertex. The marked covering action chooses one residual conjugator whose
line centralizer generates with the new endpoint, which moves that line.
This constructs the choice in MS93 (5.9), equation (**).

The same conjugator transports the kernel and the entire local orbit span.
Their commutator is exactly the transported line. Above distance four,
the predecessor seed and reverse kernel lie in the transported slice
kernel. Their commutators with the span must vanish: any nonzero one would
be the whole line, whereas the inner seeds centralize the new endpoint.
Full-seed centralization puts the span in the predecessor two-core across
the retained odd kernel. The shifted center is either critical with the
old endpoint, or the entire span lies in that endpoint's two-core.

The final applications retain the original whole-core and literal C.1.32
alternatives. Point-core equality, the remainder of the small-slice
exclusion, the other radical images, R4/R6 and MS93 (5.11)--(5.12) are still
required, as are natural exhaustion and final assembly of both outcomes.
The full cubic kernel and both covers of orders sixteen and thirty-two
are preserved throughout.

Source: Meierfrankenfeld--Stellmacher (1993), (5.8)--(5.9),
printed pp.919--922, particularly equation (**) on p.920.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk
include h e hz hk in
/-- Forward radius escape supplies a critical path with the literal initial overlap. -/
theorem full_point_forward_critical_path
    (hb : 2 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
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
    obtain ⟨z,w,q,hw,hq,hover⟩ := full_point_backward_critical_path h e hz hk hb u hfull rev
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

/-- The literal forward-slice centralizer in the starting two-core. -/
@[expose] def forwardSliceKernel (a c : Vertex Rg) : Subgroup (FreeAmalgam Rg) :=
  Q Rg a ⊓ centralizer (U Rg c ⊓ B Rg a ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))

/-- The full moving-cover commutator with its forward-slice kernel. -/
@[expose] def forwardSliceLine (a c : Vertex Rg) : Subgroup (FreeAmalgam Rg) :=
  ⁅U Rg c,forwardSliceKernel h a c⁆

/-- The actual forward endpoint and single residual conjugator used in
MS93 (5.9), equation (**). The construction below supplies every field. -/
structure SmallSliceShift {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a') where
  endpoint : Vertex Rg
  path : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) endpoint
  overlap : ∀ i ≤ p.walk.length-2, path.walk.getVert i = p.walk.getVert (i+2)
  conjugator : FreeAmalgam Rg
  residual : conjugator ∈ Ltilde Rg (p.walk.getVert 2)
  generates : (stabilizer Rg (p.walk.getVert 2) ⊓ centralizer
      ((forwardSliceLine h (alpha Rg) (p.walk.getVert 2)).map
        (MulAut.conj conjugator).toMonoidHom : Set (FreeAmalgam Rg))) ⊔
      Z Rg endpoint = stabilizer Rg (p.walk.getVert 2)
  moves : ¬ (forwardSliceLine h (alpha Rg) (p.walk.getVert 2)).map
      (MulAut.conj conjugator).toMonoidHom ≤ centralizer (Z Rg endpoint : Set (FreeAmalgam Rg))

namespace SmallSliceShift
variable {h} {a' : Vertex (edge L R)}
  {p : CriticalPath (edge L R) (sourceGeometry h) (alpha (edge L R)) a'}
/-- The shifted source vertex μ, using the graph's right action. -/
@[expose] def centerVertex (s : SmallSliceShift h p) : Vertex Rg :=
  act Rg s.conjugator⁻¹ (alpha Rg)
/-- The transported literal kernel T₂. -/
@[expose] def kernel (s : SmallSliceShift h p) : Subgroup (FreeAmalgam Rg) :=
  (forwardSliceKernel h (alpha Rg) (p.walk.getVert 2)).map
    (MulAut.conj s.conjugator).toMonoidHom
/-- The transported order-two commutator H₂. -/
@[expose] def line (s : SmallSliceShift h p) : Subgroup (FreeAmalgam Rg) :=
  (forwardSliceLine h (alpha Rg) (p.walk.getVert 2)).map
    (MulAut.conj s.conjugator).toMonoidHom
/-- The source orbit span V = ⟨Z_(α+2)^(G_μ)⟩. -/
@[expose] def span (s : SmallSliceShift h p) : Subgroup (FreeAmalgam Rg) :=
  localZSpan Rg (p.walk.getVert 2) s.centerVertex
end SmallSliceShift

include h e hz hk in
/-- Radius escape and the marked cover construct equation (**) of (5.9).
No independent displacement or generating-centralizer premise is assumed. -/
theorem exists_small_slice_shift
    (hb : 2 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    Nonempty (SmallSliceShift h p) := by
  obtain ⟨z,q,hover⟩ := full_point_forward_critical_path h e hz hk hb u hfull p
  have hline := small_forward_slice_central_line h e hz hk hb p hsmall hslice heligible
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
    (forwardSliceLine h (alpha Rg) c) hHU hline.1 hline.2.2.2
  exact ⟨⟨z,q,hover,g,hg,hgen,hmove⟩⟩

namespace SmallSliceShift
variable {h} {a' : Vertex (edge L R)}
  {p : CriticalPath (edge L R) (sourceGeometry h) (alpha (edge L R)) a'}
  (s : SmallSliceShift h p)

theorem fixes_second : act Rg s.conjugator⁻¹ (p.walk.getVert 2) = p.walk.getVert 2 :=
  (stabilizer Rg _).inv_mem (Ltilde_le_stabilizer _ s.residual)

theorem center_color : color Rg s.centerVertex = false :=
  action_preserves_color Rg s.conjugator⁻¹ (alpha Rg)

theorem span_map : s.span = (localZSpan Rg (p.walk.getVert 2) (alpha Rg)).map
    (MulAut.conj s.conjugator).toMonoidHom := by
  have hh := LocalCommutator.CriticalCase.localZSpan_act s.conjugator⁻¹
    (p.walk.getVert 2) (alpha Rg)
  rw [s.fixes_second,inv_inv] at hh
  exact hh

theorem kernel_eq (hb : 2 < sourceDistance h) : s.kernel = forwardSliceKernel h s.centerVertex (p.walk.getVert 2) := by
  have hC (A : Subgroup (FreeAmalgam Rg)) :
      (centralizer (A : Set (FreeAmalgam Rg))).map (MulAut.conj s.conjugator).toMonoidHom =
        centralizer (A.map (MulAut.conj s.conjugator).toMonoidHom : Set (FreeAmalgam Rg)) :=
    Theory.GroupTheory.map_centralizer_equiv (A : Set (FreeAmalgam Rg)) (MulAut.conj s.conjugator)
  unfold kernel forwardSliceKernel
  rw [map_inf _ _ _ (MulAut.conj s.conjugator).injective]
  change (Q Rg (alpha Rg)).map (MulAut.conj s.conjugator).toMonoidHom ⊓
    (centralizer ((U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
      ((sourceGeometry h).Z_normal _) : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg))).map
        (MulAut.conj s.conjugator).toMonoidHom = _
  rw [hC (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)),
    map_inf _ _ _ (MulAut.conj s.conjugator).injective]
  have hU := U_act Rg s.conjugator⁻¹ (p.walk.getVert 2)
  rw [s.fixes_second,inv_inv] at hU
  have hB := Escape.PairingControl.FirstPairing.B_act (geometry := sourceGeometry h) hb s.conjugator⁻¹ (alpha Rg) rfl
  rw [inv_inv] at hB
  have hQ := Q_act Rg s.conjugator⁻¹ (alpha Rg)
  rw [inv_inv] at hQ
  rw [←hU,←hB,←hQ]
  rfl

include e hz hk in
theorem span_commutator (hb : 2 < sourceDistance h)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) : ⁅s.span,s.kernel⁆ = s.line := by
  have hh := congrArg (Subgroup.map (MulAut.conj s.conjugator).toMonoidHom)
    (small_selected_span_forward_commutator h e hz hk hb p hsmall hslice).1
  rw [map_commutator,←s.span_map] at hh
  exact hh

include e hz hk in
theorem line_facts (hb : 2 < sourceDistance h)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    Nat.card s.line = 2 ∧ s.line ≤ centralizer (stabilizer Rg s.centerVertex : Set (FreeAmalgam Rg)) := by
  have hh := small_forward_slice_central_line h e hz hk hb p hsmall hslice heligible
  constructor
  · exact (card_map_of_injective (MulAut.conj s.conjugator).injective).trans hh.1
  · have hm := map_mono (f := (MulAut.conj s.conjugator).toMonoidHom) hh.2.2.1
    rw [Theory.GroupTheory.map_centralizer_equiv,
    show (MulAut.conj s.conjugator : FreeAmalgam Rg → FreeAmalgam Rg) = (MulAut.conj s.conjugator).toMonoidHom from rfl,←Subgroup.coe_map] at hm
    have he := stabilizer_act Rg s.conjugator⁻¹ (alpha Rg)
    rw [inv_inv] at he
    rwa [←he] at hm

/-- The same residual conjugator preserves eligibility at the shifted center:
the entire orbit span still escapes its Baumann slice. -/
theorem span_not_le_slice (hb : 2 < sourceDistance h)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    ¬ s.span ≤ B Rg s.centerVertex ((sourceGeometry h).Z_normal _) := by
  have hU := U_act Rg s.conjugator⁻¹ (p.walk.getVert 2)
  rw [s.fixes_second,inv_inv] at hU
  have hB := Escape.PairingControl.FirstPairing.B_act
    (geometry := sourceGeometry h) hb s.conjugator⁻¹ (alpha Rg) rfl
  rw [inv_inv] at hB
  intro hn
  apply heligible
  apply (map_le_map_iff_of_injective (f := (MulAut.conj s.conjugator).toMonoidHom) (MulAut.conj s.conjugator).injective).mp
  rw [←hU,←hB]
  exact (DistanceEight.U_le_Z Rg _).trans ((Z_le_localZSpan Rg _ _).trans hn)
end SmallSliceShift
namespace SmallSliceShift
variable {h} {a' : Vertex (edge L R)}
  {p : CriticalPath (edge L R) (sourceGeometry h) (alpha (edge L R)) a'}
  (s : SmallSliceShift h p)

private theorem center_distance (hb : 2 < sourceDistance h) :
    (cosetGraph Rg).dist s.centerVertex (p.walk.getVert 2) = 2 := by
  rw [centerVertex,←s.fixes_second,dist_act]
  exact p.dist_start (by have he := p.length_eq_b; change p.walk.length = sourceDistance h at he; omega)

private theorem predecessor_color : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
  apply (p.vertex_color (Nat.sub_le _ _)).mpr
  have he := sourceDistance_even h
  rw [Nat.even_iff] at he ⊢
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  omega

private theorem predecessor_distance (hb : 4 < sourceDistance h) :
    (cosetGraph Rg).dist (p.walk.getVert 2) (p.walk.getVert (p.walk.length-2)) = p.walk.length-4 := by
  have hl : 4 < p.walk.length := p.length_eq_b ▸ hb
  have hh := SimpleGraph.length_eq_dist_of_subwalk
    (SimpleGraph.length_eq_dist_of_subwalk p.shortest (p.walk.isSubwalk_drop 2))
    ((p.walk.drop 2).isSubwalk_take (p.walk.length-4))
  have hmin : p.walk.length-4 ≤ p.walk.length-2 := by omega
  simpa only [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
    inf_eq_left.mpr hmin,SimpleGraph.Walk.drop_getVert,
    show 2+(p.walk.length-4)=p.walk.length-2 by omega] using hh.symm

private theorem center_predecessor_distance (hb : 4 < sourceDistance h) :
    (cosetGraph Rg).dist s.centerVertex (p.walk.getVert (p.walk.length-2)) ≤ sourceDistance h-2 := by
  have hh := (cosetGraph_connected Rg).dist_triangle (u := s.centerVertex)
    (v := p.walk.getVert 2) (w := p.walk.getVert (p.walk.length-2))
  rw [s.center_distance (by omega),predecessor_distance (h := h) (p := p) hb] at hh
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  omega

private theorem span_le_radius (hb : 2 < sourceDistance h) : s.span ≤ V Rg s.centerVertex := by
  apply localZSpan_le_V
  rw [SimpleGraph.dist_comm,s.center_distance hb]

private theorem span_le_core (hb : 2 < sourceDistance h) : s.span ≤ Q Rg s.centerVertex :=
  (s.span_le_radius hb).trans ((sourceGeometry h).V_le_Q hb _ s.center_color)

private theorem span_le_predecessor_stabilizer (hb : 4 < sourceDistance h) :
    s.span ≤ stabilizer Rg (p.walk.getVert (p.walk.length-2)) := by
  apply (s.span_le_radius (by omega)).trans
  apply (V_le_iff Rg s.center_color _).mpr
  intro v hv hd
  apply Z_le_stabilizer_of_dist_le v ((sourceGeometry h).exists_critical v hv)
  rw [(sourceGeometry h).distance_constant _ hv]
  have hh := (cosetGraph_connected Rg).dist_triangle (u := v) (v := s.centerVertex)
    (w := p.walk.getVert (p.walk.length-2))
  have hp := s.center_predecessor_distance hb
  change (cosetGraph Rg).dist v (p.walk.getVert (p.walk.length-2)) ≤ sourceDistance h
  omega

/-- The predecessor seed and full reverse kernel lie in the transported T₂,
without assuming the shifted pair is critical. -/
theorem inner_le_kernel (hb : 4 < sourceDistance h) :
    Z Rg (p.walk.getVert (p.walk.length-2)) ⊔ (Z Rg a' ⊓ Q Rg s.centerVertex) ≤ s.kernel := by
  have hc : color Rg (p.walk.getVert 2) = false := s.path.start_color
  have hpreQ : Z Rg (p.walk.getVert (p.walk.length-2)) ≤ Q Rg (p.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ (predecessor_color (h := h) (p := p)))
    rw [(sourceGeometry h).distance_constant _ (predecessor_color (h := h) (p := p)),SimpleGraph.dist_comm,predecessor_distance (h := h) (p := p) hb]
    change p.walk.length-4 < sourceDistance h
    have hl : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have heQ : Z Rg a' ≤ Q Rg (p.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.end_color)
    rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end]
    change p.walk.length-2 < sourceDistance h
    have hl : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hpreM : Z Rg (p.walk.getVert (p.walk.length-2)) ≤ Q Rg s.centerVertex := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ (predecessor_color (h := h) (p := p)))
    rw [(sourceGeometry h).distance_constant _ (predecessor_color (h := h) (p := p)),SimpleGraph.dist_comm]
    change (cosetGraph Rg).dist s.centerVertex (p.walk.getVert (p.walk.length-2)) < sourceDistance h
    exact lt_of_le_of_lt (s.center_predecessor_distance hb) (by omega)
  have hQc : Q Rg (p.walk.getVert 2) ≤ centralizer
      (U Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg _ hc))).trans (centralizer_le (DistanceEight.U_le_Z Rg _))
  rw [s.kernel_eq (by omega)]
  exact le_inf (sup_le hpreM inf_le_right)
    ((sup_le hpreQ (inf_le_left.trans heQ)).trans
      (hQc.trans (centralizer_le inf_le_left)))

private theorem old_endpoint_distance (hb : 2 < sourceDistance h) :
    (cosetGraph Rg).dist a' s.endpoint = 2 := by
  have hh := s.path.dist_end (p.walk.length-2)
  rw [s.overlap _ (Nat.le_refl _),show p.walk.length-2+2=p.walk.length by
    have hl : 2 < p.walk.length := p.length_eq_b ▸ hb; omega,p.walk.getVert_length] at hh
  rw [s.path.length_eq_b,←p.length_eq_b] at hh
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  exact hh.trans (by omega)

private theorem inner_seed_centralizes_endpoint (hb : 4 < sourceDistance h) :
    Z Rg (p.walk.getVert (p.walk.length-2)) ⊔ Z Rg a' ≤
      centralizer (Z Rg s.endpoint : Set (FreeAmalgam Rg)) := by
  have hpre : (cosetGraph Rg).dist (p.walk.getVert (p.walk.length-2)) s.endpoint < sourceDistance h := by
    have hh := (cosetGraph_connected Rg).dist_triangle
      (u := p.walk.getVert (p.walk.length-2)) (v := a') (w := s.endpoint)
    rw [p.dist_end,s.old_endpoint_distance (by omega)] at hh
    have hl : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hQ : Z Rg (p.walk.getVert (p.walk.length-2)) ⊔ Z Rg a' ≤ Q Rg s.endpoint := by
    apply sup_le
    · apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ (predecessor_color (h := h) (p := p)))
      rw [(sourceGeometry h).distance_constant _ (predecessor_color (h := h) (p := p))]
      exact hpre
    · apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.end_color)
      rw [(sourceGeometry h).distance_constant _ p.end_color,s.old_endpoint_distance (by omega)]
      change 2 < sourceDistance h
      omega
  exact hQ.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (Z_centralizes_Q Rg _ s.path.end_color)))

include e hz hk in
/-- The shifted span centralizes both literal inner layers. Its predecessor
core placement is derived from full-seed centralization across the odd kernel. -/
theorem inner_control (hb : 4 < sourceDistance h)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    s.span ≤ Q Rg (p.walk.getVert (p.walk.length-2)) ∧
      s.span ≤ stabilizer Rg a' ∧
      ⁅s.span,Z Rg (p.walk.getVert (p.walk.length-2)) ⊔ (Z Rg a' ⊓ Q Rg s.centerVertex)⁆ = ⊥ := by
  have hcard := (s.line_facts e hz hk (by omega) hsmall hslice heligible).1
  have hcomm := s.span_commutator e hz hk (by omega) hsmall hslice
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
theorem old_endpoint_alternative (hb : 4 < sourceDistance h)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    CriticalPair Rg s.centerVertex a' ((sourceGeometry h).exists_critical _ s.center_color) ∨
      (Z Rg a' ≤ Q Rg s.centerVertex ∧ s.span ≤ Q Rg a') := by
  have hi := s.inner_control e hz hk hb hsmall hslice heligible
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
end SmallSliceShift
omit hk in
include h e hz in
/-- Apply the shifted-span construction and its inner-layer bounds to the
original whole-core alternative, retaining the full cubic kernel and covers. -/
theorem coreExhaustion_or_cubic_small_slice_shift :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) ≤ 2 →
          ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) →
          ∃ s : SmallSliceShift h p,
            ⁅s.span,s.kernel⁆ = s.line ∧ Nat.card s.line = 2 ∧
            s.line ≤ centralizer (stabilizer Rg s.centerVertex : Set (FreeAmalgam Rg)) ∧
            (¬ s.span ≤ B Rg s.centerVertex ((sourceGeometry h).Z_normal _)) ∧
            (4 < sourceDistance h →
              s.span ≤ Q Rg (p.walk.getVert (p.walk.length-2)) ∧
              s.span ≤ stabilizer Rg a' ∧
              ⁅s.span,Z Rg (p.walk.getVert (p.walk.length-2)) ⊔
                (Z Rg a' ⊓ Q Rg s.centerVertex)⁆ = ⊥ ∧
              (CriticalPair Rg s.centerVertex a' ((sourceGeometry h).exists_critical _ s.center_color) ∨
                (Z Rg a' ≤ Q Rg s.centerVertex ∧ s.span ≤ Q Rg a'))) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,?_⟩
    intro u hfull a' p hsmall hslice hel
    obtain ⟨s⟩ := exists_small_slice_shift h e hz hk hb u hfull p hsmall hslice hel
    have hf := s.line_facts e hz hk hb hsmall hslice hel
    refine ⟨s,s.span_commutator e hz hk hb hsmall hslice,hf.1,hf.2,s.span_not_le_slice hb hel,?_⟩
    intro hb4
    have hi := s.inner_control e hz hk hb4 hsmall hslice hel
    exact ⟨hi.1,hi.2.1,hi.2.2,s.old_endpoint_alternative e hz hk hb4 hsmall hslice hel⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the constructed shifted span. The remaining
strict-slice and terminal contradictions are not premises hidden in this result. -/
theorem rankTwo_or_cubic_small_slice_shift :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) ≤ 2 →
          ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) →
          ∃ s : SmallSliceShift h p,
            ⁅s.span,s.kernel⁆ = s.line ∧ Nat.card s.line = 2 ∧
            s.line ≤ centralizer (stabilizer Rg s.centerVertex : Set (FreeAmalgam Rg)) ∧
            (¬ s.span ≤ B Rg s.centerVertex ((sourceGeometry h).Z_normal _)) ∧
            (4 < sourceDistance h →
              s.span ≤ Q Rg (p.walk.getVert (p.walk.length-2)) ∧
              s.span ≤ stabilizer Rg a' ∧
              ⁅s.span,Z Rg (p.walk.getVert (p.walk.length-2)) ⊔
                (Z Rg a' ⊓ Q Rg s.centerVertex)⁆ = ⊥ ∧
              (CriticalPair Rg s.centerVertex a' ((sourceGeometry h).exists_critical _ s.center_color) ∨
                (Z Rg a' ≤ Q Rg s.centerVertex ∧ s.span ≤ Q Rg a'))) :=
  (coreExhaustion_or_cubic_small_slice_shift h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
