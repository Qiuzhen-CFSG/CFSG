module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.LocalSpans.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay.Model

/-!
# Good-conjugate differences generate the moving quotient

Write W = localZSpan R a c, J = Z_c[W,G_c], and let H be the sum of
coordinate images of the bad conjugates and V_u. Assume H is proper.
Choose an original seed element with nonzero coordinate; one exists since
its conjugates generate W and the coordinate map is surjective. Neighbor
transitivity puts a conjugate y of this same element in V_u.

The actual marked dual action is transitive on nonzero vectors. For every
v outside H, choose a conjugate x^g with coordinate v times the coordinate
of y. This coordinate is outside H, so g is good. The product x^g y^{-1}
lies in the good span times V_u and, as a difference of conjugates of the
same element, in [W,G_c]. Its coordinate is v. The complement of a proper
subgroup generates the whole coordinate group, proving the required full
image of K intersect J, not just of K. The exact moving-kernel theorem
then lifts this to J contained in K, using Z_c contained in V_u.

Only the stipulated bad-image premise remains conditional. Its producer and
the final source-theorem assembly belong to the parent task. No full-radius
coordinates, favorable pairing, or extra centralizer premise are used.
The proof keeps the original inverse-conjugated edge and both frame markings.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), pp.890–891.
This is the additional sufficient good-span deduction used with the displayed
bad-span estimate on p.891. The finite transitivity step reuses the checked
binary dual pair-orbit theorem in SourceDisplay/Model.lean.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.LocalSpans
open RankOnePairing
private abbrev Space := Multiplicative (Fin 3 → ZMod 2)

private theorem transpose_transitive (v w : Space) (hv : v ≠ 1) (hw : w ≠ 1) :
    ∃ g : SL, g.val.transpose.mulVec v.toAdd = w.toAdd := by
  have h : ∀ v w : Space, ∃ d : Space, d ≠ 1 ∧ d ≠ v ∧ d ≠ w := by decide +kernel
  obtain ⟨d, hd, hdv, hdw⟩ := h v w
  obtain ⟨g, _, hg⟩ :=
    Escape.PairingControl.Geometry.Selection.Centralizer.Generation.SourceDisplay.Model.pair_orbit
      d v w hd hv hw hdv hdw
  exact ⟨g⁻¹, congrArg Multiplicative.toAdd hg⟩

private theorem eq_top_of_complement {G : Type*} [Group G]
    (H K : Subgroup G) (hH : H ≠ ⊤) (hK : ∀ x, x ∉ H → x ∈ K) : K = ⊤ := by
  have hex : ∃ y, y ∉ H := by
    by_contra! h
    exact hH (top_unique (fun y _ => h y))
  obtain ⟨y, hy⟩ := hex
  apply top_unique
  intro x _
  by_cases hx : x ∈ H
  · have hxy : y * x ∉ H := by
      intro hh
      exact hy ((H.mul_mem_cancel_right hx).mp hh)
    have hh := K.mul_mem (K.inv_mem (hK y hy)) (hK (y*x) hxy)
    simpa only [inv_mul_cancel_left] using hh
  · exact hK x hx

variable {M : Type*} [Group M] {R : Subgroup M} {a c : Vertex R}

private theorem conjugateSeed_mem (g : stabilizer R c) (x : Z R a) :
    (g : FreeAmalgam R)⁻¹ * (x : FreeAmalgam R) * g ∈ Z R (act R g a) := by
  rw [Z_act]
  exact ⟨x, x.property, by simp only [MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]⟩

private noncomputable def conjugateSeed (g : stabilizer R c) (x : Z R a) :
    localZSpan R a c :=
  ⟨(g : FreeAmalgam R)⁻¹ * (x : FreeAmalgam R) * g,
    (le_iSup (fun h : stabilizer R c => Z R (act R h a)) g) (conjugateSeed_mem g x)⟩

private theorem conjugateSeed_difference_mem (g h : stabilizer R c) (x : Z R a) :
    (conjugateSeed g x : FreeAmalgam R) * (conjugateSeed h x : FreeAmalgam R)⁻¹ ∈
      movingSpan a c := by
  have hm (k : stabilizer R c) :
      ⁅(k : FreeAmalgam R)⁻¹, (x : FreeAmalgam R)⁆ ∈
        ⁅localZSpan R a c, stabilizer R c⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator ((stabilizer R c).inv_mem k.property)
      (Z_le_localZSpan R a c x.property)
  apply mem_sup_right
  have hh := (⁅localZSpan R a c, stabilizer R c⁆).mul_mem (hm g)
    ((⁅localZSpan R a c, stabilizer R c⁆).inv_mem (hm h))
  have he : ⁅(g : FreeAmalgam R)⁻¹, (x : FreeAmalgam R)⁆ *
      ⁅(h : FreeAmalgam R)⁻¹, (x : FreeAmalgam R)⁆⁻¹ =
      (conjugateSeed g x : FreeAmalgam R) * (conjugateSeed h x : FreeAmalgam R)⁻¹ := by
    simp only [commutatorElement_def, inv_inv, conjugateSeed]
    group
  exact he ▸ hh

variable [Finite M] {L : Subgroup M} {geometry : Geometry R}

private theorem exists_seed_coordinate_ne_one (source : LocalSource L R)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hop : ¬ f.SameOrientation) :
    ∃ x : Z R a,
      coordinates source hc hd hb f hop ⟨x, Z_le_localZSpan R a c x.property⟩ ≠ 1 := by
  classical
  by_contra! h
  have hseed : Z R a ≤ B R c (geometry.Z_normal c) := by
    intro x hx
    have hh : (⟨x, Z_le_localZSpan R a c hx⟩ : localZSpan R a c) ∈
        (coordinates source hc hd hb f hop).ker := h ⟨x,hx⟩
    rwa [coordinates_kernel] at hh
  have hspan : localZSpan R a c ≤ B R c (geometry.Z_normal c) := by
    apply iSup_le
    intro g
    rw [Z_act]
    rintro _ ⟨z, hz, rfl⟩
    let zc : stabilizer R c := ⟨z, f.sectionData.local_group (Z_le_localZSpan R a c hz)⟩
    exact (fixed_normal (geometry := geometry) c).conj_mem zc (hseed hz) g⁻¹
  let v : Space := Multiplicative.ofAdd ![1,0,0]
  obtain ⟨x,hx⟩ := coordinates_surjective source hc hd hb f hop v
  have hk : x ∈ (coordinates source hc hd hb f hop).ker := by
    rw [coordinates_kernel]
    exact hspan x.property
  have he : v = 1 := hx.symm.trans hk
  have : v ≠ 1 := by decide
  exact this he

private theorem exists_conjugate_coordinate (source : LocalSource L R)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (x : Z R a)
    (hx : coordinates source hc hd hb f hop ⟨x, Z_le_localZSpan R a c x.property⟩ ≠ 1)
    (v : Space) (hv : v ≠ 1) :
    ∃ g : stabilizer R c, coordinates source hc hd hb f hop (conjugateSeed g x) = v := by
  obtain ⟨k,hk⟩ := transpose_transitive _ v hx hv
  obtain ⟨g,hg⟩ := f.sectionData.module_section.projection_surjective
    (f.naturalU.marking.symm k)
  refine ⟨g, Multiplicative.toAdd.injective ?_⟩
  rw [coordinates_inverse_conjugation source hc hd hb f hop g
    ⟨x, Z_le_localZSpan R a c x.property⟩ (conjugateSeed g x) rfl,
    hg, f.naturalU.marking.apply_symm_apply]
  exact hk

private theorem exists_incident_conjugate (s : EdgeData a c)
    {u : Vertex R} (hcu : Adjacent R c u) :
    ∃ g : stabilizer R c, Z R (act R g a) ≤ V R u := by
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors R c s.adjacent_center hcu
  refine ⟨⟨g,hg⟩, ?_⟩
  have hgu : Adjacent R (act R g a) u := by
    rw [← hgt]
    exact (adjacent_act_iff R g _ _).mpr s.adjacent_start
  apply le_iSup_of_le (act R g a)
  exact le_iSup_of_le (show (cosetGraph R).dist (act R g a) u ≤ 2 from
    (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hgu)).le.trans
      (by decide)) le_rfl

/-- Good conjugate differences, with an incident conjugate cancelling the
fixed component, generate the full moving quotient. -/
theorem good_moving_coordinate_image_eq_top (source : LocalSource L R)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (s : EdgeData a c) {u : Vertex R} (hcu : Adjacent R c u)
    (hbad : coordinateImage source hc hd hb f hop (badConjugateSpan a c s.neighbor u) ⊔
      coordinateImage source hc hd hb f hop (V R u) ≠ ⊤) :
    coordinateImage source hc hd hb f hop
      ((goodConjugateSpan a c s.neighbor u ⊔ V R u) ⊓ movingSpan a c) = ⊤ := by
  classical
  let π := coordinates source hc hd hb f hop
  let H := coordinateImage source hc hd hb f hop (badConjugateSpan a c s.neighbor u) ⊔
    coordinateImage source hc hd hb f hop (V R u)
  obtain ⟨x,hx⟩ := exists_seed_coordinate_ne_one source hc hd hb f hop
  obtain ⟨h,hh⟩ := exists_incident_conjugate s hcu
  let y := conjugateSeed h x
  have hy : (y : FreeAmalgam R) ∈ V R u := hh (conjugateSeed_mem h x)
  have hyH : π y ∈ H := mem_sup_right (mem_map_of_mem _ hy)
  apply eq_top_of_complement H _ hbad
  intro v hv
  have hvy : v * π y ∉ H := by
    intro hvy
    exact hv ((H.mul_mem_cancel_right hyH).mp hvy)
  have hne : v * π y ≠ 1 := by
    intro he
    exact hvy (he ▸ H.one_mem)
  obtain ⟨g,hg⟩ := exists_conjugate_coordinate source hc hd hb f hop x hx (v * π y) hne
  have hgood : GoodConjugate a c s.neighbor u g := by
    by_contra hn
    have hle : Z R (act R g a) ≤ badConjugateSpan a c s.neighbor u :=
      le_iSup_of_le g (le_iSup_of_le hn le_rfl)
    have hbadmem : (conjugateSeed g x : FreeAmalgam R) ∈ badConjugateSpan a c s.neighbor u :=
      hle (conjugateSeed_mem g x)
    have hi : π (conjugateSeed g x) ∈ H := mem_sup_left (mem_map_of_mem _ hbadmem)
    exact hvy (hg ▸ hi)
  refine ⟨conjugateSeed g x * y⁻¹, ?_, ?_⟩
  · refine ⟨?_, conjugateSeed_difference_mem g h x⟩
    have hle : Z R (act R g a) ≤ goodConjugateSpan a c s.neighbor u :=
      le_iSup_of_le g (le_iSup_of_le hgood le_rfl)
    exact (goodConjugateSpan a c s.neighbor u ⊔ V R u).mul_mem
      (mem_sup_left (hle (conjugateSeed_mem g x)))
      (mem_sup_right ((V R u).inv_mem hy))
  · change π (conjugateSeed g x * y⁻¹) = v
    rw [map_mul, map_inv, hg, mul_inv_cancel_right]

/-- Apply the coordinate calculation to the exact moving kernel Z_c.
The geometric incident-radius inclusion discharges kernel absorption. -/
theorem movingSpan_le_goodConjugateSpan_sup_radius (source : LocalSource L R)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (s : EdgeData a c) {u : Vertex R} (hcu : Adjacent R c u)
    (hbad : coordinateImage source hc hd hb f hop (badConjugateSpan a c s.neighbor u) ⊔
      coordinateImage source hc hd hb f hop (V R u) ≠ ⊤) :
    movingSpan a c ≤ goodConjugateSpan a c s.neighbor u ⊔ V R u := by
  apply movingSpan_le_of_coordinateImage source hc hd hb f hop s
  · apply le_trans (b := V R u) _ le_sup_right
    apply le_iSup_of_le c
    exact le_iSup_of_le (show (cosetGraph R).dist c u ≤ 2 from
      (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hcu)).le.trans
        (by decide)) le_rfl
  · exact good_moving_coordinate_image_eq_top source hc hd hb f hop s hcu hbad

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.LocalSpans
