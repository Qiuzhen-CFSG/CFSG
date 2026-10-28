module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanDerived
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSeedFixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EdgeMarkedRefinement
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SymplecticMovedDual

/-!
# The whole selected span modulo its full B-intersection

Keep the actual span action, its full denominator and the natural marking
on its literal moved section. Zero fixed space makes this a dual cover in
the retained coordinates. The actual edge fixes the seed modulo B and has
no invariant refinement in this same marking. The seed therefore lies in
the moved image, and its full normal span lies in Vcirc joined with B.
The reciprocal orientation is retained explicitly.
Source: MS93 (5.12)(2), printed p.926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem whole_from_same_span
    {geometry : Geometry d.radical} {a z c₀ y t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (largePath : CriticalPath d.radical geometry c₀ y)
    (hlarge : Nat.card F^2 ≤ (Q d.radical y).relIndex (Z d.radical c₀))
    (hat : Adjacent d.radical a t)
    (hseed : ⁅Z d.radical (path.walk.getVert 2),Q d.radical t⁆ ≤
      B d.radical a (geometry.Z_normal a))
    (hnat : distanceFourSpanNatural geometry a (path.walk.getVert 2) n) :
    localZSpan d.radical (path.walk.getVert 2) a ≤
      Vcirc d.radical a ⊔ B d.radical a (geometry.Z_normal a) := by
  obtain ⟨E,hE,f,hf,hfQ,hD,hEA,σ,hfaith,c,hcoord,hactor,hIrr,Eₙ,hEₙ,⟨eₙ⟩⟩ := hnat
  let := hD
  let := hEA
  let W := localZSpan d.radical (path.walk.getVert 2) a
  let P := Vcirc d.radical a
  let S := stabilizer d.radical a
  let B₀ := B d.radical a (geometry.Z_normal a)
  let T := Q d.radical t
  let s := MovedSection.ofNormal σ (⊤ : Subgroup (Sp E.Carrier))
  let := finite_stabilizer d.radical a
  let : Finite W := Finite.of_injective (inclusion c.section_le) (inclusion_injective _)
  have hl := path.length_eq_b
  have hWV : W ≤ V d.radical a := localZSpan_le_V d.radical (by
    rw [SimpleGraph.dist_comm,path.dist_start (by omega)])
  have hm : c.imageSpace P=s.space.toSubmodule :=
    (h.replacement_distance_four_span_moved_image d path hb largePath hlarge E hE f hf σ c).trans
      s.space_eq.symm
  have hzero := h.replacement_radius_section_fixedSpace_eq_bot d geometry (by omega)
    path.start_color W hWV f σ c
  let α : Sp E.Carrier ≃* Sp Eₙ.Carrier := topEquiv.symm.trans eₙ.groupEquiv
  let f' := α.toMonoidHom.comp f
  have hf' : Function.Surjective f' := α.surjective.comp hf
  have hk : f'.ker=f.ker := by
    ext x
    change α (f x)=1 ↔ f x=1
    exact α.map_eq_one_iff
  have hfQ' : f'.ker.map S.subtype=Q d.radical a := by rw [hk]; exact hfQ
  have hcard : 2 < Nat.card Eₙ.Carrier := by
    rw [Eₙ.card_eq,hEₙ]
    exact (by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let A := (T.subgroupOf S).map f
  have hno := h.replacement_edge_no_refinement_of_marking d geometry (by omega)
    path.start_color hat Eₙ hEₙ f' hf' hfQ'
  change ¬ ∃ c₀ : Vector Eₙ.Carrier, ∀ x : (T.subgroupOf S).map f',
    ∀ v, Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors.refinement c₀
      (x.val • v) = Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors.refinement c₀ v at hno
  rw [show (T.subgroupOf S).map f'=A.map α.toMonoidHom from
    (Subgroup.map_map _ _ _).symm] at hno
  have hfix : fixedSpace σ A ≤ s.space.toSubmodule := by
    rw [s.space_eq]
    exact fixedSpace_le_moved_of_symplectic_no_refinement σ Eₙ hcard eₙ hzero A hno
  have hTS : T ≤ S := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hZW : Z d.radical (path.walk.getVert 2) ≤ W := Z_le_localZSpan _ _ _
  have hcomm : ⁅Z d.radical (path.walk.getVert 2),T⁆ ≤ W :=
    (commutator_mono hZW le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hTS.trans c.normalized))
  have hseedspace : c.imageSpace (Z d.radical (path.walk.getVert 2)) ≤ s.space.toSubmodule := by
    apply le_trans _ hfix
    intro v hv x
    obtain ⟨w,hw,rfl⟩ := (c.mem_imageSpace_iff _ v).mp hv
    obtain ⟨g,hg,he⟩ := x.property
    change f g=x.val at he
    change σ x.val (c.coordinates w).toAdd=(c.coordinates w).toAdd
    rw [←he]
    exact (c.fixed_coordinate_iff_commutator_mem g w).mpr
      ⟨hcomm (commutator_mem_commutator hw hg),hseed (commutator_mem_commutator hw hg)⟩
  let N := c.subspacePreimage s.space.toSubmodule
  have hZN : Z d.radical (path.walk.getVert 2) ≤ N := by
    intro z hz
    exact (c.mem_subspacePreimage _ z).mpr ⟨hZW hz,
      hseedspace ((c.mem_imageSpace_iff _ _).mpr ⟨⟨z,hZW hz⟩,hz,rfl⟩)⟩
  have hSN : S ≤ normalizer (N : Set (FreeAmalgam d.radical)) := by
    apply c.subspacePreimage_normalized S le_rfl
    rw [subgroupOf_self]
    apply le_subspaceStabilizer
    intro g _ v hv
    exact s.space.apply_mem_toSubmodule (f g) hv
  have hWN : W ≤ N := by
    change localZSpan d.radical (path.walk.getVert 2) a ≤ N
    rw [localZSpan_eq_conjugates]
    apply iSup_le
    intro g
    exact (map_mono (f := (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom) hZN).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (hSN (S.inv_mem g.property)))
  apply hWN.trans
  apply c.subspacePreimage_le_of_imageSpace_le _ (P ⊔ B₀)
  · exact inf_le_right.trans le_sup_right
  · rw [←hm]
    exact c.imageSpace_mono le_sup_left

/-- The actual fixed-radius, large-back branch puts the whole selected
normal span in its moved radius joined with the full B-preimage. The
original retained natural marking and reciprocal orientation are preserved. -/
theorem Input.replacement_distance_four_span_whole_or_reciprocal
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hlarge : Nat.card F < (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u))
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    (distanceFourSpanNatural geometry a (path.walk.getVert 2) n ∧
      localZSpan d.radical (path.walk.getVert 2) a ≤
        Vcirc d.radical a ⊔ B d.radical a (geometry.Z_normal a)) ∨
    (distanceFourSpanNatural geometry (path.walk.getVert 2) a n ∧
      localZSpan d.radical a (path.walk.getVert 2) ≤
        Vcirc d.radical (path.walk.getVert 2) ⊔
          B d.radical (path.walk.getVert 2) (geometry.Z_normal (path.walk.getVert 2))) := by
  let e := path.walk.getVert 2
  let t := path.walk.getVert 1
  have hl := path.length_eq_b
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hat : Adjacent d.radical a t := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have het : Adjacent d.radical e t := adjacent_symm _
    ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hsq : Nat.card F^2 ≤ (Q d.radical e).relIndex (Z d.radical u) := by
    by_contra! hs
    exact (ne_of_gt hlarge) (h.replacement_small_critical_indices_eq_field d back (by omega) hs).1
  have hseed := h.replacement_distance_four_seed_fixed d path hb back hmid hlarge hfixed
  rcases h.replacement_distance_four_span_natural_or_reciprocal d path hb back hmid hlarge hfixed
    with hnat | hnat
  · exact Or.inl ⟨hnat,whole_from_same_span h d path hb back hsq hat hseed.1 hnat⟩
  · let rev : CriticalPath d.radical geometry e u := {
      start_color := back.end_color
      walk := back.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,back.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical geometry
        (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
          (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
        u back.start_color (by
          rw [geometry.distance_constant u back.start_color]
          exact lt_of_lt_of_le (by decide : 0<4) hb4)
        e back.end_color back.critical }
    have hrmid : rev.walk.getVert 2=a := by
      change back.walk.reverse.getVert 2=a
      rw [SimpleGraph.Walk.getVert_reverse,back.length_eq_b,hb]
      exact hmid
    refine Or.inr ⟨hnat,?_⟩
    have hseed' : ⁅Z d.radical (rev.walk.getVert 2),Q d.radical t⁆ ≤
        B d.radical e (geometry.Z_normal e) := by rw [hrmid]; exact hseed.2
    have hnat' : distanceFourSpanNatural geometry e (rev.walk.getVert 2) n := by
      rw [hrmid]
      exact hnat
    have hh := whole_from_same_span h d rev hb back hsq het hseed' hnat'
    rwa [hrmid] at hh

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
