module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.AutomorphismPropagation
/-!
# Intrinsic recovery of the original cubic root subgroup

The graph automorphisms fixing W and all its neighbors are precisely
the conjugation actions of W. Two common neighbors of W and an opposite
vertex have at most four common neighbors. Excluding W leaves the three
points in the free W-orbit. Thus such an automorphism agrees with some
element of W on the opposite vertex; propagation makes them equal.
Source: Aschbacher, Sporadic Groups (1994),45.11, pp.248–249.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)

theorem common_neighbors_card_le_four (I J : c.points)
    (hna : ¬c.collinearity.Adj I J) (hne : I≠J) :
    Nat.card (c.collinearity.commonNeighbors I J)≤4 := by
  classical
  have hh (U : c.collinearity.commonNeighbors I J) :
      ∃L:c.linesThrough I.val,U.val.val≤L.val := by
    obtain ⟨-, -, L,hL,hIL,hUL⟩ := U.property.1
    exact ⟨⟨L,hL,hIL⟩,hUL⟩
  let f (U : c.collinearity.commonNeighbors I J) : c.linesThrough I.val := (hh U).choose
  have hf : Function.Injective f := by
    intro U U' he
    apply Subtype.ext
    exact c.common_neighbors_on_line_unique I J U.val U'.val hna hne U.property U'.property
      (f U).property (hh U).choose_spec (he ▸ (hh U').choose_spec)
  exact (Nat.card_le_card_of_injective f hf).trans_eq (c.linesThrough_card I.property)

omit [Finite G] in
theorem root_fixes_neighbor {w : G} (hw : w∈c.W) (U : c.points)
    (hU : c.collinearity.Adj ⟨c.W,c.point_mem⟩ U) :
    c.graphAction w U=U := by
  apply Subtype.ext
  exact mem_normalizer_iff_map_conj_eq.mp ((c.neighbor_centralizes hU).trans
    (Subgroup.centralizer_le_normalizer _) hw)

theorem fixed_neighborhood_opposite_image (f : c.collinearity ≃g c.collinearity)
    (hbase : f ⟨c.W,c.point_mem⟩=⟨c.W,c.point_mem⟩)
    (hperp : ∀U:c.points,c.collinearity.Adj ⟨c.W,c.point_mem⟩ U→f U=U)
    {Y : Subgroup G} (hYL : Y≤c.oppositeFactor) (hY : Nat.card Y=3) (hne : Y≠c.W)
    (hK : c.K≤normalizer (Y:Set G)) :
    ∃w∈c.W,f ⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩=
      c.graphAction w ⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩ := by
  classical
  let Wp : c.points := ⟨c.W,c.point_mem⟩
  let Yp : c.points := ⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩
  let C := c.collinearity.commonNeighbors Wp Yp
  have hdist : c.collinearity.edist Wp Yp=2 := c.opposite_cubic_distance_two hYL hY hne
  let : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1<Nat.card (c.collinearity.commonNeighbors Wp Yp)
    rw [c.opposite_common_neighbors_card hYL hY hne hK]
    decide)
  obtain ⟨I,J,hIJ⟩ := exists_pair_ne C
  have hneIJ : I.val≠J.val := fun he=>hIJ (Subtype.ext he)
  have hnot : ¬c.collinearity.Adj I.val J.val := by
    intro hij
    obtain ⟨L,hL,hWL,hIL,hJL⟩ := c.triangle_on_line Wp I.val J.val I.property.1 J.property.1 hij
    exact hneIJ (c.common_neighbors_on_line_unique Wp Yp I.val J.val
      (c.collinearity.edist_eq_two_iff.mp hdist).2.1 (c.collinearity.edist_eq_two_iff.mp hdist).1
      I.property J.property ⟨hL,hWL⟩ hIL hJL)
  let B : Set c.points := c.collinearity.commonNeighbors I.val J.val \ {Wp}
  have hWB : Wp∈c.collinearity.commonNeighbors I.val J.val :=
    ⟨c.collinearity.adj_symm I.property.1,c.collinearity.adj_symm J.property.1⟩
  have hBc : Nat.card B≤3 := by
    change B.ncard≤3
    rw [show B=c.collinearity.commonNeighbors I.val J.val \ {Wp} from rfl,
      Set.ncard_sdiff_singleton_of_mem hWB]
    have hc := c.common_neighbors_card_le_four I.val J.val hnot hneIJ
    change (c.collinearity.commonNeighbors I.val J.val).ncard≤4 at hc
    omega
  have hWD : c.W≤c.D := c.odd_fixed.ge.trans inf_le_left
  have hfixed (w:c.W) (U:c.points) (hU:c.collinearity.Adj Wp U) : c.graphAction w.val U=U :=
    c.root_fixes_neighbor w.property U hU
  have horbit (w:c.W) : c.graphAction w.val Yp∈B := by
    refine ⟨⟨?_,?_⟩,?_⟩
    · exact hfixed w I.val I.property.1 ▸ (c.graphAction w.val).map_rel_iff.mpr
        (c.collinearity.adj_symm I.property.2)
    · exact hfixed w J.val J.property.1 ▸ (c.graphAction w.val).map_rel_iff.mpr
        (c.collinearity.adj_symm J.property.2)
    · intro he
      have hd := c.opposite_cubic_conjugate_distance_two hYL hY hne w.val (hWD w.property)
      have he' : c.graphAction w.val Yp=Wp := he
      rw [←show c.graphAction w.val Yp=⟨Y.conjBy w.val,c.point_conjugate_mem Yp.property w.val⟩ from rfl,
        he',c.collinearity.edist_self] at hd
      exact (by decide : (0:ENat)≠2) hd
  let j (w:c.W) : B := ⟨c.graphAction w.val Yp,horbit w⟩
  have hj : Function.Injective j := by
    intro w w' he
    apply Subtype.ext
    have hh := congrArg (fun U:B=>U.val.val) he
    exact congrArg (fun d:c.D=>(d:G)) (c.opposite_odd_conjugation_injective hYL hY hne
      (a₁:=⟨w.val,hWD w.property⟩) (a₂:=⟨w'.val,hWD w'.property⟩) hh)
  have hsurj := (hj.bijective_of_nat_card_le (c.line_card.symm ▸ hBc)).2
  have hfYB : f Yp∈B := by
    refine ⟨⟨?_,?_⟩,?_⟩
    · exact hperp I.val I.property.1 ▸ f.map_rel_iff.mpr (c.collinearity.adj_symm I.property.2)
    · exact hperp J.val J.property.1 ▸ f.map_rel_iff.mpr (c.collinearity.adj_symm J.property.2)
    · intro he
      have he' : Yp=Wp := f.injective (he.trans hbase.symm)
      exact hne (congrArg Subtype.val he')
  obtain ⟨w,hw⟩ := hsurj ⟨f Yp,hfYB⟩
  exact ⟨w.val,w.property,(congrArg Subtype.val hw).symm⟩

theorem graph_aut_fixes_closed_neighborhood_iff (f : c.collinearity ≃g c.collinearity) :
    (f ⟨c.W,c.point_mem⟩=⟨c.W,c.point_mem⟩ ∧
      ∀U:c.points,c.collinearity.Adj ⟨c.W,c.point_mem⟩ U→f U=U) ↔
    ∃w∈c.W,f=c.graphAction w := by
  constructor
  · rintro ⟨hbase,hperp⟩
    obtain ⟨Y,hYL,hY,hne,-,hK⟩ := c.exists_complement_fixed_opposite_cubic
    obtain ⟨w,hw,he⟩ := c.fixed_neighborhood_opposite_image f hbase hperp hYL hY hne hK
    let g := c.graphAction w
    have hgbase : g ⟨c.W,c.point_mem⟩=⟨c.W,c.point_mem⟩ :=
      Subtype.ext (mem_normalizer_iff_map_conj_eq.mp (c.W.le_normalizer hw))
    have hginv : g.symm ⟨c.W,c.point_mem⟩=⟨c.W,c.point_mem⟩ := by
      exact g.symm_apply_eq.mpr hgbase.symm
    let f' := f.trans g.symm
    have hbase' : f' ⟨c.W,c.point_mem⟩=⟨c.W,c.point_mem⟩ := by
      change g.symm (f ⟨c.W,c.point_mem⟩)=⟨c.W,c.point_mem⟩
      rw [hbase,hginv]
    have hperp' (U:c.points) (hU:c.collinearity.Adj ⟨c.W,c.point_mem⟩ U) : f' U=U := by
      change g.symm (f U)=U
      rw [hperp U hU]
      have hgU : g U=U := c.root_fixes_neighbor hw U hU
      exact g.symm_apply_eq.mpr hgU.symm
    have hY' : f' ⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩=⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩ := by
      change g.symm (f ⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩)=_
      rw [he]
      exact g.symm_apply_apply _
    have hid := c.graph_aut_eq_of_fixed_opposite f' hbase' hperp' hYL hY hne hK hY'
    refine ⟨w,hw,?_⟩
    apply RelIso.ext
    intro U
    have hh := DFunLike.congr_fun hid U
    change g.symm (f U)=U at hh
    exact g.symm_apply_eq.mp hh
  · rintro ⟨w,hw,rfl⟩
    exact ⟨Subtype.ext (mem_normalizer_iff_map_conj_eq.mp (c.W.le_normalizer hw)),
      c.root_fixes_neighbor hw⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration

