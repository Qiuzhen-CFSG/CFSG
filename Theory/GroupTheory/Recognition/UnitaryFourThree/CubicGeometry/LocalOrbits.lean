module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceGlobal
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.OppositeConnections
public import Theory.GroupAction.OrbitFamilyEquivalence
/-!
# The three original local orbits and their equivariant comparison

The normalizer of W has exactly three orbits on the connected cubic graph:
W, the 36 neighboring points, and the 243 opposite points. Their marked
stabilizers are respectively the whole normalizer, the normalizer of the
second axis, and K. A marked local normalizer isomorphism therefore gives
an equivariant point bijection. Source: Asc94,45.11, pp.248–249.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)

theorem neighbor_eq_axis_conjugate {U:Subgroup G} (hU:U∈c.neighbors c.W) :
    ∃n∈normalizer (c.W:Set G),U=c.otherAxis.conjBy n := by
  obtain ⟨hUp,hne,L,hL,hWL,hUL⟩ := hU
  obtain ⟨n,hn,hLn⟩ := c.linesThrough_base ▸ (show L∈c.linesThrough c.W from ⟨hL,hWL⟩)
  have hwn : c.W.conjBy n=c.W := mem_normalizer_iff_map_conj_eq.mp hn
  have hUV : U.conjBy n⁻¹≤c.V := by
    have hh := map_mono (f:=(MulAut.conj n⁻¹).toMonoidHom) hUL
    change U.conjBy n⁻¹≤L.conjBy n⁻¹ at hh
    rwa [hLn,conjBy_inv] at hh
  have hU' : U.conjBy n⁻¹≠c.W := by
    intro he
    have hh := congrArg (fun R:Subgroup G=>R.conjBy n) he
    rw [conjBy_inv',hwn] at hh
    exact hne hh
  have hIp : c.otherAxis∈c.kernelLines := c.pointsOn_base ▸
    (show c.otherAxis∈c.pointsOn c.V from ⟨c.otherAxis_is_point,c.otherAxis_le_kernel⟩)
  obtain ⟨d,hd,he⟩ := c.other_kernelLine_orbit hIp c.otherAxis_ne_point _
    (c.pointsOn_base ▸ (show U.conjBy n⁻¹∈c.pointsOn c.V from ⟨c.point_conjugate_mem hUp n⁻¹,hUV⟩)) hU'
  refine ⟨n*d,mul_mem hn (c.complement_product.ge (mem_sup_left hd)),?_⟩
  have hh := congrArg (fun R:Subgroup G=>R.conjBy n) he
  change (U.conjBy n⁻¹).conjBy n=(c.otherAxis.conjBy d).conjBy n at hh
  rw [conjBy_inv',conjBy_conjBy] at hh
  exact hh

@[expose] noncomputable def localRoot (Y:Subgroup G) (hY:Y∈c.points) : Fin 3→c.points :=
  ![⟨c.W,c.point_mem⟩,⟨c.otherAxis,c.otherAxis_is_point⟩,⟨Y,hY⟩]

theorem localRoot_cover {Y:Subgroup G}
    (hYL:Y≤c.oppositeFactor) (hY:Nat.card Y=3) (hne:Y≠c.W)
    (hK:c.K≤normalizer (Y:Set G)) (U:c.points) :
    ∃(i:Fin 3)(n:normalizer (c.W:Set G)),
      c.conjugatePoint (c.localRoot Y (c.cubic_in_oppositeFactor_is_point hYL hY) i) n.val=U := by
  rcases (c.reachable_iff_withinTwo U).mp (c.original_point_reachable U) with he|ha|hd
  · refine ⟨0,1,?_⟩
    exact Subtype.ext ((conjBy_one c.W).trans (congrArg Subtype.val he).symm)
  · obtain ⟨n,hn,he⟩ := c.neighbor_eq_axis_conjugate ha
    exact ⟨1,⟨n,hn⟩,Subtype.ext he.symm⟩
  · obtain ⟨d,hdD,he⟩ := c.distance_two_mem_oddPointOrbit hYL hY hne hK hd
    exact ⟨2,⟨d,c.complement_product.ge (mem_sup_left hdD)⟩,Subtype.ext he.symm⟩

theorem localRoot_conjugate_distance {Y:Subgroup G}
    (hYL:Y≤c.oppositeFactor) (hY:Nat.card Y=3) (hne:Y≠c.W)
    (i:Fin 3) (n:normalizer (c.W:Set G)) :
    c.collinearity.edist ⟨c.W,c.point_mem⟩
      (c.conjugatePoint (c.localRoot Y (c.cubic_in_oppositeFactor_is_point hYL hY) i) n.val)=i.val := by
  have hWn : c.W.conjBy n.val=c.W := mem_normalizer_iff_map_conj_eq.mp n.property
  have hWni : c.W.conjBy n.val⁻¹=c.W := mem_normalizer_iff_map_conj_eq.mp (inv_mem n.property)
  fin_cases i
  · exact c.collinearity.edist_eq_zero_iff.mpr (Subtype.ext hWn.symm)
  · apply c.collinearity.edist_eq_one_iff_adj.mpr
    have hh := c.neighbor_conjugate c.otherAxis_neighbor n.val
    rwa [hWn] at hh
  · let U := c.conjugatePoint ⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩ n.val
    have hneU : U≠⟨c.W,c.point_mem⟩ := by
      intro he
      have hh := congrArg (fun R:Subgroup G=>R.conjBy n.val⁻¹) (congrArg Subtype.val he)
      change (Y.conjBy n.val).conjBy n.val⁻¹=c.W.conjBy n.val⁻¹ at hh
      rw [conjBy_inv,hWni] at hh
      exact hne hh
    have hna : ¬c.collinearity.Adj ⟨c.W,c.point_mem⟩ U := by
      intro ha
      have hh := c.neighbor_conjugate ha n.val⁻¹
      change (Y.conjBy n.val).conjBy n.val⁻¹∈c.neighbors (c.W.conjBy n.val⁻¹) at hh
      rw [conjBy_inv,hWni] at hh
      exact c.opposite_cubic_not_collinear hYL hY hne hh
    rcases (c.reachable_iff_withinTwo U).mp (c.original_point_reachable U) with he|ha|hd
    · exact (hneU he).elim
    · exact (hna ha).elim
    · exact hd


variable {G' : Type*} [Group G'] [Finite G'] {z' : G'} {h' : IsType z'}
variable {P' : Sylow 3 (centralizer z')} (c' : SourceConfiguration h' P')

theorem marked_point_equiv
    (e:normalizer (c.W:Set G) ≃* normalizer (c'.W:Set G'))
    (hI:∀n:normalizer (c.W:Set G),
      n.val∈normalizer (c.otherAxis:Set G) ↔ (e n).val∈normalizer (c'.otherAxis:Set G'))
    (hKmap:∀n:normalizer (c.W:Set G),n.val∈c.K ↔ (e n).val∈c'.K)
    {Y:Subgroup G} {Y':Subgroup G'}
    (hYL:Y≤c.oppositeFactor) (hY:Nat.card Y=3) (hne:Y≠c.W) (hK:c.K≤normalizer (Y:Set G))
    (hYL':Y'≤c'.oppositeFactor) (hY':Nat.card Y'=3) (hne':Y'≠c'.W) (hK':c'.K≤normalizer (Y':Set G')) :
    ∃F:c.points≃c'.points,
      F ⟨c.W,c.point_mem⟩=⟨c'.W,c'.point_mem⟩ ∧
      F ⟨c.otherAxis,c.otherAxis_is_point⟩=⟨c'.otherAxis,c'.otherAxis_is_point⟩ ∧
      F ⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩=⟨Y',c'.cubic_in_oppositeFactor_is_point hYL' hY'⟩ ∧
      ∀(n:normalizer (c.W:Set G))(U:c.points),
        F (c.conjugatePoint U n.val)=c'.conjugatePoint (F U) (e n).val := by
  let := c.conjugationAction
  let := c'.conjugationAction
  let : MulAction (normalizer (c.W:Set G)) c.points := MulAction.compHom c.points (normalizer (c.W:Set G)).subtype
  let : MulAction (normalizer (c'.W:Set G')) c'.points := MulAction.compHom c'.points (normalizer (c'.W:Set G')).subtype
  let r := c.localRoot Y (c.cubic_in_oppositeFactor_is_point hYL hY)
  let s := c'.localRoot Y' (c'.cubic_in_oppositeFactor_is_point hYL' hY')
  have hsep (i j:Fin 3) (g k:normalizer (c.W:Set G)) (he:g•r i=k•r j) : i=j := by
    have hi := c.localRoot_conjugate_distance hYL hY hne i g
    have hj := c.localRoot_conjugate_distance hYL hY hne j k
    change c.collinearity.edist ⟨c.W,c.point_mem⟩ (g•r i)=i.val at hi
    change c.collinearity.edist ⟨c.W,c.point_mem⟩ (k•r j)=j.val at hj
    rw [he] at hi
    exact Fin.ext (ENat.natCast_inj.mp (hi.symm.trans hj))
  have hsep' (i j:Fin 3) (g k:normalizer (c'.W:Set G')) (he:g•s i=k•s j) : i=j := by
    have hi := c'.localRoot_conjugate_distance hYL' hY' hne' i g
    have hj := c'.localRoot_conjugate_distance hYL' hY' hne' j k
    change c'.collinearity.edist ⟨c'.W,c'.point_mem⟩ (g•s i)=i.val at hi
    change c'.collinearity.edist ⟨c'.W,c'.point_mem⟩ (k•s j)=j.val at hj
    rw [he] at hi
    exact Fin.ext (ENat.natCast_inj.mp (hi.symm.trans hj))
  have hst (i:Fin 3) : (MulAction.stabilizer (normalizer (c.W:Set G)) (r i)).map e.toMonoidHom=
      MulAction.stabilizer (normalizer (c'.W:Set G')) (s i) := by
    ext n'
    obtain ⟨n,rfl⟩ := e.surjective n'
    rw [mem_map_equiv,e.symm_apply_apply]
    change (n•r i=r i) ↔ (e n•s i=s i)
    change c.conjugatePoint (r i) n.val=r i ↔ c'.conjugatePoint (s i) (e n).val=s i
    rw [Subtype.ext_iff,Subtype.ext_iff]
    change (r i).val.conjBy n.val=(r i).val ↔ (s i).val.conjBy (e n).val=(s i).val
    have hm (A:Subgroup G) : A.conjBy n.val=A ↔ n.val∈normalizer (A:Set G) :=
      mem_normalizer_iff_map_conj_eq.symm
    have hm' (A:Subgroup G') : A.conjBy (e n).val=A ↔ (e n).val∈normalizer (A:Set G') :=
      mem_normalizer_iff_map_conj_eq.symm
    rw [hm,hm']
    fin_cases i
    · exact iff_of_true n.property (e n).property
    · exact hI n
    · change n.val∈normalizer (Y:Set G) ↔ (e n).val∈normalizer (Y':Set G')
      have hleft : n.val∈normalizer (Y:Set G) ↔ n.val∈c.K :=
        ⟨fun hn=>c.opposite_cubic_common_normalizer hYL hY hne hK ▸ ⟨n.property,hn⟩,
          fun hn=>hK hn⟩
      have hright : (e n).val∈normalizer (Y':Set G') ↔ (e n).val∈c'.K :=
        ⟨fun hn=>c'.opposite_cubic_common_normalizer hYL' hY' hne' hK' ▸ ⟨(e n).property,hn⟩,
          fun hn=>hK' hn⟩
      exact hleft.trans ((hKmap n).trans hright.symm)
  obtain ⟨F,hbase,hact⟩ := MulAction.orbit_family_equiv e r s
    (c.localRoot_cover hYL hY hne hK) (c'.localRoot_cover hYL' hY' hne' hK') hsep hsep' hst
  exact ⟨F,hbase 0,hbase 1,hbase 2,hact⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration

