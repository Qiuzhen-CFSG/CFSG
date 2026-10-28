module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.EdgeNormalizer
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCharacteristic

/-!
# A Todd correction preserving the whole original edge fixer

The point-plane overlap has characteristic core Q. Since every full-word
Todd twist fixes E pointwise, transporting Q by a member of K shows that the
twist preserves each of the seven centralizer cores attached to Z. Hence it
preserves their actual join K. Choose the odd full word by averaging over the
cubic Sylow subgroup supplied by the edge-normalizer formula. The resulting
Todd twist fixes that cubic pointwise, preserves its relative normalizer in
S∩M, and therefore preserves the entire B=K N_(S∩M)(Y).

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.2), p.606,
the verification of hypothesis (V2). This proves edge-subgroup control for
the constructed outer automorphism. Alignment of the two local comparisons
and the full edge-reversal conjugation equation remain necessary.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu MathieuCode
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
variable (a : SourceIncidence.LocalData h)

/-- Every full-word Todd correction fixes the original point radical elementwise. -/
theorem pointTwist_fixes_radical (w : Full) (m : a.P.M) (hm : (m : G) ∈ a.P.E) :
    pointTwist a w m=m := by
  obtain ⟨v,hv⟩ := hm
  have he : m=a.P.toddEquiv (SemidirectProduct.inl v) := Subtype.ext hv.symm
  rw [he,pointTwist_vector]

private theorem pointTwist_core_mem (w : Full) (m : a.P.M) (hm : (m : G) ∈ ambientCore z) :
    (pointTwist a w m : G) ∈ ambientCore z := by
  let u : PlaneOverlap a := ⟨⟨m,ambientCore_le z hm⟩,m.property⟩
  have hu : u ∈ (core z).subgroupOf (PlaneOverlap a) := by
    obtain ⟨q,hq,he⟩ := hm
    have hq' : q=u.val := Subtype.ext he
    change u.val ∈ core z
    exact hq' ▸ hq
  have he := mem_map_of_mem (planeOverlapToddTwist a w).toMonoidHom hu
  rw [overlap_automorphism_preserves_core] at he
  have hh : (planeOverlapToddTwist a w u).val.val ∈ ambientCore z :=
    ⟨(planeOverlapToddTwist a w u).val,he,rfl⟩
  rw [planeOverlapToddTwist_coe] at hh
  exact hh

private theorem exists_K_marker_transporter (v : G) (hv : v ∈ a.d.space) (hne : v ≠ 1) :
    ∃ k : a.d.K, (k : G)*z*(k : G)⁻¹=v := by
  obtain ⟨n,hn,he⟩ := a.d.normalizer_transitive v hv hne
  obtain ⟨k,hk,s,hs,hks⟩ := a.d.normalizer_product h n hn
  have hz : z ∈ a.d.space := (a.d.markedPoint 0).property
  have hsz : s*z*s⁻¹=z := by
    rw [←hs z hz,mul_inv_cancel_right]
  refine ⟨⟨k,hk⟩,?_⟩
  calc
    k*z*k⁻¹ = k*(s*z*s⁻¹)*k⁻¹ := by rw [hsz]
    _ = (k*s)*z*(k*s)⁻¹ := by group
    _ = v := by rw [hks,he]

/-- The Todd correction preserves each of the seven original centralizer cores.
Its action on the marked involutions is pointwise, and Q is characteristic
in the literal point-plane overlap. -/
theorem pointTwist_seven_core (w : Full) (v : G) (hv : v ∈ a.d.space) (hne : v ≠ 1) :
    ((ambientCore v).subgroupOf a.P.M).map (pointTwist a w).toMonoidHom =
      (ambientCore v).subgroupOf a.P.M := by
  have hzK : ambientCore z ≤ a.d.K := core_le_threeSpaceCores a.d.space
    (a.d.markedPoint 0).property (by intro he; have hh := h.involution; simp [he] at hh)
  obtain ⟨k,hkv⟩ := exists_K_marker_transporter a v hv hne
  let kM : a.P.M := ⟨k,a.K_le_point k.property⟩
  let zM : a.P.M := ⟨z,marker_mem_point a⟩
  let vM : a.P.M := ⟨v,a.P.E_le (a.space_le_E hv)⟩
  have hmark : (pointTwist a w kM : G)*z*(pointTwist a w kM : G)⁻¹=v := by
    have he : kM*zM*kM⁻¹=vM := Subtype.ext hkv
    have hh := congrArg (fun u : a.P.M => (pointTwist a w u : G)) he
    simp only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv] at hh
    rw [show (pointTwist a w zM : G)=z from pointTwist_marker a w,
      pointTwist_fixes_radical a w vM (a.space_le_E hv)] at hh
    exact hh
  apply eq_of_le_of_card_ge
  · rintro m ⟨q,hq,rfl⟩
    change (q : G) ∈ ambientCore v at hq
    have hmap : (ambientCore z).map (MulAut.conj (k : G)).toMonoidHom=ambientCore v := by
      rw [ambientCore_map]
      exact congrArg ambientCore hkv
    rw [←hmap] at hq
    obtain ⟨u,hu,he⟩ := hq
    let uM : a.P.M := ⟨u,a.K_le_point (hzK hu)⟩
    have hqeq : q=kM*uM*kM⁻¹ := Subtype.ext he.symm
    rw [hqeq,map_mul,map_mul,map_inv]
    change (pointTwist a w kM : G)*(pointTwist a w uM : G)*
      (pointTwist a w kM : G)⁻¹ ∈ ambientCore v
    have hmap' : (ambientCore z).map (MulAut.conj (pointTwist a w kM : G)).toMonoidHom =
        ambientCore v := by
      rw [ambientCore_map]
      exact congrArg ambientCore hmark
    rw [←hmap']
    exact mem_map_of_mem _ (pointTwist_core_mem a w uM hu)
  · rw [card_map_of_injective (pointTwist a w).injective]

/-- K is preserved through its actual seven-core construction. No abstract
identification of the line kernel is used. -/
theorem pointTwist_line_kernel (w : Full) :
    (a.d.K.subgroupOf a.P.M).map (pointTwist a w).toMonoidHom=a.d.K.subgroupOf a.P.M := by
  let V := {v : G // v ∈ a.d.space ∧ v ≠ 1}
  let Q : V → Subgroup a.P.M := fun v => (ambientCore v.val).subgroupOf a.P.M
  have hle (v : V) : ambientCore v.val ≤ a.P.M :=
    (core_le_threeSpaceCores a.d.space v.property.1 v.property.2).trans a.K_le_point
  have hgen : (⨆ v : V, Q v)=a.d.K.subgroupOf a.P.M := by
    apply Subgroup.map_injective a.P.M.subtype_injective
    rw [Subgroup.map_iSup,map_subgroupOf_eq_of_le a.K_le_point]
    simp_rw [Q,map_subgroupOf_eq_of_le (hle _)]
    rfl
  rw [←hgen,Subgroup.map_iSup]
  congr 1
  funext v
  exact pointTwist_seven_core a w v.val v.property.1 v.property.2


/-- The source edge-normalizer formula in the exact point group used by the
Todd automorphism. The cubic still comes from Syl₃(S∩M). -/
theorem exists_lineEdge_point_normalizer (t : G) (ht : t ∈ a.L.G₂) (hnt : t ∉ a.P.M) :
    ∃ Y : Sylow 3 (lineCentralPoint a),
      let U := (Y : Subgroup (lineCentralPoint a)).map (lineCentralPoint a).subtype
      (lineEdgeGroup a t).subgroupOf a.P.M = a.d.K.subgroupOf a.P.M ⊔
        (a.d.S.subgroupOf a.P.M ⊓ normalizer (U.subgroupOf a.P.M : Set a.P.M)) := by
  obtain ⟨Y,hY⟩ := exists_lineEdge_ambient_normalizer a t ht hnt
  refine ⟨Y,?_⟩
  dsimp only
  let U := (Y : Subgroup (lineCentralPoint a)).map (lineCentralPoint a).subtype
  have hUM : U ≤ a.P.M := (map_subtype_le _).trans inf_le_right
  rw [hY]
  change (a.d.K ⊔ (lineCentralPoint a ⊓ normalizer (U : Set G))).subgroupOf a.P.M=_
  rw [subgroupOf_sup a.K_le_point (show lineCentralPoint a ⊓ normalizer (U : Set G) ≤ a.P.M
    from fun _ hg => hg.1.2)]
  congr 1
  rw [←subgroupOf_normalizer_eq hUM]
  ext m
  change (((m : G) ∈ a.d.S ∧ (m : G) ∈ a.P.M) ∧ (m : G) ∈ normalizer (U : Set G)) ↔
    ((m : G) ∈ a.d.S ∧ (m : G) ∈ normalizer (U : Set G))
  simp only [m.property,and_true]

private theorem pointCubic_odd (Y : Sylow 3 (lineCentralPoint a)) :
    Odd (Nat.card (((Y : Subgroup (lineCentralPoint a)).map (lineCentralPoint a).subtype).subgroupOf a.P.M)) := by
  have hUM : (Y : Subgroup (lineCentralPoint a)).map (lineCentralPoint a).subtype ≤ a.P.M :=
    (map_subtype_le _).trans inf_le_right
  rw [Nat.card_congr (subgroupOfEquivOfLe hUM).toEquiv,
    card_map_of_injective (lineCentralPoint a).subtype_injective]
  obtain ⟨n,hn⟩ := Y.isPGroup'.exists_card_eq
  rw [hn]
  exact Odd.pow (by decide : Odd 3)

/-- Choose the actual outer Todd correction preserving the entire original
pointwise edge fixer. Its cubic and odd full word are constructed; no edge
map or automorphism classification is an input. This is the normalizer
control used in AS91 (8.2), hypothesis (V2). -/
theorem exists_edge_preserving_Todd_twist (t : G) (ht : t ∈ a.L.G₂) (hnt : t ∉ a.P.M) :
    ∃ (Y : Sylow 3 (lineCentralPoint a)) (w : Full) (v : Cocode),
      let U := (Y : Subgroup (lineCentralPoint a)).map (lineCentralPoint a).subtype
      w ∉ Core ∧
      pointTwist a w=MulAut.conj (a.P.toddEquiv (SemidirectProduct.inl (Multiplicative.ofAdd v))) *
        pointTwist a toddOddWord ∧
      pointTwist a w ^ 2=1 ∧
      (∀ u : U.subgroupOf a.P.M, pointTwist a w u.val=u.val) ∧
      (¬ ∃ x : pointOverlap a, overlapToddTwist a w=MulAut.conj x) ∧
      (lineEdgeGroup a t).subgroupOf a.P.M = a.d.K.subgroupOf a.P.M ⊔
        (a.d.S.subgroupOf a.P.M ⊓ normalizer (U.subgroupOf a.P.M : Set a.P.M)) ∧
      ((lineEdgeGroup a t).subgroupOf a.P.M).map (pointTwist a w).toMonoidHom =
        (lineEdgeGroup a t).subgroupOf a.P.M := by
  obtain ⟨Y,hY⟩ := exists_lineEdge_point_normalizer a t ht hnt
  let U := (Y : Subgroup (lineCentralPoint a)).map (lineCentralPoint a).subtype
  obtain ⟨w,v,hw,hclass,hsq,hfix,houter,_,_,hN⟩ :=
    exists_odd_point_correction a (U.subgroupOf a.P.M) (pointCubic_odd a Y)
  refine ⟨Y,w,v,hw,hclass,hsq,hfix,houter,hY,?_⟩
  rw [hY,Subgroup.map_sup,pointTwist_line_kernel,hN]

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
