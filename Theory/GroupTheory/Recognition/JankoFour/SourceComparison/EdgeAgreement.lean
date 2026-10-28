module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.EdgeControl
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.LocalAgreement
import all Theory.GroupTheory.Recognition.JankoFour.SourceComparison.LocalAgreement
import all Theory.GroupTheory.Recognition.JankoFour.SourceComparison.CentralTwist

/-!
# Simultaneous overlap agreement and full edge-fixer comparison

The overlap factorization permits any odd Todd word. Choose the previously
constructed word preserving the actual edge fixer. Both outer factors then
preserve its plane part. The self-normalizer calculation forces the inner
factor into the edge fixer too, so correcting the point and plane maps
achieves overlap agreement without losing the full edge image.

The central plane twist leaves the endpoint coset unchanged. Consequently
the target edge is still the edge defined by the corrected image of the
original t. The exported maps retain both line flags, the line kernel,
marked involution, scalar cubic, six-cover restriction and M24 projection.
The full edge-reversal conjugation equation remains a further obligation.

Source: Aschbacher--Segev, Invent. Math. 105 (1991), (8.2)--(8.4), pp.606--607.
The internal imports reuse LocalAgreement's overlap restrictions and identify
the original CentralTwist marker, without changing either public boundary.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu MathieuCode
open scoped Pointwise
variable {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
variable {z : G} {z' : G'} {h : IsTypeJ4 z} {h' : IsTypeJ4 z'}
variable (a : SourceIncidence.LocalData h) (a' : SourceIncidence.LocalData h')

private noncomputable def overlapVector (v : Cocode) : PlaneOverlap a :=
  ⟨⟨a.P.toddEquiv (SemidirectProduct.inl (Multiplicative.ofAdd v)), by
    apply (a.point_plane_todd_overlap _).mpr
    change (a.P.toddEquiv.symm (a.P.toddEquiv (SemidirectProduct.inl _))).right • _ = _
    rw [a.P.toddEquiv.symm_apply_apply]
    exact one_smul _ _⟩,(a.P.toddEquiv _).property⟩

private theorem odd_twist_class (w : Full) (hw : w ∉ Core) :
    ∃ v : Cocode, planeOverlapToddTwist a w =
      MulAut.conj (overlapVector a v)*planeOverlapToddTwist a toddOddWord := by
  obtain ⟨v,hv⟩ := toddTwist_odd_class w hw
  refine ⟨v,?_⟩
  have he : pointTwist a w =
      MulAut.conj (a.P.toddEquiv (SemidirectProduct.inl (Multiplicative.ofAdd v)))*
        pointTwist a toddOddWord := by
    rw [pointTwist_eq_congr,hv,map_mul,MulAut.congr_conj,←pointTwist_eq_congr]
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  rw [planeOverlapToddTwist_coe,he]
  rfl

/-- Any chosen odd Todd word may represent the outer factor, in particular
the word constructed to preserve the original full edge fixer. -/
theorem overlap_factorization_odd (w : Full) (hw : w ∉ Core)
    (f : MulAut (PlaneOverlap a)) :
    ∃ (x : PlaneOverlap a) (b c : Bool),
      f=MulAut.conj x*planeOverlapToddTwist a w^b.toNat*overlapPlaneTwist a^c.toNat := by
  obtain ⟨v,hv⟩ := odd_twist_class a (cubicFixedWord a) (cubicFixedWord_odd a)
  obtain ⟨u,hu⟩ := odd_twist_class a w hw
  have hβ : planeOverlapToddTwist a (cubicFixedWord a) =
      MulAut.conj (overlapVector a v*(overlapVector a u)⁻¹)*planeOverlapToddTwist a w := by
    rw [hv,hu,map_mul,map_inv]
    group
  obtain ⟨x,hx⟩ := overlap_automorphism_factorization a f
  rcases hx with hx | hx | hx | hx
  · exact ⟨x,false,false,by simpa only [Bool.toNat_false,pow_zero,mul_one] using hx⟩
  · exact ⟨x,false,true,by simpa only [Bool.toNat_false,Bool.toNat_true,pow_zero,pow_one,mul_one] using hx⟩
  · refine ⟨x*(overlapVector a v*(overlapVector a u)⁻¹),true,false,?_⟩
    simpa only [Bool.toNat_true,Bool.toNat_false,pow_one,pow_zero,mul_one,hβ,map_mul,mul_assoc] using hx
  · refine ⟨x*(overlapVector a v*(overlapVector a u)⁻¹),true,true,?_⟩
    simpa only [Bool.toNat_true,pow_one,hβ,map_mul,mul_assoc] using hx

private theorem subgroup_mem_map_iff {J J' : Type*} [Group J] [Group J']
    (E : J ≃* J') (U : Subgroup J) (V : Subgroup J')
    (hE : U.map E.toMonoidHom=V) (j : J) : E j ∈ V ↔ j ∈ U := by
  rw [←hE]
  exact mem_map_iff_mem E.injective

private def edgeInOverlap (t : centralizer z) : Subgroup (PlaneOverlap a) :=
  ((lineEdgeGroup a t).subgroupOf (centralizer z)).subgroupOf (PlaneOverlap a)

private theorem planeTwist_edge_mem (t k : centralizer z) :
    (planeTwist h a.e k : G) ∈ lineEdgeGroup a t ↔ (k : G) ∈ lineEdgeGroup a t := by
  have hzB : z ∈ lineEdgeGroup a t := by
    refine ⟨marker_mem_point a,?_⟩
    change (t : G)⁻¹*z*((t : G)⁻¹)⁻¹ ∈ a.P.M
    rw [inv_inv]
    have he : (t : G)⁻¹*z*(t : G)=z := by
      have hh := mem_centralizer_singleton_iff.mp t.property
      calc
        _ = (t : G)⁻¹*((t : G)*z) := by rw [hh]; group
        _ = z := inv_mul_cancel_left _ _
    rw [he]
    exact marker_mem_point a
  rw [planeTwist_apply]
  split
  · rfl
  · change (k : G)*z ∈ lineEdgeGroup a t ↔ (k : G) ∈ lineEdgeGroup a t
    exact mul_mem_cancel_right hzB

/-- Normalizer control forces the inner part of an edge-preserving overlap
automorphism into the actual edge subgroup. -/
private theorem factor_conjugator_mem_edge
    (t : centralizer z) (ht : (t : G) ∈ a.L.G₂) (hnt : (t : G) ∉ a.P.M)
    (w : Full) (hwB : ((lineEdgeGroup a t).subgroupOf a.P.M).map
      (pointTwist a w).toMonoidHom=(lineEdgeGroup a t).subgroupOf a.P.M)
    (f : MulAut (PlaneOverlap a))
    (hf : ∀ i, f i ∈ edgeInOverlap a t ↔ i ∈ edgeInOverlap a t)
    (x : PlaneOverlap a) (b c : Bool)
    (he : f=MulAut.conj x*planeOverlapToddTwist a w^b.toNat*overlapPlaneTwist a^c.toNat) :
    x.val.val ∈ lineEdgeGroup a t := by
  let α := overlapPlaneTwist a^c.toNat
  let β := planeOverlapToddTwist a w^b.toNat
  have hα (i : PlaneOverlap a) : α i ∈ edgeInOverlap a t ↔ i ∈ edgeInOverlap a t := by
    cases c
    · rfl
    · exact planeTwist_edge_mem a t i.val
  have hβ (i : PlaneOverlap a) : β i ∈ edgeInOverlap a t ↔ i ∈ edgeInOverlap a t := by
    cases b
    · rfl
    · change (planeOverlapToddTwist a w i).val.val ∈ lineEdgeGroup a t ↔ _
      rw [planeOverlapToddTwist_coe]
      exact subgroup_mem_map_iff (pointTwist a w) _ _ hwB (overlapPointHom a i)
  have hx : MulAut.conj x=f*α*β := by
    have hh : f*α=MulAut.conj x*β := by
      rw [he,mul_assoc,show overlapPlaneTwist a^c.toNat*α=1 from
        involutory_bool_power _ (overlapPlaneTwist_sq a) c,mul_one]
    have hbβ : β*β=1 := involutory_bool_power _ (planeOverlapToddTwist_sq a w) b
    symm
    rw [hh,mul_assoc,hbβ,mul_one]
  have hxJ (i : PlaneOverlap a) : x*i*x⁻¹ ∈ edgeInOverlap a t ↔ i ∈ edgeInOverlap a t := by
    change MulAut.conj x i ∈ edgeInOverlap a t ↔ _
    rw [hx]
    exact (hf (α (β i))).trans ((hα (β i)).trans (hβ i))
  have hn : x.val ∈ normalizer ((lineEdgeGroup a t).subgroupOf (centralizer z) : Set (centralizer z)) := by
    apply mem_normalizer_iff.mpr
    intro k
    constructor
    · intro hk
      have hkM : (k : G) ∈ a.P.M := hk.1
      exact (hxJ ⟨k,hkM⟩).mpr hk
    · intro hk
      have hkM : (k : G) ∈ a.P.M := by
        have hm := a.P.M.mul_mem (a.P.M.mul_mem (a.P.M.inv_mem x.property) hk.1) x.property
        change x.val.val⁻¹*(x.val.val*(k : G)*x.val.val⁻¹)*x.val.val ∈ a.P.M at hm
        have he : x.val.val⁻¹*(x.val.val*(k : G)*x.val.val⁻¹)*x.val.val=(k : G) := by group
        rwa [he] at hm
      exact (hxJ ⟨k,hkM⟩).mp hk
  have heq := EdgeControl.edgePlane_normalizer a t ht hnt
  change x.val ∈ (lineEdgeGroup a t).subgroupOf (centralizer z)
  rw [←heq]
  exact ⟨x.property,hn⟩

private theorem align_edge_equivs
    (H : centralizer z ≃* centralizer z')
    (hH : (PlaneOverlap a).map H.toMonoidHom=PlaneOverlap a')
    (M : a.P.M ≃* a'.P.M)
    (hM : (pointOverlap a).map M.toMonoidHom=pointOverlap a')
    (t : centralizer z) (ht : (t : G) ∈ a.L.G₂) (hnt : (t : G) ∉ a.P.M)
    (hMB : ((lineEdgeGroup a t).subgroupOf a.P.M).map M.toMonoidHom =
      (lineEdgeGroup a' (H t)).subgroupOf a'.P.M) :
    ∃ (w : Full) (x : PlaneOverlap a) (b c : Bool),
      ((lineEdgeGroup a t).subgroupOf a.P.M).map (pointTwist a w).toMonoidHom =
        (lineEdgeGroup a t).subgroupOf a.P.M ∧
      x.val.val ∈ lineEdgeGroup a t ∧
      ∀ i : PlaneOverlap a,
        (M ((MulAut.conj (overlapPointHom a x)*pointTwist a w^b.toNat)
          (overlapPointHom a i))).val =
        (H (((planeTwist h a.e)^c.toNat) i.val)).val := by
  obtain ⟨_,w,_,hw,_,_,_,_,_,hwB⟩ := exists_edge_preserving_Todd_twist a t ht hnt
  let u := restrictPlane a a' H hH
  let v := restrictPoint a a' M hM
  let f := u.trans v.symm
  have hHB : ((lineEdgeGroup a t).subgroupOf (centralizer z)).map H.toMonoidHom =
      (lineEdgeGroup a' (H t)).subgroupOf (centralizer z') := by
    simpa only [Cosets.edgeFixer_eq,lineEdgeGroup] using (planeEquiv_local_edge_images a a' H hH t).1
  have hu (i : PlaneOverlap a) : (u i).val.val ∈ lineEdgeGroup a' (H t) ↔
      i ∈ edgeInOverlap a t := subgroup_mem_map_iff H _ _ hHB i.val
  have hv (i : PlaneOverlap a) : (v i).val.val ∈ lineEdgeGroup a' (H t) ↔
      i ∈ edgeInOverlap a t := subgroup_mem_map_iff M _ _ hMB (overlapPointHom a i)
  have hf (i : PlaneOverlap a) : f i ∈ edgeInOverlap a t ↔ i ∈ edgeInOverlap a t := by
    rw [←hv (f i),show v (f i)=u i from v.apply_symm_apply _]
    exact hu i
  obtain ⟨x,b,c,he⟩ := overlap_factorization_odd a w hw f
  have hx := factor_conjugator_mem_edge a t ht hnt w hwB f hf x b c he
  let α := overlapPlaneTwist a^c.toNat
  let β := planeOverlapToddTwist a w^b.toNat
  have hα (i : PlaneOverlap a) : (α i).val=((planeTwist h a.e)^c.toNat) i.val := by
    cases c <;> simp only [α,Bool.toNat_false,Bool.toNat_true,pow_zero,pow_one,
      MulAut.one_apply,overlapPlaneTwist_coe]
  have hβ (i : PlaneOverlap a) : overlapPointHom a (β i)=
      (pointTwist a w^b.toNat) (overlapPointHom a i) := by
    cases b
    · rfl
    · apply Subtype.ext
      exact planeOverlapToddTwist_coe a w i
  have hprod (i : PlaneOverlap a) :
      overlapPointHom a ((MulAut.conj x*β) i)=
        (MulAut.conj (overlapPointHom a x)*pointTwist a w^b.toNat)
          (overlapPointHom a i) := by
    change overlapPointHom a (x*β i*x⁻¹)=_
    rw [map_mul,map_mul,map_inv,hβ]
    rfl
  have hfα : f*α=MulAut.conj x*β := by
    rw [he,mul_assoc,show overlapPlaneTwist a^c.toNat*α=1 from
      involutory_bool_power _ (overlapPlaneTwist_sq a) c,mul_one]
  refine ⟨w,x,b,c,hwB,hx,fun i => ?_⟩
  have hvu : v (f (α i))=u (α i) := v.apply_symm_apply _
  rw [show f (α i)=(MulAut.conj x*β) i from MulEquiv.congr_fun hfα i] at hvu
  have hh := congrArg (fun j : PlaneOverlap a' => j.val.val) hvu
  change (M (overlapPointHom a ((MulAut.conj x*β) i))).val = (H (α i).val).val at hh
  rwa [hprod,hα] at hh

private theorem planeTwist_vertex (t : centralizer z) (c : Bool) :
    Cosets.vertex a.P.M (((planeTwist h a.e)^c.toNat) t : G)=Cosets.vertex a.P.M (t : G) := by
  cases c
  · rfl
  · change Cosets.vertex a.P.M (planeTwist h a.e t : G)=_
    rw [planeTwist_apply]
    split
    · rfl
    · apply (Cosets.vertex_eq_iff _ _ _).mpr
      change ((t : G)*z)⁻¹*(t : G) ∈ a.P.M
      rw [mul_inv_rev,inv_mul_cancel_right]
      exact a.P.M.inv_mem (marker_mem_point a)

/-- Construct local isomorphisms that agree on the literal overlap and
simultaneously preserve the entire original edge fixer. The target edge is
defined by the image of the original reversal element. -/
theorem exists_compatible_edge_equivs (d : CubicNormalizerData a) (d' : CubicNormalizerData a')
    (t : centralizer z) (ht : (t : G) ∈ a.L.G₂) (hnt : (t : G) ∉ a.P.M) :
    ∃ (C : cubicCentralizerInH a.e a.X ≃* cubicCentralizerInH a'.e a'.X)
      (n : cubicNormalizerInH a'.e a'.X) (g : M24)
      (φM : a.P.M ≃* a'.P.M) (φH : centralizer z ≃* centralizer z'),
      (∀ c, cubicNativeProjection h' a'.e a'.X (C c)=cubicNativeProjection h a.e a.X c) ∧
      φH planeMarker=planeMarker ∧
      (∀ c : cubicCentralizerInH a.e a.X,
        φH c.val=(cubicNormalizerAction a'.e a'.X n (C c)).val) ∧
      (core z).map φH.toMonoidHom=core z' ∧
      (cubicSylowImage a.e a.X).map φH.toMonoidHom=cubicSylowImage a'.e a'.X ∧
      (φM ⟨z,marker_mem_point a⟩ : G')=z' ∧
      (a.L.G₂.subgroupOf (centralizer z)).map φH.toMonoidHom=a'.L.G₂.subgroupOf (centralizer z') ∧
      (a.L.G₂.subgroupOf a.P.M).map φM.toMonoidHom=a'.L.G₂.subgroupOf a'.P.M ∧
      (a.d.K.subgroupOf a.P.M).map φM.toMonoidHom=a'.d.K.subgroupOf a'.P.M ∧
      (∀ m, a'.P.projection (φM m)=g*a.P.projection m*g⁻¹) ∧
      (∀ (k : G) (hkM : k ∈ a.P.M) (hkH : k ∈ centralizer z),
        (φM ⟨k,hkM⟩ : G')=(φH ⟨k,hkH⟩ : G')) ∧
      ((lineEdgeGroup a t).subgroupOf a.P.M).map φM.toMonoidHom =
        (lineEdgeGroup a' (φH t)).subgroupOf a'.P.M := by
  obtain ⟨C,n,g₀,M,H,hC,hz,hHC,_,hA,hHI,hHL,_,hMp,hMI,hML,hMB⟩ :=
    exists_local_edge_equivs a a' d d' t ht hnt
  obtain ⟨w,x,b,c,hwB,hxB,hagree⟩ := align_edge_equivs a a' H hHI M hMI t ht hnt hMB
  let α := (planeTwist h a.e)^c.toNat
  let β := pointTwist a w^b.toNat
  let φH := α.trans H
  let φM := (MulAut.conj (overlapPointHom a x)*β).trans M
  have hfix (q : cubicCentralizerInH a.e a.X) : α q.val=q.val := by
    cases c
    · rfl
    · exact planeTwist_fixes_cubicCentralizer h a.e a.X q
  have hzα : α planeMarker=planeMarker :=
    hfix ⟨planeMarker,center_le_centralizer _ planeMarker_central⟩
  have hαA : (cubicSylowImage a.e a.X).map α.toMonoidHom=cubicSylowImage a.e a.X := by
    have hf (k) (hk : k ∈ cubicSylowImage a.e a.X) : α k=k :=
      hfix ⟨k,cubicSylowImage_le_centralizer h a.e a.X hk⟩
    ext k
    constructor
    · rintro ⟨y,hy,rfl⟩
      change α y ∈ cubicSylowImage a.e a.X
      rwa [hf y hy]
    · intro hk
      exact ⟨k,hk,hf k hk⟩
  have hφA : (cubicSylowImage a.e a.X).map φH.toMonoidHom=cubicSylowImage a'.e a'.X := by
    change (cubicSylowImage a.e a.X).map (H.toMonoidHom.comp α.toMonoidHom)=_
    rw [←map_map,hαA,hA]
  have hzL : z ∈ a.L.G₂ := by
    rw [a.line_normalizer]
    exact le_normalizer (a.d.markedPoint 0).property
  have hαL : (a.L.G₂.subgroupOf (centralizer z)).map α.toMonoidHom =
      a.L.G₂.subgroupOf (centralizer z) := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨k,hk,rfl⟩
      cases c
      · exact hk
      · change (planeTwist h a.e k : G) ∈ a.L.G₂
        rw [planeTwist_apply]
        split
        · exact hk
        · exact a.L.G₂.mul_mem hk hzL
    · rw [card_map_of_injective α.injective]
  have hφHL : (a.L.G₂.subgroupOf (centralizer z)).map φH.toMonoidHom =
      a'.L.G₂.subgroupOf (centralizer z') := by
    change (a.L.G₂.subgroupOf (centralizer z)).map (H.toMonoidHom.comp α.toMonoidHom)=_
    rw [←Subgroup.map_map,hαL,hHL]
  have hβL : (a.L.G₂.subgroupOf a.P.M).map β.toMonoidHom=a.L.G₂.subgroupOf a.P.M := by
    cases b
    · exact Subgroup.map_id _
    · exact (pointTwist_flags a w).2.1
  have hxL : (a.L.G₂.subgroupOf a.P.M).map (MulAut.conj (overlapPointHom a x)).toMonoidHom =
      a.L.G₂.subgroupOf a.P.M :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer (lineEdgeGroup_le_line a t ht hnt hxB))
  have hφML : (a.L.G₂.subgroupOf a.P.M).map φM.toMonoidHom = a'.L.G₂.subgroupOf a'.P.M := by
    change (a.L.G₂.subgroupOf a.P.M).map
      (M.toMonoidHom.comp ((MulAut.conj (overlapPointHom a x)).toMonoidHom.comp β.toMonoidHom)) = _
    rw [←Subgroup.map_map,←Subgroup.map_map,hβL,hxL,hML]
  have hφMz : (φM ⟨z,marker_mem_point a⟩ : G')=z' := by
    have he := hagree ⟨planeMarker,marker_mem_point a⟩
    change (φM ⟨z,marker_mem_point a⟩ : G')=(H (α planeMarker) : G') at he
    rw [hzα,hz] at he
    exact he
  have hβp (m : a.P.M) : a.P.projection (β m)=a.P.projection m := by
    cases b
    · rfl
    · exact pointTwist_projection a w m
  refine ⟨C,n,g₀*a.P.projection (overlapPointHom a x),φM,φH,hC,?_,?_,
    planeEquiv_core_map h h' φH,hφA,hφMz,hφHL,hφML,
    pointMap_line_kernel a a' φM hφMz hφML,?_,?_,?_⟩
  · change H (α planeMarker)=planeMarker
    rw [hzα,hz]
  · intro q
    change H (α q.val)=_
    rw [hfix,hHC]
  · intro m
    change a'.P.projection (M ((MulAut.conj (overlapPointHom a x)*β) m))=_
    rw [hMp]
    change g₀*a.P.projection (overlapPointHom a x*β m*(overlapPointHom a x)⁻¹)*g₀⁻¹=_
    rw [map_mul,map_mul,map_inv,hβp]
    group
  · intro k hkM hkH
    exact hagree ⟨⟨k,hkH⟩,hkM⟩
  · have hβB : ((lineEdgeGroup a t).subgroupOf a.P.M).map β.toMonoidHom =
        (lineEdgeGroup a t).subgroupOf a.P.M := by
      cases b
      · exact Subgroup.map_id _
      · exact hwB
    have hxB' : ((lineEdgeGroup a t).subgroupOf a.P.M).map
        (MulAut.conj (overlapPointHom a x)).toMonoidHom =
          (lineEdgeGroup a t).subgroupOf a.P.M :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer hxB)
    have he : lineEdgeGroup a' (φH t)=lineEdgeGroup a' (H t) := by
      have htcos := (planeEquiv_coset_eq_iff a a' H hHI (α t) t).mpr
        (planeTwist_vertex a t c)
      change a'.P.M ⊓ a'.P.M.comap (MulAut.conj (H (α t) : G')⁻¹).toMonoidHom = _
      simp only [lineEdgeGroup]
      rw [←Cosets.edgeFixer_eq,←Cosets.edgeFixer_eq,htcos]
    change ((lineEdgeGroup a t).subgroupOf a.P.M).map
      (M.toMonoidHom.comp ((MulAut.conj (overlapPointHom a x)).toMonoidHom.comp β.toMonoidHom)) = _
    rw [←Subgroup.map_map,←Subgroup.map_map,hβB,hxB',hMB,he]

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
