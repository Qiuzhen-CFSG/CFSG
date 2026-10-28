module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.EdgeReversal
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Input
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.ComponentGeometry
public import Theory.GroupTheory.GraphUniquenessSystem.UniversalCompletion.LocalHom
/-!
# AS91 recognition through the original source cycle base

Construct the two local isomorphisms, with their overlap agreement and full
edge-reversal equation, from the unchanged source and target LocalData and
original cubic-normalizer clauses. The incidence constructor supplies the
source Input on the same P and L. Its cycle base extends the maps by the
direct LocalHom theorem. Target generation gives surjectivity; source
simplicity and the nonidentity marked involution give injectivity.

The recognition equivalence retains both local restrictions, the marker,
scalar cubic, core, six-cover comparison, both line flags and M24 projection.
Only the source is assumed simple. Native local-data construction and its
literal generation equality remain the earlier-source owner's obligations.

Source: Aschbacher--Segev (1991), section 8, pp.605--607; source-base extension
as in Aschbacher, Sporadic Groups, 37.4--37.7.
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry SourceCycleBase GraphUniquenessSystem
open scoped IsMulCommutative Pointwise
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
variable (a : SourceIncidence.LocalData h)
variable {G' : Type*} [Group G'] [Finite G'] {z' : G'} {h' : IsTypeJ4 z'}
variable (a' : SourceIncidence.LocalData h')
/-- Extend the constructed local comparisons through the source cycle base.
Only the source group is assumed simple; the target requires its actual two
local subgroups to generate. Both local restriction equations are retained. -/
theorem exists_recognition_equiv [IsSimpleGroup G]
    (d : CubicNormalizerData a) (d' : CubicNormalizerData a')
    (generate' : centralizer z' ⊔ a'.P.M=⊤) :
    ∃ (C : cubicCentralizerInH a.e a.X ≃* cubicCentralizerInH a'.e a'.X)
      (n : cubicNormalizerInH a'.e a'.X) (g : Sporadic.Mathieu.M24)
      (M : a.P.M ≃* a'.P.M) (H : centralizer z ≃* centralizer z') (F : G ≃* G'),
      (∀ q, cubicNativeProjection h' a'.e a'.X (C q)=cubicNativeProjection h a.e a.X q) ∧
      H planeMarker=planeMarker ∧
      (∀ q : cubicCentralizerInH a.e a.X,
        H q.val=(cubicNormalizerAction a'.e a'.X n (C q)).val) ∧
      (core z).map H.toMonoidHom=core z' ∧
      (cubicSylowImage a.e a.X).map H.toMonoidHom=cubicSylowImage a'.e a'.X ∧
      (a.L.G₂.subgroupOf (centralizer z)).map H.toMonoidHom=a'.L.G₂.subgroupOf (centralizer z') ∧
      (a.L.G₂.subgroupOf a.P.M).map M.toMonoidHom=a'.L.G₂.subgroupOf a'.P.M ∧
      (a.d.K.subgroupOf a.P.M).map M.toMonoidHom=a'.d.K.subgroupOf a'.P.M ∧
      (∀ m, a'.P.projection (M m)=g*a.P.projection m*g⁻¹) ∧
      (∀ m : a.P.M, F m=(M m : G')) ∧
      (∀ k : centralizer z, F k=(H k : G')) ∧ F z=z' := by
  let c := SourceIncidence.source_input_of_local_data h a
  obtain ⟨C,n,g,M,H,hC,hz,hHC,hQ,hA,hMz,hHL,hML,hK,hproj,hagree,_,hrev⟩ :=
    exists_compatible_edge_reversal a a' d d' ⟨c.t,c.t_plane⟩ c.t_line c.t_not_point c.t_sq
  let U := c.system
  have hv : U.vertexGroup=a.P.M := Cosets.stabilizer_base a.P.M
  let v : U.vertexGroup →* G' := a'.P.M.subtype.comp
    (M.toMonoidHom.comp (MulEquiv.subgroupCongr hv).toMonoidHom)
  let l : U.H →* G' := (centralizer z').subtype.comp H.toMonoidHom
  let t : U.H := ⟨c.t,c.t_plane⟩
  have htx : (t : G) • U.x=U.y := by
    change c.t • Cosets.vertex a.P.M 1=Cosets.vertex a.P.M c.t
    rw [Cosets.smul_vertex,mul_one]
  have hty : (t : G) • U.y=U.x := by
    change c.t • Cosets.vertex a.P.M c.t=Cosets.vertex a.P.M 1
    rw [Cosets.smul_vertex]
    exact (Cosets.vertex_eq_base _ _).mpr c.t_sq
  have hvl (k : G) (hkH : k ∈ U.H) (hkv : k ∈ U.vertexGroup) :
      v ⟨k,hkv⟩=l ⟨k,hkH⟩ := hagree k (hv ▸ hkv) hkH
  have hedge : U.edgeGroup=lineEdgeGroup a c.t := Cosets.edgeFixer_eq a.P.M c.t
  have hconj (b : U.edgeGroup) :
      v ⟨(t : G)*b*(t : G)⁻¹,(U.conj_mem_edgeGroup htx hty b.property).1⟩ =
        l t*v ⟨b,b.property.1⟩*(l t)⁻¹ :=
    hrev ⟨b,hedge ▸ b.property⟩
  obtain ⟨f,⟨hfv,hfl⟩,_⟩ := U.existsUnique_hom_of_local_conjugation v l hvl t htx hty hconj c.source_isBase
  have hfM (m : a.P.M) : f m=(M m : G') := hfv ⟨m,hv.symm ▸ m.property⟩
  have hfH (k : centralizer z) : f k=(H k : G') := hfl k
  have hsurj : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [←generate']
    apply sup_le
    · intro x hx
      obtain ⟨k,hk⟩ := H.surjective ⟨x,hx⟩
      exact ⟨k,(hfH k).trans (congrArg Subtype.val hk)⟩
    · intro x hx
      obtain ⟨m,hm⟩ := M.surjective ⟨x,hx⟩
      exact ⟨m,(hfM m).trans (congrArg Subtype.val hm)⟩
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker inferInstance) with hk | hk
    · exact hk
    · have hfz : f z=1 := MonoidHom.mem_ker.mp (hk.symm ▸ mem_top z)
      have hz' : f z=z' := by
        simpa only [planeMarker_val] using (hfH planeMarker).trans (congrArg Subtype.val hz)
      have hi := h'.involution
      rw [hz'.symm.trans hfz,orderOf_one] at hi
      contradiction
  let F := MulEquiv.ofBijective f ⟨hinj,hsurj⟩
  exact ⟨C,n,g,M,H,F,hC,hz,hHC,hQ,hA,hHL,hML,hK,hproj,hfM,hfH,
    by
      change f z=z'
      simpa only [planeMarker_val] using (hfH planeMarker).trans (congrArg Subtype.val hz)⟩


end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
