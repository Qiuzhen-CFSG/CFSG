module
public import CFSG.Quasithin.ChapterJ.Section05.SourceRecognition.NeighborRows
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.Points

/-!
# All automorphisms of the original Rudvalis orbital graph

The complement of each original local graph is the actual binary-building
opposition relation. Its checked automorphism theorem identifies a base fixer
on the first orbit; the common-neighbor row lemma then determines its action
on every vertex. Transitivity and the original faithful action yield the
unique ambient group element inducing an arbitrary graph automorphism.
Source: Aschbacher–Smith J.5.6, printed p.447.
-/

@[expose] public section
noncomputable section
open Subgroup MulAction
open ReeF4.Octagon.Binary
attribute [local instance] Automorphisms.FiniteBridge.pointAction
namespace CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
variable {G:Type*} [Group G] [Finite G]
variable (F:Subgroup G) (q:G) (hq:q∉F) (hs:q•(q•basePoint F)=basePoint F) {g:G}
variable (h:RudvalisAction F (q•basePoint F) (g•basePoint F))
include h

theorem local_opposition_iff (u v:orbit F (q•basePoint F)) :
    pointDistance (h.pointEquiv u) (h.pointEquiv v)=8 ↔
      u≠v ∧ ¬(sourceGraph F q hq hs).Adj u.val v.val := by
  let d:orbit F (q•basePoint F):=⟨q•basePoint F,mem_orbit_self _⟩
  obtain ⟨f,hf⟩:=exists_smul_eq F d u
  let w:=f⁻¹•v
  have hv:f•w=v:=smul_inv_smul f v
  have hd:pointDistance (h.pointEquiv u) (h.pointEquiv v)=
      pointDistance (h.pointEquiv d) (h.pointEquiv w) := by
    rw [←hf,←hv,h.pointEquiv_smul,h.pointEquiv_smul,pointDistance_smul]
  have hdist : h.localDistance d w=4 ↔ pointDistance (h.pointEquiv d) (h.pointEquiv w)=8 := by
    simpa using h.localDistance_eq_iff d w (4:Fin 5)
  rw [hd,←hdist]
  have hn:=h.localNonneighbors_iff_opposite F q hq hs w
  change (w.val≠d.val ∧ ¬(sourceGraph F q hq hs).Adj d.val w.val) ↔ _ at hn
  rw [←hn]
  have he : w.val≠d.val ↔ u≠v := by
    constructor
    · intro hh huv
      apply hh
      apply congrArg Subtype.val
      exact (MulAction.toPerm f).injective (hv.trans (huv.symm.trans hf.symm))
    · intro hh he
      apply hh
      exact hf.symm.trans ((congrArg (fun z=>f•z) (Subtype.ext he).symm).trans hv)
  rw [he]
  have ha:=sourceGraph_adj_smul F q hq hs (f:G) d.val w.val
  have hfu:(f:G)•d.val=u.val:=congrArg Subtype.val hf
  have hfv:(f:G)•w.val=v.val:=congrArg Subtype.val hv
  rw [hfu,hfv] at ha
  exact and_congr Iff.rfl (not_congr ha.symm)

/-- Restrict a source graph automorphism fixing the base to its actual neighbor orbit. -/
def neighborEquiv (a:sourceGraph F q hq hs ≃g sourceGraph F q hq hs)
    (ha:a (basePoint F)=basePoint F) :
    orbit F (q•basePoint F) ≃ orbit F (q•basePoint F) :=
  a.toEquiv.subtypeEquiv (fun x=>by
    rw [←sourceGraph_neighbor_base F q hq hs]
    change (sourceGraph F q hq hs).Adj (basePoint F) x ↔
      (sourceGraph F q hq hs).Adj (basePoint F) (a x)
    simpa only [ha] using (a.map_adj_iff (v:=basePoint F) (w:=x)).symm)

theorem base_fixer_neighbor_action
    (a:sourceGraph F q hq hs ≃g sourceGraph F q hq hs)
    (ha:a (basePoint F)=basePoint F) :
    ∃f:F,∀x∈orbit F (q•basePoint F),a x=(f:G)•x := by
  let b:=neighborEquiv F q hq hs a ha
  let e:PointCoset≃PointCoset:=h.pointEquiv.symm.trans (b.trans h.pointEquiv)
  have he:∀u v,pointDistance (e u) (e v)=8 ↔ pointDistance u v=8 := by
    intro u v
    obtain ⟨x,rfl⟩:=h.pointEquiv.surjective u
    obtain ⟨y,rfl⟩:=h.pointEquiv.surjective v
    change pointDistance (h.pointEquiv (b (h.pointEquiv.symm (h.pointEquiv x))))
      (h.pointEquiv (b (h.pointEquiv.symm (h.pointEquiv y))))=8 ↔ _
    rw [h.pointEquiv.symm_apply_apply,h.pointEquiv.symm_apply_apply,
      h.local_opposition_iff F q hq hs,h.local_opposition_iff F q hq hs]
    have hab: (sourceGraph F q hq hs).Adj (b x).val (b y).val ↔
        (sourceGraph F q hq hs).Adj x.val y.val := a.map_adj_iff
    rw [hab,b.injective.ne_iff]
  obtain ⟨r,hr⟩:=Automorphisms.opposition_equiv_eq_left_action e he
  refine ⟨h.marking.symm r,?_⟩
  intro x hx
  let v:orbit F (q•basePoint F):=⟨x,hx⟩
  have hh:b v=h.marking.symm r•v := by
    apply h.pointEquiv.injective
    rw [h.pointEquiv_smul,h.marking.apply_symm_apply]
    simpa only [e,Equiv.trans_apply,Equiv.symm_apply_apply] using hr (h.pointEquiv v)
  exact congrArg Subtype.val hh

/-- The original left translation, with the original orbital adjacency. -/
def sourceTranslation (k:G) : sourceGraph F q hq hs ≃g sourceGraph F q hq hs :=
  { toEquiv:=MulAction.toPerm k
    map_rel_iff':=sourceGraph_adj_smul F q hq hs k _ _ }

theorem base_fixer_eq_left_action
    (a:sourceGraph F q hq hs ≃g sourceGraph F q hq hs)
    (ha:a (basePoint F)=basePoint F) :
    ∃f:F,∀x:Cosets F,a x=(f:G)•x := by
  obtain ⟨f,hf⟩:=h.base_fixer_neighbor_action F q hq hs a ha
  let b:=a.trans (sourceTranslation F q hq hs (f:G)⁻¹)
  have hb:b=SimpleGraph.Iso.refl:=h.fix_base_neighbors_eq_refl F q hq hs b (by
    change (f:G)⁻¹•a (basePoint F)=basePoint F
    rw [ha]
    exact basePoint_fixed F f⁻¹) (by
    intro x hx
    change (f:G)⁻¹•a x=x
    rw [hf x hx,inv_smul_smul])
  refine ⟨f,fun x=>?_⟩
  have he:=congrArg (fun t:sourceGraph F q hq hs ≃g sourceGraph F q hq hs=>t x) hb
  change (f:G)⁻¹•a x=x at he
  exact (inv_smul_eq_iff).mp he

/-- J.5.6: every automorphism of the unchanged original orbital graph is a
unique original group translation. -/
theorem source_graph_automorphism_eq_unique_left_action
    (a:sourceGraph F q hq hs ≃g sourceGraph F q hq hs) :
    ∃!k:G,∀x:Cosets F,a x=k•x := by
  obtain ⟨k,hk⟩:=exists_smul_eq G (basePoint F) (a (basePoint F))
  let b:=a.trans (sourceTranslation F q hq hs k⁻¹)
  have hb:b (basePoint F)=basePoint F:=by
    change k⁻¹•a (basePoint F)=basePoint F
    rw [←hk,inv_smul_smul]
  obtain ⟨f,hf⟩:=h.base_fixer_eq_left_action F q hq hs b hb
  have he:∀x:Cosets F,a x=(k*(f:G))•x:=by
    intro x
    have hh:=hf x
    change k⁻¹•a x=(f:G)•x at hh
    rw [mul_smul]
    exact inv_smul_eq_iff.mp hh
  refine ⟨k*(f:G),he,?_⟩
  intro t ht
  let := h.faithful
  exact eq_of_smul_eq_smul (fun x=>(ht x).symm.trans (he x))
end CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
