module
public import CFSG.Quasithin.ChapterJ.Section05.SourceGeometry.Source

/-!
# Transitivity on the780 common neighbors

Normalize each two-path at its middle point using the original q that exchanges
the first edge. Its outer endpoints become opposite building points. The proved
first-parabolic transitivity on opposites then identifies the two paths, fixing
the original outer endpoints. Orbit–stabilizer gives the exact order20 of their
three-point stabilizer. No subgroup classification is used in this argument.

Source: Aschbacher–Smith J.5.5(4), printed p.446.
-/

public noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
variable {G:Type*} [Group G] [Finite G] (F:Subgroup G) (q:G) (hq:q∉F)
    (hs:q•(q•basePoint F)=basePoint F) {g:G}
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F))

include h

omit [Finite G] in
private theorem second_not_adjacent :
    g•basePoint F≠basePoint F ∧ ¬(sourceGraph F q hq hs).Adj (basePoint F) (g•basePoint F) := by
  have hg:g•basePoint F∈(({basePoint F}:Set (Cosets F))∪orbit F (q•basePoint F))ᶜ:=
    h.partition ▸ mem_orbit_self _
  refine ⟨fun he=>hg (Or.inl he),?_⟩
  intro he
  have hm:g•basePoint F∈(sourceGraph F q hq hs).neighborSet (basePoint F):=he
  exact hg (Or.inr ((sourceGraph_neighbor_base F q hq hs).le hm))

omit [Finite G] in
private theorem normalize_common_neighbor
    (x:(sourceGraph F q hq hs).commonNeighbors (basePoint F) (g•basePoint F)) :
    ∃a:G,a•basePoint F=q•basePoint F ∧ a•x.val=basePoint F ∧
      ∃w:orbit F (q•basePoint F),a•(g•basePoint F)=w.val ∧
        w∈localNonneighbors F q hq hs := by
  have hx:x.val∈orbit F (q•basePoint F):=
    (sourceGraph_neighbor_base F q hq hs).le x.property.1
  obtain ⟨f,hf⟩:=hx
  change (f:G)•(q•basePoint F)=x.val at hf
  let a: G := ((f:G)*q)⁻¹
  have hax:a•x.val=basePoint F:=by
    apply inv_smul_eq_iff.mpr
    exact hf.symm.trans (mul_smul (f:G) q (basePoint F)).symm
  have ha0:a•basePoint F=q•basePoint F:=by
    apply inv_smul_eq_iff.mpr
    exact (basePoint_fixed F f).symm.trans
      ((congrArg (fun z:Cosets F=>(f:G)•z) hs.symm).trans
        (mul_smul (f:G) q (q•basePoint F)).symm)
  have hadj:(sourceGraph F q hq hs).Adj (basePoint F) (a•(g•basePoint F)):=by
    have hx':=(sourceGraph_adj_smul F q hq hs a x.val (g•basePoint F)).mpr x.property.2.symm
    rwa [hax] at hx'
  let w:orbit F (q•basePoint F):=⟨a•(g•basePoint F),
    (sourceGraph_neighbor_base F q hq hs).le hadj⟩
  refine ⟨a,ha0,hax,w,rfl,?_,?_⟩
  · intro he
    exact (second_not_adjacent F q hq hs h).1
      ((MulAction.injective a) (he.trans ha0.symm))
  · intro he
    apply (second_not_adjacent F q hq hs h).2
    apply (sourceGraph_adj_smul F q hq hs a (basePoint F) (g•basePoint F)).mp
    rwa [ha0]

/-- The pair stabilizer is transitive on the780 common neighbors. -/
theorem common_neighbors_transitive
    (x y:(sourceGraph F q hq hs).commonNeighbors (basePoint F) (g•basePoint F)) :
    ∃k:stabilizer F (g•basePoint F),k•x.val=y.val := by
  obtain ⟨a,ha0,hax,u,hau,hu⟩:=normalize_common_neighbor F q hq hs h x
  obtain ⟨b,hb0,hby,v,hbv,hv⟩:=normalize_common_neighbor F q hq hs h y
  have huu:= (h.localNonneighbors_iff_opposite F q hq hs u).mp hu
  have hvv:= (h.localNonneighbors_iff_opposite F q hq hs v).mp hv
  obtain ⟨f,hf⟩:=h.first_stabilizer_transitive u v (huu.trans hvv.symm)
  have hfp:(f.val:G)•(q•basePoint F)=q•basePoint F:=f.property
  have hf0:(f.val:G)•basePoint F=basePoint F:=basePoint_fixed F f.val
  have hfu:(f.val:G)•u.val=v.val:=congrArg Subtype.val hf
  let k:G:=b⁻¹*(f.val:G)*a
  have hact (z:Cosets F):k•z=b⁻¹•((f.val:G)•(a•z)):=
    (mul_smul (b⁻¹*(f.val:G)) a z).trans (mul_smul b⁻¹ (f.val:G) (a•z))
  have hk0:k•basePoint F=basePoint F:=
    (hact _).trans ((congrArg (fun z:Cosets F=>b⁻¹•z)
      ((congrArg (fun z:Cosets F=>(f.val:G)•z) ha0).trans hfp)).trans
        (inv_smul_eq_iff.mpr hb0.symm))
  have hkg:k•(g•basePoint F)=g•basePoint F:=
    (hact _).trans ((congrArg (fun z:Cosets F=>b⁻¹•z)
      ((congrArg (fun z:Cosets F=>(f.val:G)•z) hau).trans hfu)).trans
        (inv_smul_eq_iff.mpr hbv.symm))
  have hkx:k•x.val=y.val:=
    (hact _).trans ((congrArg (fun z:Cosets F=>b⁻¹•z)
      ((congrArg (fun z:Cosets F=>(f.val:G)•z) hax).trans hf0)).trans
        (inv_smul_eq_iff.mpr hby.symm))
  have hkF:k∈F:=(stabilizer_quotient F).le hk0
  exact ⟨⟨⟨k,hkF⟩,hkg⟩,hkx⟩

omit [Finite G] in
theorem second_stabilizer_card : Nat.card (stabilizer F (g•basePoint F))=15600 := by
  have hc:=Nat.card_congr (orbitProdStabilizerEquivGroup F (g•basePoint F))
  rw [Nat.card_prod,h.second_length] at hc
  have hf:Nat.card F=35942400:=
    (Nat.card_congr h.marking.toEquiv).trans Tits.ExceptionalParabolics.FullRee.group_card
  rw [hf] at hc
  omega

theorem common_neighbors_orbit
    (x:(sourceGraph F q hq hs).commonNeighbors (basePoint F) (g•basePoint F)) :
    orbit (stabilizer F (g•basePoint F)) x.val=
      (sourceGraph F q hq hs).commonNeighbors (basePoint F) (g•basePoint F) := by
  ext y
  constructor
  · rintro ⟨k,rfl⟩
    have hk0:(k.val:G)•basePoint F=basePoint F:=basePoint_fixed F k.val
    have hkg:(k.val:G)•(g•basePoint F)=g•basePoint F:=k.property
    constructor
    · have hh:=(sourceGraph_adj_smul F q hq hs (k.val:G) (basePoint F) x.val).mpr x.property.1
      rwa [hk0] at hh
    · have hh:=(sourceGraph_adj_smul F q hq hs (k.val:G) (g•basePoint F) x.val).mpr x.property.2
      rwa [hkg] at hh
  · intro hy
    exact h.common_neighbors_transitive F q hq hs x ⟨y,hy⟩

/-- The original stabilizer of a nondegenerate two-path has order20. -/
theorem common_neighbor_stabilizer_card
    (x:(sourceGraph F q hq hs).commonNeighbors (basePoint F) (g•basePoint F)) :
    Nat.card (stabilizer (stabilizer F (g•basePoint F)) x.val)=20 := by
  have hc:=Nat.card_congr
    (orbitProdStabilizerEquivGroup (stabilizer F (g•basePoint F)) x.val)
  rw [Nat.card_prod,h.common_neighbors_orbit F q hq hs x,
    (h.parameters F q hq hs).2,h.second_stabilizer_card F q] at hc
  omega

end CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
