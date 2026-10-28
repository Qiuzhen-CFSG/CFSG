module

public import Theory.Combinatorics.DoilyRecognition.Frame

/-!
# Cross-block matchings in the doily

The common-neighbor counts force each pair of local matching edges to be
joined by a perfect matching. A cross-block edge has its unique common
neighbor in the third block. These retain the original graph coordinates.
-/

@[expose] public section

namespace Theory.Combinatorics.Doily
variable {Ω:Type*} [Fintype Ω] [DecidableEq Ω]
variable {G:SimpleGraph Ω} [DecidableRel G.Adj]
namespace Frame
variable (F:Frame G) (h:G.IsSRGWith 15 6 1 3)
include h

omit [DecidableEq Ω] in
 theorem cross_card (i j:Fin 3) (hij:i≠j) (p:Bool×Bool) :
    Fintype.card {q:Bool×Bool // G.Adj (F.vertex (.inr (i,p))) (F.vertex (.inr (j,q)))} = 2 := by
  classical
  let C := {q:Bool×Bool // G.Adj (F.vertex (.inr (i,p))) (F.vertex (.inr (j,q)))}
  let N := G.commonNeighbors (F.vertex (.inl j)) (F.vertex (.inr (i,p)))
  let f : Option C → N := fun q => match q with
    | none => ⟨F.vertex (.inl i),(F.base_adj j i).mpr hij.symm,
        (F.mixed_adj i i p).mpr rfl |>.symm⟩
    | some q => ⟨F.vertex (.inr (j,q.val)),(F.mixed_adj j j q.val).mpr rfl,q.property⟩
  have hf:Function.Injective f:=by
    intro x y hxy
    have hv:=congrArg Subtype.val hxy
    cases x with
    | none => cases y with
      | none => rfl
      | some y => exact (Sum.inl_ne_inr (F.vertex.injective hv)).elim
    | some x => cases y with
      | none => exact (Sum.inr_ne_inl (F.vertex.injective hv)).elim
      | some y =>
        have hh:x=y:=Subtype.ext (congrArg Prod.snd (Sum.inr.inj (F.vertex.injective hv)))
        exact congrArg some hh
  have hs:Function.Surjective f:=by
    intro x
    obtain ⟨v,hv⟩:=F.vertex.surjective x.val
    cases v with
    | inl k =>
      have hk:i=k:=(F.mixed_adj k i p).mp (hv.symm ▸ x.property.2.symm) |>.symm
      subst k
      exact ⟨none,Subtype.ext hv⟩
    | inr v =>
      rcases v with ⟨k,q⟩
      have hk:j=k:=(F.mixed_adj j k q).mp (hv.symm ▸ x.property.1)
      subst k
      exact ⟨some ⟨q,hv.symm ▸ x.property.2⟩,Subtype.ext hv⟩
  have hc:=Fintype.card_congr (Equiv.ofBijective f ⟨hf,hs⟩)
  have hn:Fintype.card N=3:=h.of_not_adj
    (fun he => Sum.inl_ne_inr (F.vertex.injective he))
    (fun ha => hij ((F.mixed_adj j i p).mp ha).symm)
  rw [hn,Fintype.card_option] at hc
  dsimp only [C] at hc
  omega

omit [DecidableEq Ω] in
 theorem cross_unique (i j:Fin 3) (hij:i≠j) (p:Bool×Bool) (a:Bool) :
    ∃!b:Bool,G.Adj (F.vertex (.inr (i,p))) (F.vertex (.inr (j,(a,b)))) := by
  classical
  let C := {q:Bool×Bool // G.Adj (F.vertex (.inr (i,p))) (F.vertex (.inr (j,q)))}
  let f:C→Bool:=fun q=>q.val.1
  have hf:Function.Injective f:=by
    rintro ⟨⟨a,b⟩,hb⟩ ⟨⟨c,d⟩,hd⟩ he
    change a=c at he
    subst c
    have hbd : b=d := by
      by_contra hbd
      have hpair:= (F.fiber_adj j (a,b) (a,d)).mpr ⟨rfl,hbd⟩
      have heq:=common_eq h hpair hb.symm hd.symm
        ((F.mixed_adj j j (a,b)).mpr rfl).symm
        ((F.mixed_adj j j (a,d)).mpr rfl).symm
      exact Sum.inr_ne_inl (F.vertex.injective heq)
    exact Subtype.ext (Prod.ext rfl hbd)
  have hs:Function.Surjective f:=
    ((Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hf,by rw [F.cross_card h i j hij p];rfl⟩).2
  obtain ⟨⟨⟨c,b⟩,hb⟩,he⟩:=hs a
  change c=a at he
  subst c
  refine ⟨b,hb,?_⟩
  intro d hd
  exact congrArg (fun q:C=>q.val.2) (hf (a₁:=⟨(a,d),hd⟩) (a₂:=⟨(a,b),hb⟩) rfl)
omit [DecidableEq Ω] in
 theorem cross_bits (i j:Fin 3) (hij:i≠j) :
    ∃f:Bool→Bool→Bool, ∀a b c d,
      G.Adj (F.vertex (.inr (i,(a,b)))) (F.vertex (.inr (j,(c,d)))) ↔
        d = Bool.xor b (f a c) := by
  classical
  have hb (a c:Bool):∃e:Bool,∀b d,
      G.Adj (F.vertex (.inr (i,(a,b)))) (F.vertex (.inr (j,(c,d)))) ↔
        d = Bool.xor b e := by
    obtain ⟨e,he,hu⟩:=F.cross_unique h i j hij (a,false) c
    refine ⟨e,?_⟩
    intro b d
    cases b with
    | false =>
      simpa only [Bool.false_xor] using
        (show G.Adj (F.vertex (.inr (i,(a,false)))) (F.vertex (.inr (j,(c,d)))) ↔ d=e
          from ⟨fun hd=>hu d hd,fun hh=>hh ▸ he⟩)
    | true =>
      obtain ⟨f,hf,_⟩:=F.cross_unique h i j hij (a,true) c
      have hfe:f≠e:=by
        intro hh
        subst f
        obtain ⟨z,hz,hu'⟩:=F.cross_unique h j i hij.symm (c,e) a
        have htf:true=false:=(hu' true hf.symm).trans (hu' false he.symm).symm
        exact Bool.noConfusion htf
      have hfn:f=(!e):=by
        cases f <;> cases e
        · exact (hfe rfl).elim
        · rfl
        · rfl
        · exact (hfe rfl).elim
      subst f
      have hun:=F.cross_unique h i j hij (a,true) c
      rcases hun with ⟨w,hw,huw⟩
      have hd:∀d,G.Adj (F.vertex (.inr (i,(a,true)))) (F.vertex (.inr (j,(c,d)))) ↔ d=(!e):=by
        intro d
        exact ⟨fun hh=>(huw d hh).trans (huw (!e) hf).symm,fun hh=>hh ▸ hf⟩
      simpa only [Bool.true_xor] using hd d
  choose f hf using hb
  exact ⟨f,fun a b c d=>hf a c b d⟩

omit [DecidableEq Ω] in
 theorem common_third (i j k:Fin 3) (hij:i≠j) (hik:i≠k) (hjk:j≠k)
    (p q:Bool×Bool) (hpq:G.Adj (F.vertex (.inr (i,p))) (F.vertex (.inr (j,q)))) :
    ∃!r:Bool×Bool, G.Adj (F.vertex (.inr (i,p))) (F.vertex (.inr (k,r))) ∧
      G.Adj (F.vertex (.inr (j,q))) (F.vertex (.inr (k,r))) := by
  classical
  have hc:=h.of_adj _ _ hpq
  obtain ⟨x,hx⟩:=Fintype.card_eq_one_iff.mp hc
  obtain ⟨v,hv⟩:=F.vertex.surjective x.val
  have he:∃r:Bool×Bool,v=Sum.inr (k,r):=by
    cases v with
    | inl l =>
      have hli:l=i:=(F.mixed_adj l i p).mp (hv.symm ▸ x.property.1.symm)
      have hlj:l=j:=(F.mixed_adj l j q).mp (hv.symm ▸ x.property.2.symm)
      exact (hij (hli.symm.trans hlj)).elim
    | inr v =>
      rcases v with ⟨l,r⟩
      have hli:l≠i:=by
        intro hh
        subst l
        have hxr:G.Adj (F.vertex (.inr (i,p))) (F.vertex (.inr (i,r))):=hv.symm ▸ x.property.1
        have heq:=common_eq h hxr hpq (hv.symm ▸ x.property.2).symm
          ((F.mixed_adj i i p).mpr rfl).symm ((F.mixed_adj i i r).mpr rfl).symm
        exact Sum.inr_ne_inl (F.vertex.injective heq)
      have hlj:l≠j:=by
        intro hh
        subst l
        have hyr:G.Adj (F.vertex (.inr (j,q))) (F.vertex (.inr (j,r))):=hv.symm ▸ x.property.2
        have heq:=common_eq h hyr hpq.symm (hv.symm ▸ x.property.1).symm
          ((F.mixed_adj j j q).mpr rfl).symm ((F.mixed_adj j j r).mpr rfl).symm
        exact Sum.inr_ne_inl (F.vertex.injective heq)
      have hl:l=k:=by
        omega
      exact ⟨r,hl ▸ rfl⟩
  obtain ⟨r,rfl⟩:=he
  refine ⟨r,⟨hv.symm ▸ x.property.1,hv.symm ▸ x.property.2⟩,?_⟩
  intro s hs
  have heq:=common_eq h hpq hs.1 hs.2 (hv.symm ▸ x.property.1) (hv.symm ▸ x.property.2)
  exact congrArg Prod.snd (Sum.inr.inj (F.vertex.injective heq))

end Frame
end Theory.Combinatorics.Doily
