module

public import CFSG.Quasithin.ChapterG.Section03.RootSpanAction
public import Theory.Representation.BinaryLinearPairWreath
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
import Mathlib.LinearAlgebra.Projection

/-!
# The marked wreath image on the total root span

Two full three-dimensional blocks give the whole paired linear actor on
their literal total span. The original actor may have a restriction kernel;
this theorem identifies exactly its restriction image and retains the
original summands and coordinate action.

Source: Aschbacher--Smith12.7.18, printed p.845.
-/

public noncomputable section
open Subgroup BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

omit [Finite V] in
private theorem orbit_block_map (Q : Subgroup (BinaryLinear.GL V)) (x : V)
    (g : Q) (i : OrbitBlock Q (MulAction.orbit Q x)) :
    ∃j : OrbitBlock Q (MulAction.orbit Q x),
      (blockSpace Q (MulAction.orbit Q x) i).map g.val.toLinearMap =
        blockSpace Q (MulAction.orbit Q x) j := by
  let Δ := MulAction.orbit Q x
  have hs : ∀g∈Q,∀v∈Δ,g v∈Δ := by
    intro a ha v hv
    obtain ⟨b,rfl⟩ := MulAction.mem_orbit_iff.mp hv
    exact MulAction.mem_orbit_iff.mpr ⟨(⟨a,ha⟩ : Q)*b,rfl⟩
  have hn := generated_normal Q Δ hs
  have hc (a : Q) (k : generated Q Δ) : a.val*k.val*a.val⁻¹ ∈ generated Q Δ :=
    hn.conj_mem (⟨k.val,generated_le Q Δ k.property⟩ : Q) k.property a
  obtain ⟨y,hy,hi⟩ := i.property
  let j : OrbitBlock Q Δ := ⟨MulAction.orbit (generated Q Δ) (g.val y),
    g.val y,hs g.val g.property y hy,rfl⟩
  have he : g.val '' i.val = j.val := by
    rw [hi]
    ext v
    constructor
    · rintro ⟨w,hw,rfl⟩
      obtain ⟨k,rfl⟩ := MulAction.mem_orbit_iff.mp hw
      exact MulAction.mem_orbit_iff.mpr
        ⟨⟨g.val*k.val*g.val⁻¹,hc g k⟩,by simp; rfl⟩
    · intro hv
      obtain ⟨k,rfl⟩ := MulAction.mem_orbit_iff.mp hv
      refine ⟨g.val⁻¹ (k.val (g.val y)),?_,by simp; rfl⟩
      exact MulAction.mem_orbit_iff.mpr ⟨⟨g.val⁻¹*k.val*g.val,hc g⁻¹ k⟩,rfl⟩
  refine ⟨j,?_⟩
  simp only [blockSpace,Submodule.map_span,LinearEquiv.coe_coe,he]

/-- The actual restriction image is the literal binary-three wreath group,
with the original summands and the full action on their total span retained. -/
theorem root_span_two_block_wreath
    (Q : Subgroup (BinaryLinear.GL V)) (x : V)
    (hsource : Hypotheses Q (MulAction.orbit Q x)) (hcore : pCore 2 Q = ⊥)
    (hf : FullAction Q (MulAction.orbit Q x))
    (hd : Decomposition Q (MulAction.orbit Q x))
    (htwo : Nat.card (OrbitBlock Q (MulAction.orbit Q x)) = 2)
    (hthree : ∀i : OrbitBlock Q (MulAction.orbit Q x),
      Module.finrank (ZMod 2) (blockSpace Q (MulAction.orbit Q x) i) = 3) :
    let S := Submodule.span (ZMod 2) (MulAction.orbit Q x)
    ∃hpar : Q ≤ parabolic S,
      let ρ := action Q S hpar
      ∃ i j : OrbitBlock Q (MulAction.orbit Q x), i ≠ j ∧
        ∃ eV : S ≃ₗ[ZMod 2] (OuterCyclic.Space 3 × OuterCyclic.Space 3),
          (∀v : S,(eV v).2 = 0 ↔ (v:V) ∈ blockSpace Q (MulAction.orbit Q x) i) ∧
          (∀v : S,(eV v).1 = 0 ↔ (v:V) ∈ blockSpace Q (MulAction.orbit Q x) j) ∧
          ∃e : ρ.range ≃* RegularWreathProduct
            (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (Multiplicative (ZMod 2)),
            ∀g : ρ.range, ∀v : S,
              eV (g.val v) = if (e g).right = 1 then
                (((e g).left 1).val.mulVec (eV v).1,
                 ((e g).left (Multiplicative.ofAdd 1)).val.mulVec (eV v).2)
              else (((e g).left 1).val.mulVec (eV v).2,
                 ((e g).left (Multiplicative.ofAdd 1)).val.mulVec (eV v).1) := by
  classical
  let Δ := MulAction.orbit Q x
  let S := Submodule.span (ZMod 2) Δ
  obtain ⟨hpar,_,_,_⟩ := root_span_action hsource hcore
  let ρ := action Q S hpar
  obtain ⟨i,j,hij,hall⟩ := Nat.card_eq_two_iff.mp htwo
  have hcases (k : OrbitBlock Q Δ) : k=i ∨ k=j := by
    have hk : k∈({i,j} : Set (OrbitBlock Q Δ)) := hall.symm ▸ Set.mem_univ k
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hk
  let U := blockSpace Q Δ i
  let W := blockSpace Q Δ j
  have hdis : Disjoint U W := hd.space_independent.pairwiseDisjoint hij
  have hsum : U ⊔ W = S := by
    apply le_antisymm
    · exact sup_le ((le_iSup (blockSpace Q Δ) i).trans hd.space_span.le)
        ((le_iSup (blockSpace Q Δ) j).trans hd.space_span.le)
    · change Submodule.span (ZMod 2) (MulAction.orbit Q x) ≤ U ⊔ W
      rw [←hd.space_span]
      apply iSup_le
      intro k
      rcases hcases k with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
  have hUS : U≤S := le_sup_left.trans hsum.le
  have hWS : W≤S := le_sup_right.trans hsum.le
  let add : U × W →ₗ[ZMod 2] S := (U.subtype.coprod W.subtype).codRestrict S
    (fun v => S.add_mem (hUS v.1.property) (hWS v.2.property))
  have hadd : Function.Bijective add := by
    constructor
    · intro p q hpq
      have he : (p.1:V)+(p.2:V)=(q.1:V)+(q.2:V) := congrArg Subtype.val hpq
      have hi : (p.1:V)-(q.1:V)=(q.2:V)-(p.2:V) := sub_eq_sub_iff_add_eq_add.mpr (he.trans (add_comm _ _))
      have hz : (p.1:V)-(q.1:V)=0 := Submodule.disjoint_def.mp hdis _
        (U.sub_mem p.1.property q.1.property) (hi.symm ▸ W.sub_mem q.2.property p.2.property)
      have h1 : p.1=q.1 := Subtype.ext (sub_eq_zero.mp hz)
      have h2 : p.2=q.2 := Subtype.ext (by simpa only [h1,add_left_cancel_iff] using he)
      exact Prod.ext h1 h2
    · intro v
      obtain ⟨u,hu,w,hw,he⟩ := Submodule.mem_sup.mp (show (v:V)∈U⊔W by rw [hsum]; exact v.property)
      exact ⟨(⟨u,hu⟩,⟨w,hw⟩),Subtype.ext he⟩
  let eadd : (U × W) ≃ₗ[ZMod 2] S := LinearEquiv.ofBijective add hadd
  have hUne : U ≠ W := by
    intro he
    have hb : U=⊥ := disjoint_self.mp (he.symm ▸ hdis)
    have hn := hthree i
    change Module.finrank (ZMod 2) U = 3 at hn
    have hr := congrArg (fun P : Submodule (ZMod 2) V => Module.finrank (ZMod 2) P) hb
    simp only [finrank_bot] at hr
    omega
  let e0 : U ≃ₗ[ZMod 2] OuterCyclic.Space 3 := LinearEquiv.ofFinrankEq _ _ (by
    simpa only [OuterCyclic.Space,Module.finrank_pi,Fintype.card_fin] using hthree i)
  let e1 : W ≃ₗ[ZMod 2] OuterCyclic.Space 3 := LinearEquiv.ofFinrankEq _ _ (by
    simpa only [OuterCyclic.Space,Module.finrank_pi,Fintype.card_fin] using hthree j)
  let ev := eadd.symm.trans (e0.prodCongr e1)
  have hev0 (v : S) : (ev v).2=0 ↔ (v:V)∈U := by
    obtain ⟨⟨u,w⟩,rfl⟩ := eadd.surjective v
    change e1 ((eadd.symm (eadd (u,w))).2)=0 ↔ (u:V)+(w:V)∈U
    rw [eadd.symm_apply_apply,LinearEquiv.map_eq_zero_iff]
    constructor
    · intro hw
      have hh : (w:V)=0 := congrArg Subtype.val hw
      rw [hh,add_zero]
      exact u.property
    · intro hv
      have hwU : (w:V)∈U := (U.add_mem_iff_right u.property).mp hv
      exact Subtype.ext (Submodule.disjoint_def.mp hdis _ hwU w.property)
  have hev1 (v : S) : (ev v).1=0 ↔ (v:V)∈W := by
    obtain ⟨⟨u,w⟩,rfl⟩ := eadd.surjective v
    change e0 ((eadd.symm (eadd (u,w))).1)=0 ↔ (u:V)+(w:V)∈W
    rw [eadd.symm_apply_apply,LinearEquiv.map_eq_zero_iff]
    constructor
    · intro hu
      have hh : (u:V)=0 := congrArg Subtype.val hu
      rw [hh,zero_add]
      exact w.property
    · intro hv
      have huW : (u:V)∈W := (W.add_mem_iff_left w.property).mp hv
      exact Subtype.ext (Submodule.disjoint_def.mp hdis _ u.property huW)
  have hevsum (u : U) (w : W) : ev (eadd (u,w)) = (e0 u,e1 w) := by
    exact congrArg (e0.prodCongr e1) (eadd.symm_apply_apply (u,w))
  have hm (g : Q) :
      (U.map g.val.toLinearMap=U ∧ W.map g.val.toLinearMap=W) ∨
      (U.map g.val.toLinearMap=W ∧ W.map g.val.toLinearMap=U) := by
    obtain ⟨k,hk⟩ := orbit_block_map Q x g i
    obtain ⟨l,hl⟩ := orbit_block_map Q x g j
    have hne : U.map g.val.toLinearMap ≠ W.map g.val.toLinearMap :=
      (Submodule.map_injective_of_injective g.val.injective).ne hUne
    rcases hcases k with rfl | rfl <;> rcases hcases l with rfl | rfl
    · exact (hne (hk.trans hl.symm)).elim
    · exact Or.inl ⟨hk,hl⟩
    · exact Or.inr ⟨hk,hl⟩
    · exact (hne (hk.trans hl.symm)).elim
  let E := SmallParabolicLevi.linearGroupCongr ev
  let Q' := ρ.range.map E.toMonoidHom
  let qE : ρ.range ≃* Q' := ρ.range.equivMapOfInjective E.toMonoidHom E.injective
  have hmap {A B : Submodule (ZMod 2) V} {g : Q}
      (hg : A.map g.val.toLinearMap=B) {v : V} (hv : v∈A) : g.val v∈B := by
    rw [←hg]
    exact ⟨v,hv,rfl⟩
  have hp : ∀g : Q',
      ((∀v : OuterCyclic.Space 3,(g.val (v,0)).2=0) ∧
       (∀v : OuterCyclic.Space 3,(g.val (0,v)).1=0)) ∨
      ((∀v : OuterCyclic.Space 3,(g.val (v,0)).1=0) ∧
       (∀v : OuterCyclic.Space 3,(g.val (0,v)).2=0)) := by
    intro g
    obtain ⟨g,rfl⟩ := qE.surjective g
    obtain ⟨g,rfl⟩ := ρ.rangeRestrict_surjective g
    rcases hm g with hh | hh
    · refine Or.inl ⟨?_,?_⟩
      · intro v
        exact (hev0 _).mpr (hmap hh.1 ((hev0 _).mp (by simp)))
      · intro v
        exact (hev1 _).mpr (hmap hh.2 ((hev1 _).mp (by simp)))
    · refine Or.inr ⟨?_,?_⟩
      · intro v
        exact (hev1 _).mpr (hmap hh.1 ((hev0 _).mp (by simp)))
      · intro v
        exact (hev0 _).mpr (hmap hh.2 ((hev1 _).mp (by simp)))
  have hb (a b : OuterCyclic.LinearGroup 3) : a.prodCongr b ∈ Q' := by
    let a0 := (SmallParabolicLevi.linearGroupCongr e0).symm a
    let b0 := (SmallParabolicLevi.linearGroupCongr e1).symm b
    obtain ⟨s,hs⟩ := hf.surjective i a0
    obtain ⟨t,ht⟩ := hf.surjective j b0
    have hsU (u : U) : s.val u = (a0 u : V) :=
      congrArg (fun F : BinaryLinear.GL U => (F u : V)) hs
    have htW (w : W) : t.val w = (b0 w : V) :=
      congrArg (fun F : BinaryLinear.GL W => (F w : V)) ht
    have hsW (w : W) : s.val w = w := hd.cross_fix i j hij s.val s.property w w.property
    have htU (u : U) : t.val u = u := hd.cross_fix j i hij.symm t.val t.property u u.property
    let g : Q := ⟨s.val*t.val,Q.mul_mem (generated_le Q i.val s.property)
      (generated_le Q j.val t.property)⟩
    refine ⟨ρ g,⟨g,rfl⟩,?_⟩
    apply LinearEquiv.ext
    rintro ⟨v,w⟩
    have he (u : U) (w : W) : ρ g (eadd (u,w)) = eadd (a0 u,b0 w) := by
      apply Subtype.ext
      change s.val (t.val ((u:V)+(w:V))) = (a0 u:V)+(b0 w:V)
      rw [map_add,htU,htW,map_add,hsU,hsW]
    change ev (ρ g (eadd (e0.symm v,e1.symm w))) = (a v,b w)
    rw [he,hevsum]
    change (e0 (e0.symm (a (e0 (e0.symm v)))),
      e1 (e1.symm (b (e1 (e1.symm w))))) = _
    simp
  have hmove : ∃g : Q',∃v : OuterCyclic.Space 3,(g.val (v,0)).2 ≠ 0 := by
    obtain ⟨g,hg,hgU⟩ := hd.spaces_conjugate i j
    let gQ : Q := ⟨g,hg⟩
    obtain ⟨u,hu⟩ := exists_ne (0 : OuterCyclic.Space 3)
    let v : U := e0.symm u
    have hv : (v : V) ≠ 0 := by
      intro he
      have he' : v=0 := Subtype.ext he
      exact hu (by simpa [v] using congrArg e0 he')
    have hgv : g v ∈ W := hmap (g := gQ) hgU v.property
    refine ⟨qE (ρ.rangeRestrict gQ),u,?_⟩
    have he : (ev.symm (u,0) : V) = (v : V) := by
      change (e0.symm u : V)+(e1.symm 0 : V) = _
      simp [v]
    change (ev (ρ gQ (ev.symm (u,0)))).2 ≠ 0
    intro hz
    have hgv' : ((ρ gQ (ev.symm (u,0))) : V)∈W := by
      change g ((ev.symm (u,0) : S) : V)∈W
      rwa [he]
    have hp0 : ev (ρ gQ (ev.symm (u,0)))=0 := Prod.ext ((hev1 _).mpr hgv') hz
    have hz' := congrArg Subtype.val (ev.map_eq_zero_iff.mp hp0)
    change g ((ev.symm (u,0) : S) : V)=0 at hz'
    rw [he] at hz'
    exact hv (g.injective (hz'.trans g.map_zero.symm))
  obtain ⟨F,hF⟩ := BinaryLinear.PairWreath.paired_full_linear_actor Q' hp hb hmove
  let c := RegularWreathProduct.congr (OuterCyclic.slEquivLinear 3).symm
    (MulEquiv.refl (Multiplicative (ZMod 2)))
  let e := qE.trans (F.trans c)
  refine ⟨hpar,i,j,hij,ev,hev0,hev1,e,?_⟩
  intro g v
  have hh := hF (qE g) (ev v)
  have hh' : ev (g.val v) = if (F (qE g)).right=1 then
      ((F (qE g)).left 1 (ev v).1,(F (qE g)).left (Multiplicative.ofAdd 1) (ev v).2)
      else ((F (qE g)).left 1 (ev v).2,(F (qE g)).left (Multiplicative.ofAdd 1) (ev v).1) := by
    change ev (g.val (ev.symm (ev v))) = _ at hh
    rw [ev.symm_apply_apply] at hh
    exact hh
  have hm (a : OuterCyclic.LinearGroup 3) (w : OuterCyclic.Space 3) :
      ((OuterCyclic.slEquivLinear 3).symm a).val.mulVec w = a w := by
    rw [←OuterCyclic.slEquivLinear_apply, MulEquiv.apply_symm_apply]
  change ev (g.val v) = if (F (qE g)).right=1 then
    (((OuterCyclic.slEquivLinear 3).symm ((F (qE g)).left 1)).val.mulVec (ev v).1,
      ((OuterCyclic.slEquivLinear 3).symm ((F (qE g)).left (Multiplicative.ofAdd 1))).val.mulVec (ev v).2)
    else (((OuterCyclic.slEquivLinear 3).symm ((F (qE g)).left 1)).val.mulVec (ev v).2,
      ((OuterCyclic.slEquivLinear 3).symm ((F (qE g)).left (Multiplicative.ofAdd 1))).val.mulVec (ev v).1)
  simpa only [hm] using hh'

end CFSG.Quasithin.ChapterG.Section03
