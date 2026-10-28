module

public import CFSG.Quasithin.ChapterG.Section03.SpanningBlockModels
public import Theory.Representation.BinaryLinearPairWreath
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
import Mathlib.LinearAlgebra.Projection

/-!
# Marked whole-actor wreath identification for two G.3 blocks

The original actor permutes the two canonical generated-group orbits, hence
their independent spans. Each full block group fixes the other span, giving
the whole linear base. Transitivity supplies an actual exchange. The resulting
wreath equivalence retains the two original summands and their full action.

Source: Aschbacher--Smith 12.7.16, printed p.844.
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

/-- The whole faithful actor is the literal binary-three wreath group, and
the equivalences retain both original summands and the matrix action. -/
theorem spanning_two_block_wreath
    (Q : Subgroup (BinaryLinear.GL V)) (x : V)
    (hf : FullAction Q (MulAction.orbit Q x))
    (hd : Decomposition Q (MulAction.orbit Q x))
    (hspan : Submodule.span (ZMod 2) (MulAction.orbit Q x) = ⊤)
    (htwo : Nat.card (OrbitBlock Q (MulAction.orbit Q x)) = 2)
    (hthree : ∀i : OrbitBlock Q (MulAction.orbit Q x),
      Module.finrank (ZMod 2) (blockSpace Q (MulAction.orbit Q x) i) = 3) :
    ∃ i j : OrbitBlock Q (MulAction.orbit Q x), i ≠ j ∧
      ∃ eV : V ≃ₗ[ZMod 2] (OuterCyclic.Space 3 × OuterCyclic.Space 3),
        (∀v,(eV v).2 = 0 ↔ v ∈ blockSpace Q (MulAction.orbit Q x) i) ∧
        (∀v,(eV v).1 = 0 ↔ v ∈ blockSpace Q (MulAction.orbit Q x) j) ∧
        ∃e : Q ≃* RegularWreathProduct
          (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (Multiplicative (ZMod 2)),
          ∀g : Q, ∀v : V,
            eV (g.val v) = if (e g).right = 1 then
              (((e g).left 1).val.mulVec (eV v).1,
               ((e g).left (Multiplicative.ofAdd 1)).val.mulVec (eV v).2)
            else (((e g).left 1).val.mulVec (eV v).2,
               ((e g).left (Multiplicative.ofAdd 1)).val.mulVec (eV v).1) := by
  classical
  let Δ := MulAction.orbit Q x
  obtain ⟨i,j,hij,hall⟩ := Nat.card_eq_two_iff.mp htwo
  have hcases (k : OrbitBlock Q Δ) : k=i ∨ k=j := by
    have hk : k∈({i,j} : Set (OrbitBlock Q Δ)) := hall.symm ▸ Set.mem_univ k
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hk
  let U := blockSpace Q Δ i
  let W := blockSpace Q Δ j
  have hc : IsCompl U W := by
    refine ⟨hd.space_independent.pairwiseDisjoint hij,?_⟩
    apply codisjoint_iff.mpr
    apply top_unique
    rw [←hspan,←hd.space_span]
    apply iSup_le
    intro k
    rcases hcases k with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  have hUne : U ≠ W := by
    intro he
    have hb : U=⊥ := disjoint_self.mp (he.symm ▸ hc.disjoint)
    have hn := hthree i
    change Module.finrank (ZMod 2) U = 3 at hn
    have hr := congrArg (fun P : Submodule (ZMod 2) V => Module.finrank (ZMod 2) P) hb
    simp only [finrank_bot] at hr
    omega
  let e0 : U ≃ₗ[ZMod 2] OuterCyclic.Space 3 := LinearEquiv.ofFinrankEq _ _ (by
    simpa only [OuterCyclic.Space,Module.finrank_pi,Fintype.card_fin] using hthree i)
  let e1 : W ≃ₗ[ZMod 2] OuterCyclic.Space 3 := LinearEquiv.ofFinrankEq _ _ (by
    simpa only [OuterCyclic.Space,Module.finrank_pi,Fintype.card_fin] using hthree j)
  let ev := (U.prodEquivOfIsCompl W hc).symm.trans (e0.prodCongr e1)
  have hev0 (v : V) : (ev v).2=0 ↔ v∈U := by
    change e1 (((U.prodEquivOfIsCompl W hc).symm v).2)=0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff]
    exact Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero U W hc
  have hev1 (v : V) : (ev v).1=0 ↔ v∈W := by
    change e0 (((U.prodEquivOfIsCompl W hc).symm v).1)=0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff]
    exact Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero U W hc
  have hevsum (u : U) (w : W) : ev ((u:V)+(w:V)) = (e0 u,e1 w) := by
    exact congrArg (e0.prodCongr e1) ((U.prodEquivOfIsCompl W hc).symm_apply_apply (u,w))
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
  let Q' := Q.map E.toMonoidHom
  let qE : Q ≃* Q' := Q.equivMapOfInjective E.toMonoidHom E.injective
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
    refine ⟨s.val*t.val,Q.mul_mem (generated_le Q i.val s.property)
      (generated_le Q j.val t.property),?_⟩
    apply LinearEquiv.ext
    rintro ⟨v,w⟩
    change ev (s.val (t.val ((e0.symm v : V)+(e1.symm w : V)))) = (a v,b w)
    rw [map_add,htU,htW,map_add,hsU,hsW,hevsum]
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
    refine ⟨qE gQ,u,?_⟩
    have he : ev.symm (u,0) = (v : V) := by
      change (e0.symm u : V)+(e1.symm 0 : V) = _
      simp [v]
    change (ev (g (ev.symm (u,0)))).2 ≠ 0
    rw [he]
    intro hz
    have hp0 : ev (g v)=0 := Prod.ext ((hev1 _).mpr hgv) hz
    exact hv (g.injective ((ev.map_eq_zero_iff.mp hp0).trans g.map_zero.symm))
  obtain ⟨F,hF⟩ := BinaryLinear.PairWreath.paired_full_linear_actor Q' hp hb hmove
  let c := RegularWreathProduct.congr (OuterCyclic.slEquivLinear 3).symm
    (MulEquiv.refl (Multiplicative (ZMod 2)))
  let e := qE.trans (F.trans c)
  refine ⟨i,j,hij,ev,hev0,hev1,e,?_⟩
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
