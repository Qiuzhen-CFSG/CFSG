module

public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.SymmetricCore
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Weak closure of the original symmetric four-core

A four-core acts on its fifteen conjugates and has an odd number of fixed
points. If a distinct conjugate returns to the symmetric subgroup, the
native four-subgroup geometry identifies its fixed points with all four
Klein subgroups there, a contradiction. The final theorem discharges the
cubic-centralizer input from the original TI Sylow and faithful C4 quotient.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 2(1), printed p.249.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.AlternatingSixCubicTI
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
variable {G:Type*} [Group G] [Finite G]

noncomputable abbrev subgroupConjugation : MulAction G (Subgroup G) :=
  MulAction.compHom (Subgroup G) MulAut.conj
attribute [local instance] subgroupConjugation

omit [Finite G] in
private theorem orbit_klein (E:Subgroup G) [IsKleinFour E] (K:MulAction.orbit G E):IsKleinFour K.val := by
  obtain ⟨g,hg⟩:=K.property
  change E.map (MulAut.conj g).toMonoidHom=K.val at hg
  let e:E≃*K.val:=((MulAut.conj g).subgroupMap E).trans (MulEquiv.subgroupCongr hg)
  exact {
    card_four := (Nat.card_congr e.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv e).symm.trans IsKleinFour.exponent_two }

omit [Finite G] in
private theorem orbit_fixed_iff (E:Subgroup G) (K:MulAction.orbit G E):
    K∈MulAction.fixedPoints E (MulAction.orbit G E) ↔ E≤normalizer (K.val:Set G) := by
  constructor
  · intro hh g hg
    rw [mem_normalizer_iff_map_conj_eq]
    exact congrArg Subtype.val (hh ⟨g,hg⟩)
  · intro hh g
    apply Subtype.ext
    exact mem_normalizer_iff_map_conj_eq.mp (hh g.property)

omit [Finite G] in
private theorem orbit_card (E:Subgroup G) (hN:(normalizer (E:Set G)).index=15):
    Nat.card (MulAction.orbit G E)=15 := by
  have he:MulAction.stabilizer G E=normalizer (E:Set G) := by
    ext g
    exact mem_normalizer_iff_map_conj_eq.symm
  change (MulAction.orbit G E).ncard=15
  rw [←MulAction.index_stabilizer,he,hN]

theorem mapped_core_weakly_closed (f:Four→*G) (hf:Function.Injective f)
    (hindex:f.range.index=15)
    (hc:∀x:G,orderOf x=3→Nat.card (centralizer ({x}:Set G))=9)
    (g:G) (hg:(core.map f).map (MulAut.conj g).toMonoidHom≤f.range):
    (core.map f).map (MulAut.conj g).toMonoidHom=core.map f := by
  classical
  let E:=core.map f
  let H:=f.range
  let : IsKleinFour E:=mapped_core_klein f hf
  have hG:Nat.card G=360 := card_eq_360_of_s4_index15 H (MonoidHom.ofInjective hf).symm hindex
  have hN:normalizer (E:Set G)=H:=mapped_core_normalizer f hf hG hc
  have hcard:Nat.card (MulAction.orbit G E)=15 := orbit_card E (by rw [hN]; exact hindex)
  have hfix (K:MulAction.orbit G E):
      K∈MulAction.fixedPoints E (MulAction.orbit G E) ↔ K.val≤H := by
    rw [orbit_fixed_iff]
    constructor
    · intro hEK
      obtain ⟨a,ha⟩:=K.property
      change E.map (MulAut.conj a).toMonoidHom=K.val at ha
      let f':Four→*G:=(MulAut.conj a).toMonoidHom.comp f
      have hf':Function.Injective f':=(MulAut.conj a).injective.comp hf
      have hk:core.map f'=K.val := by rw [←map_map]; exact ha
      have hNK:normalizer (K.val:Set G)=f'.range := by
        rw [←hk]
        exact mapped_core_normalizer f' hf' hG hc
      have he: E≤f'.range := hNK ▸ hEK
      have hh:=mapped_core_normalizes_klein f' hf' E he
      rwa [hk,hN] at hh
    · intro hKH
      let : IsKleinFour K.val:=orbit_klein E K
      exact mapped_core_normalizes_klein f hf K.val hKH
  by_contra hne
  let K:MulAction.orbit G E:=⟨E.map (MulAut.conj g).toMonoidHom,⟨g,rfl⟩⟩
  let : IsKleinFour K.val:=orbit_klein E K
  have hall (L:Subgroup G) [IsKleinFour L] (hL:L≤H):L∈MulAction.orbit G E := by
    by_cases he:L=E
    · subst L
      exact MulAction.mem_orbit_self E
    obtain ⟨a,_,ha⟩:=mapped_klein_conjugate f hf K.val L hg hL hne he
    refine ⟨a*g,?_⟩
    calc
      (a*g) • E = a • (g • E) := mul_smul a g E
      _ = a • K.val := rfl
      _ = L := ha
  let e:{L:Subgroup G // IsKleinFour L ∧ L≤H} ≃
      MulAction.fixedPoints E (MulAction.orbit G E) := {
    toFun := fun L=>by
      let : IsKleinFour L.val:=L.property.1
      exact ⟨⟨L.val,hall L.val L.property.2⟩,(hfix _).mpr L.property.2⟩
    invFun := fun L=>⟨L.val.val,orbit_klein E L.val,(hfix L.val).mp L.property⟩
    left_inv := fun _=>rfl
    right_inv := fun _=>rfl }
  have hfour:Nat.card (MulAction.fixedPoints E (MulAction.orbit G E))=4 :=
    (Nat.card_congr e).symm.trans (mapped_klein_count f hf)
  let : Fact (Nat.Prime 2):=⟨by decide⟩
  have hp:IsPGroup 2 E:=IsPGroup.of_card (n:=2) IsKleinFour.card_four
  have hm:=hp.card_modEq_card_fixedPoints (MulAction.orbit G E)
  rw [hcard,hfour] at hm
  norm_num [Nat.ModEq] at hm

theorem symmetricCore_weakly_closed (H:Subgroup G) (e:H≃*Four) (hi:H.index=15)
    (hc:∀x:G,orderOf x=3→Nat.card (centralizer ({x}:Set G))=9)
    (g:G) (hg:(symmetricCore H).map (MulAut.conj g).toMonoidHom≤H):
    (symmetricCore H).map (MulAut.conj g).toMonoidHom=symmetricCore H := by
  let f:=H.subtype.comp e.symm.toMonoidHom
  have hf:Function.Injective f:=H.subtype_injective.comp e.symm.injective
  have hr:f.range=H := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact (e.symm a).property
    · intro hx
      exact ⟨e ⟨x,hx⟩,by simp [f]⟩
  rw [symmetricCore_eq H e] at hg ⊢
  exact mapped_core_weakly_closed f hf (hr ▸ hi) hc g (hr ▸ hg)

theorem symmetricCore_source (H:Subgroup G) (e:H≃*Four) (hi:H.index=15)
    (P:Sylow 3 G) [IsElementaryAbelian 3 P] (hP:Nat.card (P:Subgroup G)=9)
    (hTI:∀g:G,(P:Subgroup G)⊓(P:Subgroup G).map (MulAut.conj g).toMonoidHom=⊥ ∨
      (P:Subgroup G).map (MulAut.conj g).toMonoidHom=P)
    (hC:centralizer (P:Set G)≤P)
    (eN:(normalizer ((P:Subgroup G):Set G)⧸(P:Subgroup G).subgroupOf
      (normalizer ((P:Subgroup G):Set G)))≃*Multiplicative (ZMod 4)):
    normalizer (symmetricCore H:Set G)=H ∧
      ∀g:G,(symmetricCore H).map (MulAut.conj g).toMonoidHom≤H→
        (symmetricCore H).map (MulAut.conj g).toMonoidHom=symmetricCore H := by
  have hc:=cubic_centralizer_card P hP hTI hC eN
  exact ⟨symmetricCore_normalizer H e hi hc,symmetricCore_weakly_closed H e hi hc⟩
end Theory.GroupTheory.Recognition.AlternatingSixCubicTI
