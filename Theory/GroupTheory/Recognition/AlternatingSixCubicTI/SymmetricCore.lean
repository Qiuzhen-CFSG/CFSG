module

public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.FourNormalizer
public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.NativeFour

/-!
# The original symmetric subgroup and its four-core

Transport the native four-subgroup geometry along an injective copy of S4.
The normalizer theorem is applied to the literal image of O2(H), not to an
abstract replacement for the given subgroup. The remaining transports give
the parity argument its four-point family of Klein subgroups.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 2(1), printed p.249.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.Recognition.AlternatingSixCubicTI
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
variable {G:Type*} [Group G] [Finite G]

private theorem klein_of_equiv {A B:Type*} [Group A] [Group B] [IsKleinFour A]
    (e:A≃*B):IsKleinFour B where
  card_four := (Nat.card_congr e.toEquiv).symm.trans IsKleinFour.card_four
  exponent_two := (Monoid.exponent_eq_of_mulEquiv e).symm.trans IsKleinFour.exponent_two

omit [Finite G] in
theorem mapped_core_klein (f:Four→*G) (hf:Function.Injective f) : IsKleinFour (core.map f) := by
  let e:=core.equivMapOfInjective f hf
  exact {
    card_four := (Nat.card_congr e.toEquiv).symm.trans NativeFour.core_klein.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv e).symm.trans NativeFour.core_klein.exponent_two }

omit [Finite G] in
theorem range_le_core_normalizer (f:Four→*G) :f.range≤normalizer (core.map f:Set G) := by
  apply le_normalizer_iff.mpr
  rintro _ ⟨a,rfl⟩ _ ⟨b,hb,rfl⟩
  exact ⟨a*b*a⁻¹,Subgroup.Normal.conj_mem inferInstance b hb a,by simp⟩

omit [Finite G] in
theorem range_inf_core_centralizer (f:Four→*G) (hf:Function.Injective f) :
    f.range⊓centralizer (core.map f:Set G)=core.map f := by
  apply le_antisymm
  · rintro _ ⟨⟨a,rfl⟩,ha⟩
    refine ⟨a,?_,rfl⟩
    rw [←centralizer_core]
    intro b hb
    apply hf
    simpa only [map_mul] using ha (f b) (mem_map_of_mem f hb)
  · rintro _ ⟨a,ha,rfl⟩
    refine ⟨⟨a,rfl⟩,?_⟩
    rintro _ ⟨b,hb,rfl⟩
    have hh := (show a∈centralizer (core:Set Four) from centralizer_core.symm ▸ ha) b hb
    simpa only [map_mul] using congrArg f hh

theorem mapped_core_normalizer (f:Four→*G) (hf:Function.Injective f)
    (hG:Nat.card G=360)
    (hc:∀x:G,orderOf x=3→Nat.card (centralizer ({x}:Set G))=9) :
    normalizer (core.map f:Set G)=f.range := by
  let : IsKleinFour (core.map f):=mapped_core_klein f hf
  apply normalizer_four_eq f.range (core.map f) hG _ (range_le_core_normalizer f)
    (range_inf_core_centralizer f hf) hc
  rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
  simp only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
  decide

omit [Finite G] in
theorem comap_klein (f:Four→*G) (hf:Function.Injective f) (K:Subgroup G)
    [IsKleinFour K] (hK:K≤f.range):IsKleinFour (K.comap f) := by
  let e:(K.comap f)≃*K:=((K.comap f).equivMapOfInjective f hf).trans
    (MulEquiv.subgroupCongr (map_comap_eq_self hK))
  exact klein_of_equiv e.symm

omit [Finite G] in
theorem mapped_core_normalizes_klein (f:Four→*G) (hf:Function.Injective f)
    (K:Subgroup G) [IsKleinFour K] (hK:K≤f.range) :
    core.map f≤normalizer (K:Set G) := by
  let : IsKleinFour (K.comap f):=comap_klein f hf K hK
  have hh:core.map f≤normalizer ((K.comap f).map f:Set G):=
    (map_mono (NativeFour.core_normalizes_klein (K.comap f))).trans (le_normalizer_map f)
  rwa [map_comap_eq_self hK] at hh

omit [Finite G] in
theorem mapped_klein_conjugate (f:Four→*G) (hf:Function.Injective f)
    (K L:Subgroup G) [IsKleinFour K] [IsKleinFour L]
    (hK:K≤f.range) (hL:L≤f.range) (hk:K≠core.map f) (hl:L≠core.map f):
    ∃g∈f.range,K.map (MulAut.conj g).toMonoidHom=L := by
  let : IsKleinFour (K.comap f):=comap_klein f hf K hK
  let : IsKleinFour (L.comap f):=comap_klein f hf L hL
  have hkc:K.comap f≠core := by
    intro he
    apply hk
    rw [←map_comap_eq_self hK,he]
  have hlc:L.comap f≠core := by
    intro he
    apply hl
    rw [←map_comap_eq_self hL,he]
  obtain ⟨a,ha⟩:=NativeFour.klein_conjugate_of_ne_core (K.comap f) (L.comap f) hkc hlc
  refine ⟨f a,⟨a,rfl⟩,?_⟩
  have hh:=congrArg (fun J:Subgroup Four=>J.map f) ha
  rw [map_comap_eq_self hL] at hh
  calc
    K.map (MulAut.conj (f a)).toMonoidHom =
        ((K.comap f).map f).map (MulAut.conj (f a)).toMonoidHom := by rw [map_comap_eq_self hK]
    _ = ((K.comap f).map (MulAut.conj a).toMonoidHom).map f := by
      rw [map_map,map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
    _ = L := hh

omit [Finite G] in
theorem mapped_klein_count (f:Four→*G) (hf:Function.Injective f):
    Nat.card {K:Subgroup G // IsKleinFour K ∧ K≤f.range}=4 := by
  classical
  let F:{K:Subgroup Four // IsKleinFour K}→{K:Subgroup G // IsKleinFour K ∧ K≤f.range}:=fun K=>
    ⟨K.val.map f,by
      let : IsKleinFour K.val:=K.property
      exact ⟨klein_of_equiv (K.val.equivMapOfInjective f hf),map_le_range _ _⟩⟩
  have hF:Function.Bijective F := by
    constructor
    · intro K L he
      apply Subtype.ext
      exact map_injective hf (congrArg Subtype.val he)
    · rintro ⟨K,hk,hK⟩
      let : IsKleinFour K:=hk
      refine ⟨⟨K.comap f,comap_klein f hf K hK⟩,?_⟩
      exact Subtype.ext (map_comap_eq_self hK)
  rw [←Nat.card_congr (Equiv.ofBijective F hF),NativeFour.klein_count]

/-- Literal two-core in the original symmetric subgroup. -/
def symmetricCore (H:Subgroup G):Subgroup G := (pCore 2 H).map H.subtype

omit [Finite G] in
theorem symmetricCore_eq (H:Subgroup G) (e:H≃*Four) :
    symmetricCore H=core.map (H.subtype.comp e.symm.toMonoidHom) := by
  change (pCore 2 H).map H.subtype=_
  rw [←map_map,core_eq,pCore_map_iso]

theorem symmetricCore_normalizer (H:Subgroup G) (e:H≃*Four) (hi:H.index=15)
    (hc:∀x:G,orderOf x=3→Nat.card (centralizer ({x}:Set G))=9) :
    normalizer (symmetricCore H:Set G)=H := by
  rw [symmetricCore_eq H e]
  have hh:=mapped_core_normalizer (H.subtype.comp e.symm.toMonoidHom)
    (H.subtype_injective.comp e.symm.injective) (card_eq_360_of_s4_index15 H e hi) hc
  refine hh.trans ?_
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact (e.symm a).property
  · intro hx
    exact ⟨e ⟨x,hx⟩,by simp⟩
end Theory.GroupTheory.Recognition.AlternatingSixCubicTI
