module
public import Theory.GroupTheory.DihedralCyclicDerived
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.AutomizerIndexSource
public import Theory.SpecificGroups.AlternatingSix.M10.SylowSemidihedral
public import GorensteinWalter.PGL2DihedralSylow
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingMarksSource
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSylowCenter
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSourceClassification
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NormalAutomizerSource
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# The distinguished mark in the order-two core branch

At core order two, the original quotient order gives |H:K|≤4, so [S,S]≤K.
The quotient map is faithful on this derived subgroup because K is centerless
and the kernel is the literal component centralizer. Dihedral and semidihedral
quotient Sylows have cyclic derived subgroups. The source Sylow is nonabelian,
so its cyclic derived subgroup has a unique involution. Every original
crossing fixes that involution; source 2.5.13 identifies it with z.

The PGL, M₁₀ and inner-model consumers discharge the order and cyclicity
inputs using the actual H/O₂(H) marking. No crossing or characteristic-line
witness is assumed in those consumers.
Source: Aschbacher--Smith 2.5.21, printed p.565, first paragraph after |SC|=2.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem MathieuSourceSetup.central_mark_mem_component_of_cyclic_derived
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (hgen : H=K⊔(S:Subgroup H).map H.subtype)
    (hb : ¬IsBenderModel K)
    (hD : IsCyclic (⁅(S:Subgroup H).map H.subtype,(S:Subgroup H).map H.subtype⁆ : Subgroup G))
    (hne : ⁅(S:Subgroup H).map H.subtype,(S:Subgroup H).map H.subtype⁆ ≠ ⊥)
    (hDK : ⁅(S:Subgroup H).map H.subtype,(S:Subgroup H).map H.subtype⁆ ≤ K) : z∈K := by
  let Y := (S:Subgroup H).map H.subtype
  let D : Subgroup G := ⁅Y,Y⁆
  let := hD
  have hDY : D≤Y := commutator_le_self Y
  have hDp : IsPGroup 2 D := (S.isPGroup'.map H.subtype).to_le hDY
  obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hd : 2∣Nat.card D := (hDp.dvd_orderOf ha).trans (orderOf_dvd_natCard a)
  obtain ⟨v,hv⟩ := exists_prime_orderOf_dvd_card' (G:=D) 2 hd
  have hvo : orderOf (v:G)=2 := (orderOf_coe v).trans hv
  have hnorm : normalizer (Y:Set G) ≤ normalizer (D:Set G) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    change D.map (MulAut.conj x).toMonoidHom=D
    change (⁅Y,Y⁆:Subgroup G).map (MulAut.conj x).toMonoidHom=⁅Y,Y⁆
    rw [map_commutator]
    have hh : Y.map (MulAut.conj x).toMonoidHom=Y := mem_normalizer_iff_map_conj_eq.mp hx
    rw [hh]
  have hfix (x:G) (hx:x∈normalizer (Y:Set G)) : x⁻¹*(v:G)*x=v := by
    let a := D.normalizerMonoidHom ⟨x⁻¹,hnorm ((normalizer (Y:Set G)).inv_mem hx)⟩
    have he : a v=v := IsCyclic.eq_of_orderOf_eq_two ((a.orderOf_eq v).trans hv) hv
    have hh := congrArg Subtype.val he
    change x⁻¹*(v:G)*(x⁻¹)⁻¹=v at hh
    simpa only [inv_inv] using hh
  have hvZ : (v:G)∈centerIn Y := by
    refine ⟨hDY v.property,?_⟩
    intro y hy
    have hh := hfix y (Y.le_normalizer hy)
    have hh' := congrArg (fun a:G=>y*a) hh
    simpa only [←mul_assoc,mul_inv_cancel,one_mul] using hh'.symm
  obtain ⟨t,k,ht,_,htC,hcore,_,_,_,hfour,_⟩ :=
    MathieuSourceSetup.source_central_marks c hG hempty hgen hb
  have htZ : t∈centerIn Y := (show t∈centerIn Y⊓twoCore H from hcore.symm ▸ mem_zpowers t).1
  obtain ⟨x,hxT,hxS,hxN,_⟩ := exists_outside_normalizer_square_mem Y
    (c.T:Subgroup G) c.T.isPGroup' c.sylow_lt
  have hvz := MathieuSourceSetup.source_fixed_projection c hgen t ht htC htZ hfour
    x hxT hxN hxS v hvo hvZ (hfix x hxN)
  exact hvz ▸ hDK v.property
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement ClassificationModels

theorem SourceSylowTwoShape.card_ge_eight {P : Type*} [Group P]
    (h : SourceSylowTwoShape P) : 8≤Nat.card P := by
  rcases h with h|h
  · obtain ⟨m,hm,⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
    have hp : 2^2≤2^m := Nat.pow_le_pow_right (by decide) hm
    omega
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv,Semidihedral.standardModel_card]
    decide

theorem SourceSylowTwoShape.not_commutative {P : Type*} [Group P]
    (h : SourceSylowTwoShape P) : ¬IsMulCommutative P := by
  intro hc
  have hcenter := h.center_card
  rw [center_eq_top_iff.mpr hc,card_top] at hcenter
  have := h.card_ge_eight
  omega

variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem MathieuSourceSetup.source_sylow_derived_ne_bot
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (hgen : H=K⊔(S:Subgroup H).map H.subtype)
    (hb : ¬IsBenderModel K) :
    ⁅(S:Subgroup H).map H.subtype,(S:Subgroup H).map H.subtype⁆ ≠ ⊥ := by
  let Y := (S:Subgroup H).map H.subtype
  have hm := MathieuSourceSetup.small_remaining_component c hG hempty hgen hb
  have hshape := (MathieuSourceSetup.small_model_outer_and_sylow c hm).2
  intro he
  have hc : IsMulCommutative Y := (commutator_self_eq_bot_iff).mp he
  let := hc
  apply hshape.not_commutative
  refine ⟨⟨fun a b=>?_⟩⟩
  exact IsMulCommutative.is_comm.comm a b
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G}
  {S : Sylow 2 H} {z : G}

private theorem commutative_of_card_le_four {P : Type*} [Group P] [Finite P]
    (hcard : Nat.card P≤4) : IsMulCommutative P := by
  have hp : 0<Nat.card P := Nat.card_pos
  interval_cases hc : Nat.card P
  · let : Subsingleton P := Finite.card_le_one_iff_subsingleton.mp (by omega)
    infer_instance
  · let : IsCyclic P := isCyclic_of_prime_card hc
    infer_instance
  · let : IsCyclic P := isCyclic_of_prime_card hc
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p:=2) hc

theorem MathieuSourceSetup.source_sylow_derived_le_component_of_small_core_quotient
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hcore : Nat.card (twoCore H)=2)
    (hquot : Nat.card (H⧸pCore 2 H)≤2*Nat.card K) :
    ⁅(S:Subgroup H).map H.subtype,(S:Subgroup H).map H.subtype⁆ ≤ K := by
  let D := K.subgroupOf H
  have hc : Nat.card (pCore 2 H)=2 := by
    rw [←card_map_of_injective H.subtype_injective]
    exact hcore
  have hh := card_eq_card_quotient_mul_card_subgroup (pCore 2 H)
  rw [hc] at hh
  have hd := D.card_mul_index
  have hdK : Nat.card D=Nat.card K := Nat.card_congr (subgroupOfEquivOfLe c.component_le).toEquiv
  rw [hdK] at hd
  have hpos : 0<Nat.card K := Nat.card_pos
  have hi : Nat.card (H⧸D)≤4 := by
    change D.index≤4
    nlinarith
  let : IsMulCommutative (H⧸D) := commutative_of_card_le_four hi
  have hle : _root_.commutator H≤D := Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  rw [←map_commutator]
  exact (map_mono ((commutator_mono le_top le_top).trans hle)).trans_eq
    (map_subgroupOf_eq_of_le c.component_le)

theorem MathieuSourceSetup.source_sylow_derived_cyclic_of_core_model
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (hgen : H=K⊔(S:Subgroup H).map H.subtype)
    (hcore : Nat.card (twoCore H)=2)
    (hquot : Nat.card (H⧸pCore 2 H)≤2*Nat.card K)
    {B : Type*} [Group B] (f:H→*B) (hk : f.ker=pCore 2 H)
    (hcyc : IsCyclic (_root_.commutator ((S:Subgroup H).map f))) :
    IsCyclic (⁅(S:Subgroup H).map H.subtype,(S:Subgroup H).map H.subtype⁆ : Subgroup G) := by
  let A : Subgroup H := ⁅(S:Subgroup H),(S:Subgroup H)⁆
  have hAK : A≤K.subgroupOf H := by
    have hh := MathieuSourceSetup.source_sylow_derived_le_component_of_small_core_quotient c hcore hquot
    rw [←map_commutator] at hh
    intro a ha
    exact hh (mem_map_of_mem H.subtype ha)
  have hAD : A≤S := commutator_le_self _
  let Q := (S:Subgroup H).map f
  let g : S→*Q := f.subgroupMap (S:Subgroup H)
  have hAeq : A=(_root_.commutator S).map (S:Subgroup H).subtype :=
    (map_subtype_commutator _).symm
  let eA := (_root_.commutator S).equivMapOfInjective (S:Subgroup H).subtype Subtype.val_injective
  have hm : A.map f≤(_root_.commutator Q).map Q.subtype := by
    rw [hAeq,map_map]
    have he : f.comp (S:Subgroup H).subtype=Q.subtype.comp g := rfl
    rw [he,←map_map,map_commutator_eq]
    exact map_mono (commutator_mono le_top le_top)
  let r : A→*_root_.commutator Q :=
    ((f.comp A.subtype).codRestrict Q (fun a=>mem_map_of_mem f (hAD a.property))).codRestrict _ (by
      intro a
      obtain ⟨b,hb,hbe⟩ := hm (mem_map_of_mem f a.property)
      change (⟨f a,mem_map_of_mem f (hAD a.property)⟩:Q)∈_root_.commutator Q
      have he : b=⟨f a,mem_map_of_mem f (hAD a.property)⟩ := Subtype.ext hbe
      rw [←he]
      exact hb)
  have hr : Function.Injective r := by
    apply (MonoidHom.ker_eq_bot_iff r).mp
    apply bot_unique
    intro a ha
    apply mem_bot.mpr
    have haf : f a=1 := congrArg (fun b:_root_.commutator Q=>(b: B)) ha
    have haC : (a:H)∈pCore 2 H := hk ▸ MonoidHom.mem_ker.mpr haf
    have hak : (a:H)∈K.subgroupOf H := hAK a.property
    have hcent : (⟨a,hak⟩:K.subgroupOf H)∈center (K.subgroupOf H) := by
      have hker := MathieuSourceSetup.normal_component_conjugation_ker c hG hempty hgen
      rw [←hker,MulAut.conjNormal_ker_eq_centralizer] at haC
      exact mem_center_iff.mpr (fun b=>Subtype.ext (haC b b.property))
    let e := subgroupOfEquivOfLe c.component_le
    have hh := (centerCongr e ⟨⟨a,hak⟩,hcent⟩).property
    change e ⟨a,hak⟩∈center K at hh
    rw [MathieuSourceSetup.component_center_eq_bot c hG hempty hgen,mem_bot] at hh
    have haH : (a:H)=1 := congrArg (fun q:K.subgroupOf H=>(q:H)) (e.map_eq_one_iff.mp hh)
    exact Subtype.ext haH
  let := hcyc
  let : IsCyclic A := isCyclic_of_injective r hr
  rw [←map_commutator]
  exact isCyclic_of_surjective (A.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
    (A.equivMapOfInjective H.subtype H.subtype_injective).surjective
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G}
  {S : Sylow 2 H} {z : G}

private theorem central_mark_mem_component_of_model
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (hgen : H=K⊔(S:Subgroup H).map H.subtype)
    (hb : ¬IsBenderModel K) (hcore : Nat.card (twoCore H)=2)
    (hquot : Nat.card (H⧸pCore 2 H)≤2*Nat.card K)
    {B : Type*} [Group B] [Finite B]
    (e : (H⧸pCore 2 H)≃*B)
    (hB : ∀P:Sylow 2 B,IsCyclic (_root_.commutator P)) : z∈K := by
  let f : H→*B := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker=pCore 2 H := by
    rw [show f=e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H)) from rfl,
      MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  exact MathieuSourceSetup.central_mark_mem_component_of_cyclic_derived c hG hempty hgen hb
    (MathieuSourceSetup.source_sylow_derived_cyclic_of_core_model c hG hempty hgen hcore hquot f hk
      (hB (S.mapSurjective hf)))
    (MathieuSourceSetup.source_sylow_derived_ne_bot c hG hempty hgen hb)
    (MathieuSourceSetup.source_sylow_derived_le_component_of_small_core_quotient c hcore hquot)

open scoped MatrixGroups
theorem MathieuSourceSetup.pgl_central_mark_mem_component_of_core_card_two
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (hgen : H=K⊔(S:Subgroup H).map H.subtype)
    (hb : ¬IsBenderModel K) (hcore : Nat.card (twoCore H)=2)
    (F : Type*) [Field F] [Finite F]
    (hodd : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (eK : K≃*PSL(2,F)) (eQ : (H⧸pCore 2 H)≃*GorensteinWalter.PGL2 F) : z∈K := by
  have ho : Odd (Nat.card F) := by
    obtain ⟨p,n,_,hp,_,hn⟩ := hodd
    rw [hn]
    exact hp.pow
  have hi := MathieuSourceSetup.linear_pgl_core_index c hG hempty hgen F ho eK eQ
  have hc := MathieuSourceSetup.normal_component_core_index_card c hG hempty hgen
  rw [hi] at hc
  apply central_mark_mem_component_of_model c hG hempty hgen hb hcore (by omega) eQ
  intro P
  obtain ⟨n,_,⟨ep⟩⟩ := GorensteinWalter.pgl2_odd_hasDihedralSylowTwo_model F hodd P
  exact derived_cyclic_of_injective ep.toMonoidHom ep.injective (dihedral_derived_cyclic (2^n))

theorem MathieuSourceSetup.m10_central_mark_mem_component_of_core_card_two
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (hgen : H=K⊔(S:Subgroup H).map H.subtype)
    (hb : ¬IsBenderModel K) (hcore : Nat.card (twoCore H)=2)
    (eK : K≃*AlternatingSix.ShadowLocal.A6)
    (eQ : (H⧸pCore 2 H)≃*AlternatingSix.M10.extension) : z∈K := by
  have hi := MathieuSourceSetup.alternating_six_nonfull_core_index c hG hempty hgen eK (Or.inl ⟨eQ⟩)
  have hc := MathieuSourceSetup.normal_component_core_index_card c hG hempty hgen
  rw [hi] at hc
  apply central_mark_mem_component_of_model c hG hempty hgen hb hcore (by omega) eQ
  intro P
  let ep := AlternatingSix.M10.sylowTwoEquivSemidihedral P
  exact derived_cyclic_of_injective ep.toMonoidHom ep.injective (semidihedral_derived_cyclic 4 (by decide))
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection

namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem MathieuSourceSetup.inner_central_mark_mem_component_of_core_card_two
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (hgen : H=K⊔(S:Subgroup H).map H.subtype)
    (hb : ¬IsBenderModel K) (hcore : Nat.card (twoCore H)=2)
    (eQ : (H⧸pCore 2 H)≃*K) : z∈K := by
  have hcard : Nat.card (H⧸pCore 2 H)≤2*Nat.card K := by
    rw [Nat.card_congr eQ.toEquiv]
    omega
  apply central_mark_mem_component_of_model c hG hempty hgen hb hcore hcard eQ
  intro P
  have hmodel := MathieuSourceSetup.small_remaining_component c hG hempty hgen hb
  rcases hmodel.sylowTwoShape P with h|h
  · obtain ⟨m,_,⟨ep⟩⟩ := h
    exact derived_cyclic_of_injective ep.toMonoidHom ep.injective (dihedral_derived_cyclic (2^m))
  · obtain ⟨ep⟩ := h
    exact derived_cyclic_of_injective ep.toMonoidHom ep.injective (semidihedral_derived_cyclic 4 (by decide))
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection