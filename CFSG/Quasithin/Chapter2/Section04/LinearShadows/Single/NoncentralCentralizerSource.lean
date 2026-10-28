module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideSuzukiSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideCardSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CyclicSource
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.MaximalSylowCentralizer
public import Theory.GroupTheory.ComplementCentralizerCard
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldSylowOrbitSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldFixedCardSource
/-!
# The original nontrivial-center field-involution centralizer

An outside involution swaps the two central factors of R. Their fixed diagonal
and the elementary-pair cardinality identity imply |C_R(i)|²=|R|, equal to the
field-involution count. The cyclic field complement has a unique involution,
fixed by the ambient complement. Comparing centralizer orders therefore proves
that C_T(s) is Sylow in C_G(s).

The involution-closure input is exactly the independently proved source
2.4.21(2), retained for the nontrivial-center terminal assembly. No block model,
fixed-cardinality or fixed-plane normalizer premise remains.
Source: Aschbacher–Smith, 2.4.14 and 2.4.23(4), printed pp.533 and 537.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_noncenterless_outside_fixed_card_square
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hZ : center (d.block.map d.H.subtype) ≠ ⊥)
    (a : G) (haT : a ∈ T) (haS : a ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (ha2 : a^2=1) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    Nat.card (R ⊓ centralizer ({a}:Set G) : Subgroup G)^2=Nat.card R := by
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let U := sourceModule L
  let V := U.map (MulAut.conj a⁻¹).toMonoidHom
  let Z := R ⊓ centralizer (R:Set G)
  let I := R ⊓ centralizer ({a}:Set G)
  let J := Z ⊓ centralizer ({a}:Set G)
  obtain ⟨hc,htrace⟩ := source_noncenterless_outside_center_fixed_data d hG T hST hsingle hL hM hTM hu hZ a haT haS ha2
  have hcount : Nat.card I*Nat.card Z=Nat.card U*Nat.card J :=
    source_outside_fixed_card_mul_of_coboundaries d hG T hST hsingle hL hM hTM hu a haT haS ha2 htrace
  obtain ⟨hd,hgen⟩ := source_distinguished_center_pair d hG T hST hsingle hL hM hTM hu hZ a haT haS
  have hcZ : Nat.card J^2=Nat.card Z := by
    let A := distinguishedZ d
    let B := A.map (MulAut.conj a⁻¹).toMonoidHom
    have hAZ : A≤Z := le_sup_left.trans hgen.le
    have hBZ : B≤Z := le_sup_right.trans hgen.le
    have hn : B≤normalizer (A:Set G) :=
      (hBZ.trans inf_le_right).trans ((centralizer_le (hAZ.trans inf_le_left)).trans (Subgroup.centralizer_le_normalizer _))
    change A⊔B=Z at hgen
    rw [←hgen,card_sup_eq_mul_of_normalizes_of_disjoint A B hn hd,
      card_map_of_injective (MulAut.conj a⁻¹).injective,
      (source_distinguished_elementary d hG T hST hsingle hL hM hTM hu).2.1]
    change Nat.card J=2^n at hc
    rw [hc,pow_two]
  have hpair : U⊓V=Z := source_absorbed_center_pair d hG T hST hsingle hL hM hTM hu a haT haS
  have hgenR : U⊔V=R := (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hu).2.2.2 a haT haS |>.1.symm
  have hRU : R≤normalizer (U:Set G) :=
    (source_core_absorption d hG T hST hsingle hL hM hTM hu).1.trans
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L)))
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes U V (le_sup_right.trans hgenR.le |>.trans hRU)
  rw [card_map_of_injective (MulAut.conj a⁻¹).injective,hpair,hgenR] at hp
  have hzpos : 0<Nat.card Z := Nat.card_pos
  change Nat.card I^2=Nat.card R
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hzpos 2)
  calc
    Nat.card I^2*Nat.card Z^2=(Nat.card I*Nat.card Z)^2 := (mul_pow _ _ _).symm
    _=(Nat.card U*Nat.card J)^2 := congrArg (fun k:ℕ=>k^2) hcount
    _=Nat.card U^2*Nat.card J^2 := mul_pow _ _ _
    _=(Nat.card Z*Nat.card R)*Nat.card Z := by rw [pow_two,hp,hcZ]
    _=Nat.card R*Nat.card Z^2 := by ring

theorem CyclicTorusSetup.field_involution_central_in_complement
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (c : CyclicTorusSetup d T n)
    (s : G) (hs : s∈(d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (hs2 : orderOf s=2) :
    (T:Subgroup G) ⊓ normalizer (c.hall:Set G) ≤ centralizer ({s}:Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let F := S⊓normalizer (c.hall:Set G)
  let : IsCyclic F := c.field_cyclic
  let ST := S.subgroupOf (T:Subgroup G)
  have hL' := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  let : ST.Normal := normal_of_index_eq_two (d.lemma_2_4_8_1 hG T hST hsingle hL').1
  have hTS : (T:Subgroup G)≤normalizer (S:Set G) := by
    have hsle : S≤(T:Subgroup G) := hST.le
    rw [←map_subgroupOf_eq_of_le hsle]
    have hh := ST.le_normalizer_map (T:Subgroup G).subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  intro a ha
  have hsn : a*s*a⁻¹∈F := ⟨((mem_normalizer_iff.mp (hTS ha.1)) s).mp hs.1,
    (normalizer (c.hall:Set G)).mul_mem ((normalizer (c.hall:Set G)).mul_mem ha.2 hs.2)
      ((normalizer (c.hall:Set G)).inv_mem ha.2)⟩
  have he : (⟨a*s*a⁻¹,hsn⟩:F)=(⟨s,hs⟩:F) := IsCyclic.eq_of_orderOf_eq_two
    ((orderOf_coe _).symm.trans (((MulAut.conj a).orderOf_eq s).trans hs2))
    ((orderOf_coe _).symm.trans hs2)
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he))
end CFSG.Quasithin.Chapter2.LinearShadows.Single

namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
private theorem card_fixed_le_of_inner_orbit (R : Subgroup G) (r s t : G)
    (hr : r∈R) (he : r*s*r⁻¹=t) :
    Nat.card (R ⊓ centralizer ({t}:Set G) : Subgroup G) ≤
      Nat.card (R ⊓ centralizer ({s}:Set G) : Subgroup G) := by
  let e := MulAut.conj r
  have hes : e s=t := he
  let f : (R ⊓ centralizer ({t}:Set G) : Subgroup G) →
      (R ⊓ centralizer ({s}:Set G) : Subgroup G) := fun a=>⟨e.symm a,by
    constructor
    · change r⁻¹*(a:G)*r∈R
      exact R.mul_mem (R.mul_mem (R.inv_mem hr) a.property.1) hr
    · apply mem_centralizer_singleton_iff.mpr
      apply e.injective
      rw [map_mul,map_mul,e.apply_symm_apply,hes]
      exact mem_centralizer_singleton_iff.mp a.property.2⟩
  exact Nat.card_le_card_of_injective f (fun a b he=>Subtype.ext (e.symm.injective (congrArg Subtype.val he)))

theorem source_noncenterless_field_centralizer_sylow
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) ≠ ⊥)
    (hclosed : ∀ r t : T, orderOf r = 2 →
      (r : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) →
      IsConj (r : G) (t : G) →
      (t : G) ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (s : T) (hs : (s:G) ∈ (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (hs2 : orderOf s=2)
    (hsR : (s:G) ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(s:G)}:Set G))
      (centralizer ({(s:G)}:Set G)) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let RT := R.subgroupOf (T:Subgroup G)
  let A := (normalizer (c.hall:Set G)).subgroupOf (T:Subgroup G)
  let := c.normal_in_sylow
  have hRT : R≤(T:Subgroup G) := (sSup_le fun _ h=>h.1).trans hST.le
  have hsord : orderOf (s:G)=2 := (orderOf_coe s).trans hs2
  have hAs : A≤centralizer ({s}:Set T) := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp
      (c.field_involution_central_in_complement d hG T hST hsingle hL s hs hsord ⟨a.property,ha⟩)
  have hcardmap (t:T) : Nat.card (RT ⊓ centralizer ({t}:Set T) : Subgroup T)=
      Nat.card (R ⊓ centralizer ({(t:G)}:Set G) : Subgroup G) := by
    have he : (RT ⊓ centralizer ({t}:Set T)).map (T:Subgroup G).subtype=
        R ⊓ centralizer ({(t:G)}:Set G) := by
      rw [map_inf _ _ _ (T:Subgroup G).subtype_injective,map_subgroupOf_eq_of_le hRT,
        map_subtype_centralizer_singleton]
      ext a
      exact ⟨fun h=>⟨h.1,h.2.2⟩,fun h=>⟨h.1,⟨hRT h.1,h.2⟩⟩⟩
    rw [←he,card_map_of_injective (T:Subgroup G).subtype_injective]
  apply exists_sylow_centralizer_of_maximal_conjugate_card T (s:G) s.property
  intro t ht hst
  have ht2 : orderOf t=2 := (SemiconjBy.orderOf_eq (hst.choose:G) hst.choose_spec).symm.trans hsord
  have htR : t∉R := fun hh=>hsR (hclosed ⟨t,ht⟩ s ((orderOf_coe ⟨t,ht⟩).symm.trans ht2) hh hst.symm)
  have hfixed : Nat.card (R ⊓ centralizer ({t}:Set G) : Subgroup G) ≤
      Nat.card (R ⊓ centralizer ({(s:G)}:Set G) : Subgroup G) := by
    by_cases htS : t∈S
    · obtain ⟨r,hr,he⟩ := source_field_involution_sylow_fusion d hG T hST hsingle hL hM hTM hu c
        s hs hsord hsR t htS ht2 htR
      exact card_fixed_le_of_inner_orbit R r s t hr he
    · have htpow : t^2=1 := by simpa only [ht2] using pow_orderOf_eq_one t
      have hc := source_noncenterless_outside_fixed_card_square d hG T hST hsingle hL
        hM hTM hu hZ t ht htS htpow
      have hsfix := source_field_thompson_centralizer_card_square d hG T hST hsingle hL
        hM hTM hu c s hs hsord
      exact ((Nat.pow_left_inj (by decide : 2≠0)).mp (hc.trans hsfix.symm)).le
  have hh := card_centralizer_le_of_complement_core_card RT A c.split_ambient s ⟨t,ht⟩ hAs (by
    rw [hcardmap,hcardmap]
    exact hfixed)
  rw [←map_subtype_centralizer_singleton (T:Subgroup G) ⟨t,ht⟩,
    ←map_subtype_centralizer_singleton (T:Subgroup G) s,
    card_map_of_injective (T:Subgroup G).subtype_injective,
    card_map_of_injective (T:Subgroup G).subtype_injective]
  exact hh
end CFSG.Quasithin.Chapter2.LinearShadows.Single
