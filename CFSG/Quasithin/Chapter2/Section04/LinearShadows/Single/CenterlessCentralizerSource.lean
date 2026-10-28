module
public import Theory.GroupTheory.MaximalSylowCentralizer
public import Theory.GroupTheory.ComplementCentralizerCard
public import Theory.GroupTheory.NormalizedSupCard
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldSylowOrbitSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterSplitSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldFixedFusionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterFixedCardSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideUnitarySource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterlessFusionSource

/-!
# The original centerless field-involution centralizer

The two fixed root planes give a lower bound for the centralizer in R.
The original outside-involution rows bound every competing centralizer, while
field-coset fusion handles involutions inside S. The torus complement centralizes
the marked field involution. Comparing centralizer orders therefore proves that
its centralizer in the ambient Sylow subgroup is a Sylow subgroup of its full
centralizer. All fusion and fixed-cardinality premises come from the original
single-block hypotheses.

Source: Aschbacher–Smith, 2.4.23(2), printed pp.537–538.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_centerless_field_core_card_lower
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (s : T) (hs : (s:G) ∈ (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (hs2 : orderOf s=2)
    (hsR : (s:G) ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    ∃ m : ℕ, 0<m ∧ n=2*m ∧ 2^(3*m) ≤ Nat.card (R ⊓ centralizer ({(s:G)}:Set G) : Subgroup G) := by
  have hclosed := c.centerless_involution_fusion_closed d hG T hST hsingle hL hM hTM hu hZ
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := R ⊓ centralizer (R:Set G)
  let U := ChapterC.Section05.ConjugateSource.sourceModule L
  let C := centralizer ({(s:G)}:Set G)
  have hsord : orderOf (s:G)=2 := (orderOf_coe s).trans hs2
  have hspow : (s:G)^2=1 := by simpa only [hsord] using pow_orderOf_eq_one (s:G)
  have hsnon : (s:G) ∉ centralizer (Z:Set G) := by
    intro hh
    have hSC : S ⊓ centralizer (Z:Set G)=R := by
      simpa only [distinguishedZ_of_centerless d hZ] using
        source_distinguished_sylow_centralizer_eq d hG T hST hsingle hL hM hTM hu
    exact hsR (hSC.le ⟨hs.1,hh⟩)
  obtain ⟨m,hm,hn,hJ⟩ := source_centerless_center_involution_fixed_card d hG T hST hsingle hL
    hM hTM hu c hZ s s.property hspow hsnon
  obtain ⟨x,hx,hxS,hx2,_,_,hxf,_⟩ := source_centerless_split_involution d hG T hST hsingle hL
    hM hTM hu c hZ hclosed
  have hxs : x ∈ C := mem_centralizer_singleton_iff.mpr (hxf s hs)
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  let A := U ⊓ C
  let B := V ⊓ C
  have hpair : U ⊓ V=Z := source_absorbed_center_pair d hG T hST hsingle hL hM hTM hu x hx.1 hxS
  have hgen : R=U ⊔ V := (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hu).2.2.2 x hx.1 hxS |>.1
  have hA : Nat.card A=2^n := source_centerless_field_plane_card d hG T hST hsingle hL hM hTM hu c hZ s hs hsord
  have hB : Nat.card B=2^n := by
    have hcn := mem_normalizer_iff_map_conj_eq.mp (C.le_normalizer (C.inv_mem hxs))
    change C.map (MulAut.conj x⁻¹).toMonoidHom=C at hcn
    have he : A.map (MulAut.conj x⁻¹).toMonoidHom=B := by
      dsimp only [A,B,V]
      rw [Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective,hcn]
    rw [←he,card_map_of_injective (MulAut.conj x⁻¹).injective]
    exact hA
  have hAB : A ⊓ B=Z ⊓ C := by
    rw [←hpair]
    ext a
    simp only [A,B,mem_inf]
    tauto
  have hRU : R ≤ normalizer (U:Set G) :=
    (source_core_absorption d hG T hST hsingle hL hM hTM hu).1.trans
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L)))
  have hBR : B≤R := inf_le_left.trans (le_sup_right.trans_eq hgen.symm)
  have hBA : B ≤ normalizer (A:Set G) :=
    (le_inf (hBR.trans hRU) (inf_le_right.trans C.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes A B hBA
  rw [hA,hB,hAB,hJ] at hprod
  have hpow : 2^n*2^n=2^m*2^(3*m) := by
    rw [←pow_add,←pow_add,hn]
    congr 1
    omega
  have hcard : Nat.card (A ⊔ B : Subgroup G)=2^(3*m) :=
    Nat.eq_of_mul_eq_mul_left (by positivity) (hprod.symm.trans hpow)
  refine ⟨m,hm,hn,?_⟩
  rw [←hcard]
  exact card_le_of_le (sup_le
    (le_inf (inf_le_left.trans (le_sup_left.trans_eq hgen.symm)) inf_le_right)
    (le_inf hBR inf_le_right))
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

theorem source_centerless_field_centralizer_sylow
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (s : T) (hs : (s:G) ∈ (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (hs2 : orderOf s=2)
    (hsR : (s:G) ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(s:G)}:Set G))
      (centralizer ({(s:G)}:Set G)) := by
  have hclosed := c.centerless_involution_fusion_closed d hG T hST hsingle hL hM hTM hu hZ
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := R ⊓ centralizer (R:Set G)
  let F := S ⊓ normalizer (c.hall:Set G)
  let RT := R.subgroupOf (T:Subgroup G)
  let A := (normalizer (c.hall:Set G)).subgroupOf (T:Subgroup G)
  let := c.normal_in_sylow
  let : IsCyclic F := c.field_cyclic
  have hRT : R≤(T:Subgroup G) := (sSup_le fun _ h=>h.1).trans hST.le
  have hsord : orderOf (s:G)=2 := (orderOf_coe s).trans hs2
  obtain ⟨m,hm,hn,hlow⟩ := source_centerless_field_core_card_lower d hG T hST hsingle hL
    hM hTM hu c hZ s hs hs2 hsR
  obtain ⟨x,_,_,_,_,_,hxf,hgen⟩ := source_centerless_split_involution d hG T hST hsingle hL
    hM hTM hu c hZ hclosed
  have hAs : A≤centralizer ({s}:Set T) := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    have hA : (T:Subgroup G) ⊓ normalizer (c.hall:Set G) ≤ centralizer ({(s:G)}:Set G) := by
      rw [hgen]
      refine sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hxf s hs))) ?_
      intro f hf
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val ((IsMulCommutative.is_comm (M:=F)).comm (⟨f,hf⟩:F) ⟨s,hs⟩)
    exact mem_centralizer_singleton_iff.mp (hA ⟨a.property,ha⟩)
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
      apply le_trans ?_ hlow
      by_cases htZ : t∈centralizer (Z:Set G)
      · have he := (source_outside_involution_center_fixed d hG T hST hsingle hL hM hTM hu t ht htS htpow htZ).1
        change R ⊓ centralizer ({t}:Set G)=Z at he
        rw [he]
        have hZcard : Nat.card Z=2^n := by
          simpa only [distinguishedZ_of_centerless d hZ] using
            (source_distinguished_elementary d hG T hST hsingle hL hM hTM hu).2.1
        rw [hZcard,hn]
        exact Nat.pow_le_pow_right (by decide) (by omega)
      · obtain ⟨k,_,hk,_,hc,_,_⟩ := source_centerless_outside_noncentral_fixed_data d hG T hST hsingle hL
          hM hTM hu c hZ t ht htS htpow htZ
        have he : k=m := by omega
        simpa only [he] using hc.le
  have hh := card_centralizer_le_of_complement_core_card RT A c.split_ambient s ⟨t,ht⟩ hAs (by
    rw [hcardmap,hcardmap]
    exact hfixed)
  rw [←map_subtype_centralizer_singleton (T:Subgroup G) ⟨t,ht⟩,
    ←map_subtype_centralizer_singleton (T:Subgroup G) s,
    card_map_of_injective (T:Subgroup G).subtype_injective,
    card_map_of_injective (T:Subgroup G).subtype_injective]
  exact hh
end CFSG.Quasithin.Chapter2.LinearShadows.Single
