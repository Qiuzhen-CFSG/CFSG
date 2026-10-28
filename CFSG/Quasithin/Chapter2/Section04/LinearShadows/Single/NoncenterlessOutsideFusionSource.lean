module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ModuleFusionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DeltaCentralSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterFieldKernelSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideSuzukiSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DeltaGeometrySource
public import Theory.ElementaryAbelian.CyclicKernel
public import Theory.GroupAction.FourGroupSylowCentralizer

/-!
# Excluding outside involutions in the nontrivial-center branch

An outside involution a has fixed subgroup I=C_R(a) whose derived group
is elementary of order 2^n>2. Fusion into R places a in the center of a
centralizer Sylow conjugate to S or T. In either case I lies in the matching
conjugate of T, and the index-two subgroup S contains its derived group.
The cyclic quotient S/R forces that elementary derived group to meet the
conjugate of R nontrivially. Such a fixed element lies in the mixed orbit Δ.
The generated-subgroup result of 2.4.20(6) then puts the conjugate of Z(R)
inside R, contradicting a∉S.

All fixed-derived, fusion, centralizer, and generated-subgroup inputs are
constructed from the original setup. The final theorem applies the result
to literal conjugates of involutions in R.

Source: Aschbacher–Smith, 2.4.21, first claim in the nontrivial-center case,
printed pp.535–536, using 2.4.14(3) and 2.4.20(2),(3),(5),(6).
-/

public section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
private theorem derived_le_index_two (S T : Subgroup G) (hindex : (S.subgroupOf T).index=2) :
    ⁅T,T⁆ ≤ S := by
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  have hh : ⁅(⟨x,hx⟩ : T), (⟨y,hy⟩ : T)⁆ ∈ S.subgroupOf T := by
    simp only [commutatorElement_def, (S.subgroupOf T).mul_mem_iff_of_index_two hindex,
      (S.subgroupOf T).inv_mem_iff]
    tauto
  exact hh

variable (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)

include hG hST hsingle hL hM hTM hunique

private theorem source_center_sylow_le_center_R :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    S ⊓ centralizer (S : Set G) ≤ R ⊓ centralizer (R : Set G) := by
  intro S R
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have hZS : distinguishedZ d ≤ S :=
    (source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique).2.2.1.trans
      (inf_le_left.trans hRS)
  intro a ha
  refine ⟨?_,centralizer_le hRS ha.2⟩
  change a∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)
  rw [←source_distinguished_sylow_centralizer_eq d hG T hST hsingle hL hM hTM hunique]
  exact ⟨ha.1,centralizer_le hZS ha.2⟩

private theorem source_center_ambient_sylow_le_center_R
    (hz : center (d.block.map d.H.subtype) ≠ ⊥) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    (T : Subgroup G) ⊓ centralizer (T : Set G) ≤ R ⊓ centralizer (R : Set G) := by
  intro R a ha
  have hZS : distinguishedZ d ≤ (d.S : Subgroup d.H).map d.H.subtype :=
    (source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique).2.2.1.trans
      (inf_le_left.trans (sSup_le fun _ h => h.1))
  apply source_center_sylow_le_center_R d hG T hST hsingle hL hM hTM hunique
  refine ⟨?_,centralizer_le hST.le ha.2⟩
  rw [←source_distinguished_normalizer_in_sylow d hG T hST hsingle hL hM hTM hunique hz]
  exact ⟨ha.1,Subgroup.centralizer_le_normalizer _ (centralizer_le (hZS.trans hST.le) ha.2)⟩

private theorem source_elementary_card_le_two_of_disjoint_R
    (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hES : E ≤ (d.S : Subgroup d.H).map d.H.subtype)
    (hdis : Disjoint E (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))) :
    Nat.card E ≤ 2 := by
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let : IsCyclic (d.H ⧸ d.block) :=
    source_single_quotient_cyclic d hG T hST hsingle hL hM hTM hunique
  let f : E →* d.H ⧸ d.block := (QuotientGroup.mk' d.block).comp
    (inclusion (hES.trans (map_subtype_le _)))
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro e he
    have heL : (e:G) ∈ d.block.map d.H.subtype :=
      mem_map_of_mem d.H.subtype ((QuotientGroup.eq_one_iff _).mp he)
    have heR : (e:G) ∈ Stellmacher.elementaryAbelianMaxJ
        ((d.S : Subgroup d.H).map d.H.subtype) := by
      rw [(source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).1]
      exact ⟨hES e.property,heL⟩
    exact Subtype.ext (disjoint_def.mp hdis e.property heR)
  let : IsCyclic E := isCyclic_of_injective f hf
  have hc : Nat.card E ∣ 2 := by
    rw [←IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 E
  exact Nat.le_of_dvd (by decide) hc

private theorem source_elementary_meets_conjugate_R
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hcard : 2 < Nat.card E) (g : G)
    (hES : E ≤ ((d.S : Subgroup d.H).map d.H.subtype).map (MulAut.conj g).toMonoidHom) :
    E ⊓ (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).map
      (MulAut.conj g).toMonoidHom ≠ ⊥ := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let e := MulAut.conj g
  let D := E.map e.symm.toMonoidHom
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map e.symm.toMonoidHom
  have hDS : D ≤ S := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy,rfl⟩ := hES hx
    change e.symm (e y)∈S
    rw [e.symm_apply_apply]
    exact hy
  intro hbot
  have hdis : Disjoint D R := by
    apply disjoint_def.mpr
    intro x hx hR
    obtain ⟨y,hy,he⟩ := hx
    have hex : e x=y := by rw [←he];exact e.apply_symm_apply y
    have hh : y ∈ E ⊓ R.map e.toMonoidHom := ⟨hy,⟨x,hR,hex⟩⟩
    have hy1 : y=1 := mem_bot.mp (hbot ▸ hh)
    apply e.injective
    rw [hex,hy1,map_one]
  have hc := source_elementary_card_le_two_of_disjoint_R d hG T hST hsingle hL hM hTM hunique D hDS hdis
  have hecard : Nat.card D=Nat.card E := card_map_of_injective e.symm.injective
  rw [hecard] at hc
  omega


omit hG hST hsingle hL hM hTM hunique [Finite G] in
private theorem mem_centralizer_sylow_image (z : G) (hz2 : z^2=1)
    (P : Sylow 2 (centralizer ({z}:Set G))) :
    z ∈ (P : Subgroup (centralizer ({z}:Set G))).map (centralizer ({z}:Set G)).subtype := by
  let C := centralizer ({z}:Set G)
  let zC : C := ⟨z,mem_centralizer_singleton_iff.mpr rfl⟩
  apply mem_map_of_mem C.subtype (x := zC)
  apply Theory.GroupAction.mem_sylow_of_sq_eq_one_of_centralizes P (Subtype.ext hz2)
  intro p _
  exact Subtype.ext (mem_centralizer_singleton_iff.mp p.property)

private theorem source_star_of_distinguished_fusion
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (I : Subgroup G) (hIp : IsPGroup 2 I) (a z : G)
    (hIC : I ≤ centralizer ({a}:Set G)) (hzZ : z ∈ distinguishedZ d) (hz1 : z≠1)
    (hconj : IsConj z a) :
    ∃ g : G, I ≤ (T : Subgroup G).map (MulAut.conj g).toMonoidHom ∧
      a ∈ ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) ⊓
        centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)).map
          (MulAut.conj g).toMonoidHom := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let ZR := R ⊓ centralizer (R:Set G)
  obtain ⟨g,hg⟩ := isConj_iff.mp hconj
  let e := MulAut.conj g
  let C := centralizer ({z}:Set G)
  let J := I.map e.symm.toMonoidHom
  have hJC : J≤C := by
    rintro _ ⟨i,hi,rfl⟩
    have hc : Commute i a := mem_centralizer_singleton_iff.mp (hIC hi)
    have hcz := hc.map e.symm.toMonoidHom
    have hga : e.symm a=z := by rw [←hg];exact e.symm_apply_apply z
    apply mem_centralizer_singleton_iff.mpr
    simpa only [MulEquiv.coe_toMonoidHom,hga] using hcz.eq
  obtain ⟨P,hJP⟩ := ((hIp.map e.symm.toMonoidHom).comap_subtype (K:=C)).exists_le_sylow
  have hJP' : J ≤ (P:Subgroup C).map C.subtype := by
    rw [←map_subgroupOf_eq_of_le hJC]
    exact map_mono hJP
  obtain ⟨h,hh⟩ := source_distinguished_centralizer_sylow d hG T hST hsingle hL hM hTM hunique
    hz z hzZ hz1 P
  let : IsElementaryAbelian 2 (distinguishedZ d) :=
    (source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique).1
  have hzP := mem_centralizer_sylow_image z (elemPow_eq_one_of_isElementaryAbelian z hzZ) P
  have hzcenter : z ∈ centerIn (S.map (MulAut.conj h).toMonoidHom) := by
    refine ⟨hh ▸ hzP,?_⟩
    intro y hy
    obtain ⟨p,_,rfl⟩ := (hh.symm ▸ hy)
    exact mem_centralizer_singleton_iff.mp p.property
  have hzR : z ∈ ZR.map (MulAut.conj h).toMonoidHom := by
    rw [←centerIn_map_equiv] at hzcenter
    exact map_mono (source_center_sylow_le_center_R d hG T hST hsingle hL hM hTM hunique) hzcenter
  have hI : I ≤ (S.map (MulAut.conj h).toMonoidHom).map e.toMonoidHom := by
    intro i hi
    refine ⟨e.symm i,?_,e.apply_symm_apply i⟩
    exact hh ▸ hJP' (mem_map_of_mem e.symm.toMonoidHom hi)
  have haR : a ∈ (ZR.map (MulAut.conj h).toMonoidHom).map e.toMonoidHom :=
    hg ▸ mem_map_of_mem e.toMonoidHom hzR
  have hmul (X : Subgroup G) : (X.map (MulAut.conj h).toMonoidHom).map e.toMonoidHom =
      X.map (MulAut.conj (g*h)).toMonoidHom := (conjBy_mul X g h).symm
  rw [hmul] at hI haR
  exact ⟨g*h,hI.trans (map_mono hST.le),haR⟩


private theorem source_star_of_delta_fusion
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (x : G) (hxT : x∈T) (hxS : x∉(d.S : Subgroup d.H).map d.H.subtype)
    (I : Subgroup G) (hIp : IsPGroup 2 I) (a u : G)
    (hIC : I≤centralizer ({a}:Set G)) (hu : u∈distinguishedDelta d x)
    (hconj : IsConj a u) :
    ∃ g : G, I ≤ (T : Subgroup G).map (MulAut.conj g).toMonoidHom ∧
      a ∈ ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) ⊓
        centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)).map
          (MulAut.conj g).toMonoidHom := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let ZR := R⊓centralizer (R:Set G)
  obtain ⟨k,hk⟩ := isConj_iff.mp hconj
  obtain ⟨b,_,hb⟩ := (source_distinguished_delta_central d hG T hST hsingle hL hM hTM hunique hz
    x hxT hxS u hu).1
  let t := b*u*b⁻¹
  let g := (b*k)⁻¹
  have hgt : (MulAut.conj g) t=a := by
    change (b*k)⁻¹*(b*u*b⁻¹)*((b*k)⁻¹)⁻¹=a
    rw [←hk]
    group
  let Q : Sylow 2 G := g • T
  have haQ : a∈centerIn (Q:Subgroup G) := by
    change a∈centerIn ((T:Subgroup G).map (MulAut.conj g).toMonoidHom)
    rw [←centerIn_map_equiv]
    exact ⟨t,hb,hgt⟩
  let C := centralizer ({a}:Set G)
  have hQC : (Q:Subgroup G)≤C := by
    intro q hq
    exact mem_centralizer_singleton_iff.mpr (haQ.2 q hq)
  let P₀ : Sylow 2 C := Q.subtype hQC
  obtain ⟨P,hIP⟩ := (hIp.comap_subtype (K:=C)).exists_le_sylow
  have hIP' : I≤(P:Subgroup C).map C.subtype := by
    rw [←map_subgroupOf_eq_of_le hIC]
    exact map_mono hIP
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq C P₀ P
  have hPimage : (P:Subgroup C).map C.subtype =
      ((Q:Subgroup G).map (MulAut.conj (c:G)).toMonoidHom) := by
    rw [←hc]
    change ((P₀:Subgroup C).map (MulAut.conj c).toMonoidHom).map C.subtype = _
    rw [map_map]
    have he : C.subtype.comp (MulAut.conj c).toMonoidHom =
        (MulAut.conj (c:G)).toMonoidHom.comp C.subtype := by ext; rfl
    rw [he,←map_map]
    congr 1
    exact map_subgroupOf_eq_of_le hQC
  have haP : a∈centerIn ((P:Subgroup C).map C.subtype) := by
    rw [hPimage,←centerIn_map_equiv]
    refine ⟨a,haQ,?_⟩
    change (c:G)*a*(c:G)⁻¹=a
    rw [mem_centralizer_singleton_iff.mp c.property,mul_inv_cancel_right]
  have hPimage' : (P:Subgroup C).map C.subtype =
      (T:Subgroup G).map (MulAut.conj ((c:G)*g)).toMonoidHom := by
    rw [hPimage]
    exact (conjBy_mul (T:Subgroup G) (c:G) g).symm
  rw [hPimage'] at hIP' haP
  rw [←centerIn_map_equiv] at haP
  exact ⟨(c:G)*g,hIP',map_mono
    (source_center_ambient_sylow_le_center_R d hG T hST hsingle hL hM hTM hunique hz) haP⟩

private theorem source_fixed_center_nonidentity_mem_delta
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (a : G) (haT : a∈T) (haS : a∉(d.S:Subgroup d.H).map d.H.subtype)
    (v : G)
    (hv : v∈(Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)⊓
      centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype):Set G))⊓
        centralizer ({a}:Set G)) (hv1 : v≠1) :
    v∈distinguishedDelta d a := by
  have hp := source_distinguished_center_pair d hG T hST hsingle hL hM hTM hunique hz a haT haS
  let e := MulAut.conj a⁻¹
  have hc : Commute a v := (mem_centralizer_singleton_iff.mp hv.2).symm
  have hev : e v=v := mul_inv_eq_iff_eq_mul.mpr hc.inv_left.eq
  have hnZ : v∉distinguishedZ d := by
    intro hZ
    exact hv1 (disjoint_def.mp hp.1 hZ ⟨v,hZ,hev⟩)
  refine ⟨hv.1,hnZ,?_⟩
  rintro ⟨z,hzZ,he⟩
  have hzv : z=v := e.injective (he.trans hev.symm)
  exact hnZ (hzv ▸ hzZ)

/-- In the nontrivial-center branch, an involution of T fused into R lies in S.
This is the first claim in the proof of the original 2.4.21. -/
theorem source_noncenterless_fused_involution_mem_sylow
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (a : G) (haT : a∈T) (ha2 : a^2=1)
    (hfused : ∃ r∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype), IsConj a r) :
    a∈(d.S:Subgroup d.H).map d.H.subtype := by
  let S := (d.S:Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let ZR := R⊓centralizer (R:Set G)
  let I := R⊓centralizer ({a}:Set G)
  let J := ⁅I,I⁆
  by_contra haS
  have ha1 : a≠1 := fun he => haS (he ▸ S.one_mem)
  have hRS : R≤S := sSup_le fun _ h => h.1
  have hIp : IsPGroup 2 I := T.isPGroup'.to_le (inf_le_left.trans (hRS.trans hST.le))
  obtain ⟨r,hr,har⟩ := hfused
  have hr2 : r^2=1 := isConj_one_right.mp (ha2 ▸ IsConj.pow 2 har)
  have hr1 : r≠1 := fun he => ha1 (isConj_one_left.mp (he ▸ har))
  have hstar : ∃ g:G, I≤(T:Subgroup G).map (MulAut.conj g).toMonoidHom ∧
      a∈ZR.map (MulAut.conj g).toMonoidHom := by
    rcases lemma_2_4_20_3 d hG T hST hsingle hL hM hTM hunique hz a haT haS r hr hr2 hr1 with
      ⟨z,hzZ,hz1,hrz⟩ | ⟨u,hu,huZ,huZa,hru⟩
    · exact source_star_of_distinguished_fusion d hG T hST hsingle hL hM hTM hunique hz
        I hIp a z inf_le_right hzZ hz1 (har.trans hrz).symm
    · exact source_star_of_delta_fusion d hG T hST hsingle hL hM hTM hunique hz a haT haS
        I hIp a u inf_le_right ⟨hu,huZ,huZa⟩ (har.trans hru)
  obtain ⟨g,hIT,haZR⟩ := hstar
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hTT : ⁅(T:Subgroup G),(T:Subgroup G)⁆≤S := derived_le_index_two S T
    (d.lemma_2_4_8_1 hG T hST hsingle hK).1
  have hJS : J≤S.map (MulAut.conj g).toMonoidHom := by
    apply (commutator_mono hIT hIT).trans
    rw [←map_commutator]
    exact map_mono hTT
  have hd := source_noncenterless_outside_fixed_derived d hG T hST hsingle hL hM hTM hunique
    hz a haT haS ha2
  let U := ChapterC.Section05.ConjugateSource.sourceModule (d.block.map d.H.subtype)
  let : IsElementaryAbelian 2 U := by
    let := hK.2.1.elementary
    exact IsElementaryAbelian.map (d.block.map d.H.subtype).subtype
  have hZRU : ZR≤U := (source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique a haT haS).ge.trans inf_le_left
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.of_le
    (hd.1.le.trans (inf_le_left.trans hZRU))
  have hJcard : 2<Nat.card J := by
    rw [hd.2]
    exact (Nat.pow_lt_pow_right (by decide : 1<2) hL.1)
  have hmeet := source_elementary_meets_conjugate_R d hG T hST hsingle hL hM hTM hunique
    J hJcard g hJS
  obtain ⟨v,hv,hv1⟩ := (J⊓R.map (MulAut.conj g).toMonoidHom).bot_or_exists_ne_one.resolve_left hmeet
  have hvDelta := source_fixed_center_nonidentity_mem_delta d hG T hST hsingle hL hM hTM hunique
    hz a haT haS v (hd.1 ▸ hv.1) hv1
  have hC : ZR.map (MulAut.conj g).toMonoidHom≤centralizer ({v}:Set G) := by
    change (centerIn R).map (MulAut.conj g).toMonoidHom≤_
    rw [centerIn_map_equiv]
    intro z hz
    exact mem_centralizer_singleton_iff.mpr (hz.2 v hv.2).symm
  have hle := source_distinguished_delta_conjugate_center_le d hG T hST hsingle hL hM hTM hunique
    hz a haT haS v hvDelta g hC
  exact haS (hRS (hle haZR))

/-- Actual conjugation form used by the remaining inside-S branches of 2.4.21. -/
theorem source_noncenterless_conjugate_involution_mem_sylow
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (r : G) (hr : r∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype))
    (hr2 : r^2=1) (g : G) (hg : g*r*g⁻¹∈T) :
    g*r*g⁻¹∈(d.S:Subgroup d.H).map d.H.subtype := by
  apply source_noncenterless_fused_involution_mem_sylow d hG T hST hsingle hL hM hTM hunique hz
    (g*r*g⁻¹) hg
  · change ((MulAut.conj g) r)^2=1
    rw [←map_pow,hr2,map_one]
  · exact ⟨r,hr,(isConj_iff.mpr ⟨g,rfl⟩).symm⟩

end CFSG.Quasithin.Chapter2.LinearShadows.Single
