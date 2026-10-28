module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CubicDerivedFactor
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.OverlapPair
public import Theory.GroupTheory.IndexTwoRetainedInvolutionComplement

/-!
# The cubic complement retaining the original pair overlap

The canonical A₆ in the literal cubic centralizer contains the canonical
D₁₀ factor of the original overlap. An involution in the actual pair
normalizer's symmetric factor centralizes that entire dihedral factor
and inverts the same cubic. Adjoining this specified involution to A₆
constructs a complement to the full cubic kernel. Its intersection with
the original pair normalizer is exactly the retained C₂ × D₁₀.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

private theorem three_cycle_inverter : ∀ s : Equiv.Perm (Fin 3),
    s ^ 3 = 1 → s ≠ 1 →
    ∃ y, y ^ 2 = 1 ∧ y ≠ 1 ∧ y * s * y⁻¹ = s⁻¹ ∧
      ∀ x, ∃ (i : Fin 3) (k : Fin 2), x = s ^ i.val * y ^ k.val := by
  decide +kernel

private theorem cubic_centralizer_tenth : ∀ s x : Equiv.Perm (Fin 3),
    s ^ 3 = 1 → s ≠ 1 → s * x = x * s → x ^ 10 = 1 → x = 1 := by
  decide +kernel

private theorem pair_factor_data {H : Type*} [Group H]
    (e : H ≃* (Equiv.Perm (Fin 3) × DihedralGroup 5))
    (s f : H) (hs : orderOf s = 3) (hf : orderOf f = 2) (hsf : Commute s f) :
    ∃ (B : Subgroup H) (_eB : B ≃* DihedralGroup 5) (y : H),
      (∀ x, x ∈ B ↔ Commute s x ∧ x ^ 10 = 1) ∧ f ∈ B ∧
      orderOf y = 2 ∧ y * s * y⁻¹ = s⁻¹ ∧
      (∀ b ∈ B, Commute y b) ∧
      ∀ x : H, ∃ (i : Fin 3) (b : B) (k : Fin 2),
        x = s ^ i.val * (b : H) * y ^ k.val := by
  have hsp : s ^ 3 = 1 := hs ▸ pow_orderOf_eq_one s
  have hsp' : (e s).1 ^ 3 = 1 := by
    simpa only [map_pow,map_one,Prod.pow_fst,Prod.fst_one] using congrArg (fun x => (e x).1) hsp
  have hss : (e s).2 = 1 := by
    have hp : (e s).2 ^ 3 = 1 := by
      simpa only [map_pow,map_one,Prod.pow_snd,Prod.snd_one] using congrArg (fun x => (e x).2) hsp
    exact (show ∀ d : DihedralGroup 5, d ^ 3 = 1 → d = 1 by decide +kernel) _ hp
  have hsn : (e s).1 ≠ 1 := by
    intro hn
    have he : e s = 1 := Prod.ext hn hss
    have he' : s = 1 := e.injective (he.trans e.map_one.symm)
    simp only [he',orderOf_one] at hs
    omega
  obtain ⟨r,hr2,hrn,hri,hrgen⟩ := three_cycle_inverter (e s).1 hsp' hsn
  let b : DihedralGroup 5 →* H := e.symm.toMonoidHom.comp
    (MonoidHom.inr (Equiv.Perm (Fin 3)) (DihedralGroup 5))
  have hb : Function.Injective b := by
    intro x y h
    have hh := congrArg (fun z => (e z).2) h
    simpa only [b,MonoidHom.comp_apply,MonoidHom.inr_apply,MulEquiv.coe_toMonoidHom,
      e.apply_symm_apply] using hh
  let B := b.range
  let eB : B ≃* DihedralGroup 5 := (MonoidHom.ofInjective hb).symm
  have hbmem (x : H) : x ∈ B ↔ (e x).1 = 1 := by
    constructor
    · rintro ⟨d,rfl⟩
      exact congrArg Prod.fst (e.apply_symm_apply (1,d))
    · intro hx
      refine ⟨(e x).2,?_⟩
      change e.symm (1,(e x).2) = x
      rw [←hx,Prod.mk.eta,e.symm_apply_apply]
  have hmem (x : H) : x ∈ B ↔ Commute s x ∧ x ^ 10 = 1 := by
    rw [hbmem]
    constructor
    · intro hx
      constructor
      · apply e.injective
        simp only [map_mul,Prod.ext_iff,Prod.fst_mul,Prod.snd_mul,hx,hss,mul_one,one_mul,and_self]
      · apply e.injective
        have hd : (e x).2 ^ 10 = 1 := by
          simpa only [DihedralGroup.nat_card] using pow_card_eq_one' (x := (e x).2)
        simp only [map_pow,map_one,Prod.ext_iff,Prod.pow_fst,Prod.pow_snd,Prod.fst_one,
          Prod.snd_one,hx,one_pow,hd,and_self]
    · rintro ⟨hc,hp⟩
      apply cubic_centralizer_tenth _ _ hsp' hsn
      · exact congrArg Prod.fst (hc.map e.toMonoidHom).eq
      · simpa only [map_pow,map_one,Prod.pow_fst,Prod.fst_one] using
          congrArg (fun x => (e x).1) hp
  have hfB : f ∈ B := by
    apply (hmem f).mpr
    refine ⟨hsf,?_⟩
    have hf2 : f ^ 2 = 1 := hf ▸ pow_orderOf_eq_one f
    rw [show 10 = 2 * 5 from rfl,pow_mul,hf2,one_pow]
  let y := e.symm (r,1)
  have hy2 : y ^ 2 = 1 := by
    apply e.injective
    rw [map_pow,map_one,show e y = (r,1) from e.apply_symm_apply _,Prod.pow_mk,hr2,one_pow]
    rfl
  have hyn : y ≠ 1 := by
    intro h
    have hh := congrArg (fun x => (e x).1) h
    apply hrn
    simpa only [y,e.apply_symm_apply,map_one,Prod.fst_one] using hh
  have hiy : y * s * y⁻¹ = s⁻¹ := by
    apply e.injective
    simp only [map_mul,map_inv,y,e.apply_symm_apply,Prod.ext_iff,Prod.fst_mul,
      Prod.snd_mul,Prod.fst_inv,Prod.snd_inv,hss,mul_one,inv_one,hri,and_self]
  have hyB (d) (hd : d ∈ B) : Commute y d := by
    apply e.injective
    simp only [map_mul,y,e.apply_symm_apply,Prod.ext_iff,Prod.fst_mul,Prod.snd_mul,
      (hbmem d).mp hd,mul_one,one_mul,and_self]
  refine ⟨B,eB,y,hmem,hfB,orderOf_eq_prime hy2 hyn,hiy,hyB,?_⟩
  intro x
  obtain ⟨i,k,hik⟩ := hrgen (e x).1
  let d : B := ⟨b (e x).2,⟨(e x).2,rfl⟩⟩
  refine ⟨i,d,k,?_⟩
  apply e.injective
  simp only [map_mul,map_pow,y,d,b,MonoidHom.comp_apply,MonoidHom.inr_apply,
    MulEquiv.coe_toMonoidHom,e.apply_symm_apply,Prod.ext_iff,Prod.fst_mul,Prod.snd_mul,
    Prod.pow_fst,Prod.pow_snd,hss,one_pow,mul_one,one_mul,hik,and_self]

private theorem mem_complement_of_power_coprime {H : Type*} [Group H] [Finite H]
    (V D : Subgroup H) [D.Normal] (hcomp : V.IsComplement' D)
    (hV : Nat.card V = 3) (x : H) (hx : x ^ 10 = 1) : x ∈ D := by
  let q := QuotientGroup.mk' D
  have hq3 : q x ^ 3 = 1 := by
    have hc : Nat.card (H ⧸ D) = 3 :=
      (Nat.card_congr hcomp.QuotientMulEquiv.toEquiv).trans hV
    simpa only [hc] using pow_card_eq_one' (x := q x)
  have hq10 : q x ^ 10 = 1 := by rw [←map_pow,hx,map_one]
  have hq9 : q x ^ 9 = 1 := by rw [show 9 = 3 * 3 from rfl,pow_mul,hq3,one_pow]
  apply (QuotientGroup.eq_one_iff x).mp
  change q x = 1
  simpa only [show 10 = 9 + 1 from rfl,pow_succ,hq9,one_mul] using hq10

/-- A complement to the entire original cubic kernel retaining the actual
D₁₀ overlap and a commuting inverting involution. Their join is precisely
its intersection with the full original pair normalizer. -/
theorem literal_cubic_normalizer_marked_complement
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (ha : ∀ (c : C) (x : A), a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j) :
    let s := j cubic
    let f := j SingerField.fieldElement
    let N := normalizer (zpowers s : Set G)
    let D₀ := (_root_.commutator (centralizer ({s} : Set G))).map
      (inclusion (cubic_centralizer_le_normalizer s))
    ∃ (B : Subgroup G) (y : N) (K : Subgroup N),
      (∀ x, x ∈ B ↔ x ∈ overlap j ∧ x ^ 10 = 1) ∧
      Nonempty (B ≃* DihedralGroup 5) ∧ f ∈ B ∧
      (y : G) ∈ normalizer (overlap j : Set G) ∧ orderOf y = 2 ∧
      (y : G) * s * (y : G)⁻¹ = s⁻¹ ∧
      (∀ b ∈ B, Commute (y : G) b) ∧
      K = D₀ ⊔ zpowers y ∧
      (cubicNormalizerKernel s).IsComplement' K ∧
      Nonempty (K ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) ∧
      B ≤ K.map N.subtype ∧
      normalizer (overlap j : Set G) ⊓ K.map N.subtype = B ⊔ zpowers (y : G) ∧
      Nonempty ((normalizer (overlap j : Set G) ⊓ K.map N.subtype : Subgroup G) ≃*
        (Multiplicative (ZMod 2) × DihedralGroup 5)) := by
  classical
  let s := j cubic
  let f := j SingerField.fieldElement
  let N := normalizer (zpowers s : Set G)
  let Z := centralizer ({s} : Set G)
  let H := Z.subgroupOf N
  let L := normalizer (overlap j : Set G)
  let V := cubicNormalizerKernel s
  let D0 := _root_.commutator Z
  have hZN : Z ≤ N := cubic_centralizer_le_normalizer s
  let i : Z →* N := inclusion hZN
  let DN := D0.map i
  have hi : i.range = H := by
    ext z
    constructor
    · rintro ⟨c,rfl⟩
      exact c.property
    · intro hz
      exact ⟨⟨z,hz⟩,rfl⟩
  have hDN : DN ≤ H := by rw [←hi]; exact map_le_range i D0
  let : H.Normal := by
    have he : centralizer (zpowers s : Set G) = Z := by
      rw [zpowers_eq_closure,centralizer_closure]
    change (Z.subgroupOf N).Normal
    rw [←he]
    infer_instance
  have hDNcomm : DN = ⁅H,H⁆ := by
    change D0.map i = ⁅H,H⁆
    rw [map_commutator_eq,hi]
  let : DN.Normal := hDNcomm ▸ inferInstance
  have hs : orderOf s = 3 := (orderOf_injective j hj.1 _).trans cubic_order
  have hf : orderOf f = 2 := image_involution_order j hj.1
  have hsf : Commute s f :=
    (cubic_commutes_complement ⟨SingerField.fieldElement,(mem_pointComplement _).mpr rfl⟩).map j
  have hsL : s ∈ L := (overlap j).le_normalizer (mem_map_of_mem j cubic_mem)
  have hfL : f ∈ L := (overlap j).le_normalizer (image_involution_mem j)
  let sL : L := ⟨s,hsL⟩
  let fL : L := ⟨f,hfL⟩
  obtain ⟨eL⟩ := literal_overlap_pair_equiv P hc A C a j hj
  obtain ⟨B0,eB0,yL,hB0,hfB0,hyL,hiyL,hyB0,hgen⟩ := pair_factor_data eL sL fL
    ((orderOf_coe _).symm.trans hs) ((orderOf_coe _).symm.trans hf) (Subtype.ext hsf.eq)
  let B := B0.map L.subtype
  let eB : B ≃* DihedralGroup 5 :=
    (B0.equivMapOfInjective L.subtype L.subtype_injective).symm.trans eB0
  have hmem (x : G) : x ∈ B ↔ x ∈ overlap j ∧ x ^ 10 = 1 := by
    constructor
    · rintro ⟨u,hu,rfl⟩
      obtain ⟨hcomm,hpow⟩ := (hB0 u).mp hu
      refine ⟨?_,congrArg Subtype.val hpow⟩
      rw [←literal_overlap_cubic_centralizer_eq P hc A C a j hj]
      exact ⟨u.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val hcomm.eq).symm⟩
    · rintro ⟨hx,hp⟩
      let u : L := ⟨x,(overlap j).le_normalizer hx⟩
      refine ⟨u,(hB0 u).mpr ⟨?_,Subtype.ext hp⟩,rfl⟩
      have hxu : x ∈ L ⊓ Z :=
        (literal_overlap_cubic_centralizer_eq P hc A C a j hj).symm ▸ hx
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hxu.2).symm
  have hBL : B ≤ L := map_le_range L.subtype B0 |>.trans (by rw [range_subtype])
  have hLN : L ≤ N := overlap_normalizer_le_cubic j hj.1
  let y : N := inclusion hLN yL
  have hy2 : y ^ 2 = 1 := by
    exact congrArg (inclusion hLN) (hyL ▸ pow_orderOf_eq_one yL)
  have hyout : y ∉ H := by
    intro hyH
    have hcomm := mem_centralizer_singleton_iff.mp (show (y:G) ∈ Z from hyH)
    have he : s = s⁻¹ := by
      have hh := congrArg Subtype.val hiyL
      change (y:G) * s * (y:G)⁻¹ = s⁻¹ at hh
      rwa [hcomm,mul_inv_cancel_right] at hh
    have hp : s ^ 2 = 1 := by rw [pow_two]; nth_rw 1 [he]; exact inv_mul_cancel _
    have hh := orderOf_dvd_of_pow_eq_one hp
    norm_num [hs] at hh
  obtain ⟨hcomp,_⟩ := literal_cubic_derived_factor P hc A C l a ha j hj
  have hVH : V ≤ H := fun x hx => cubic_le_centralizer s hx
  have hVD : (V.subgroupOf H).IsComplement' (DN.subgroupOf H) := by
    refine ⟨mul_injective_of_disjoint ?_,?_⟩
    · apply disjoint_def.mpr
      intro x hxV hxD
      obtain ⟨d,hd,hed⟩ := hxD
      apply Subtype.ext
      apply Subtype.ext
      have hdV : d ∈ cubicKernel s := by
        change (d:G) ∈ zpowers s
        exact (congrArg Subtype.val hed).symm ▸ hxV
      have hd1 := disjoint_def.mp hcomp.disjoint hdV hd
      exact (congrArg (fun n : N => (n:G)) hed).symm.trans
        (congrArg (fun z : Z => (z:G)) hd1)
    · intro x
      let z : Z := ⟨((x:N):G),x.property⟩
      obtain ⟨⟨v,d⟩,hvd⟩ := hcomp.2 z
      let vH : V.subgroupOf H := ⟨⟨i v,hVH (show i v ∈ V from v.property)⟩,v.property⟩
      let dH : DN.subgroupOf H := ⟨⟨i d,hDN (mem_map_of_mem i d.property)⟩,
        mem_map_of_mem i d.property⟩
      refine ⟨(vH,dH),?_⟩
      apply Subtype.ext
      exact congrArg i hvd
  have hindex : H.index = 2 := cubic_normalizer_index D.localType hc s f hs hf hsf
  let K := DN ⊔ zpowers y
  have hK : V.IsComplement' K := isComplement'_sup_zpowers_of_index_two V DN H
    hVH hDN hVD hindex y hy2 hyout (by rw [DN.normalizer_eq_top]; exact mem_top y)
  let KA := K.map N.subtype
  have hBK : B ≤ KA := by
    intro b hb
    obtain ⟨hbL,hb10⟩ := (hmem b).mp hb
    have hbZ : b ∈ Z := by
      have hh := (literal_overlap_cubic_centralizer_eq P hc A C a j hj).symm ▸ hbL
      exact hh.2
    let z : Z := ⟨b,hbZ⟩
    have hzD : z ∈ D0 := mem_complement_of_power_coprime _ _ hcomp
      (cubicKernel_card s hs) z (Subtype.ext hb10)
    exact ⟨i z,mem_sup_left (mem_map_of_mem i hzD),rfl⟩
  have hyKA : (y:G) ∈ KA := mem_map_of_mem N.subtype (mem_sup_right (mem_zpowers y))
  have hpair : L ⊓ KA = B ⊔ zpowers (y:G) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨m,b,k,he⟩ := hgen (⟨x,hx.1⟩ : L)
      have heG : x = s ^ m.val * ((b:L):G) * (y:G) ^ k.val := congrArg Subtype.val he
      have hbB : ((b:L):G) ∈ B := mem_map_of_mem L.subtype b.property
      have htK : ((b:L):G) * (y:G) ^ k.val ∈ KA := KA.mul_mem (hBK hbB) (KA.pow_mem hyKA _)
      have hsK : s ^ m.val ∈ KA := by
        have hh := KA.mul_mem hx.2 (KA.inv_mem htK)
        rw [heG] at hh
        have hec : s ^ m.val * ((b:L):G) * (y:G) ^ k.val *
            (((b:L):G) * (y:G) ^ k.val)⁻¹ = s ^ m.val := by group
        exact hec ▸ hh
      obtain ⟨v,hv,hve⟩ := hsK
      change (v:G) = s ^ m.val at hve
      have hvV : v ∈ V := by
        change (v:G) ∈ zpowers s
        rw [hve]
        exact pow_mem (mem_zpowers s) _
      have hv1 := disjoint_def.mp hK.disjoint hvV hv
      have hsp : s ^ m.val = 1 := hve.symm.trans (congrArg Subtype.val hv1)
      rw [heG,hsp,one_mul]
      exact mul_mem_sup hbB (pow_mem (mem_zpowers (y:G)) _)
    · exact sup_le (le_inf hBL hBK) (zpowers_le.mpr ⟨yL.property,hyKA⟩)
  have hyB (b) (hb : b ∈ B) : Commute (y:G) b := by
    obtain ⟨u,hu,rfl⟩ := hb
    exact congrArg Subtype.val (hyB0 u hu).eq
  have hdis : Disjoint (zpowers (y:G)) B := by
    apply disjoint_def.mpr
    intro x hxY hxB
    have hxZ : x ∈ Z := by
      have hxO := ((hmem x).mp hxB).1
      have hh := (literal_overlap_cubic_centralizer_eq P hc A C a j hj).symm ▸ hxO
      exact hh.2
    have hyG : orderOf (y:G) = 2 := (orderOf_coe y).trans
      ((orderOf_injective (inclusion hLN) (inclusion_injective hLN) yL).trans hyL)
    rw [mem_zpowers_iff_mem_range_orderOf,hyG] at hxY
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hxY
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · exact pow_zero _
    · have hh : (y:G) ∈ Z := by simpa only [pow_one] using hxZ
      exact (hyout hh).elim
  have hcomm : zpowers (y:G) ≤ centralizer (B:Set G) := zpowers_le.mpr
    (mem_centralizer_iff.mpr fun b hb => (hyB b hb).eq.symm)
  obtain ⟨eprod,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (zpowers (y:G)) B hdis hcomm
  have hyG : orderOf (y:G) = 2 := (orderOf_coe y).trans
    ((orderOf_injective (inclusion hLN) (inclusion_injective hLN) yL).trans hyL)
  let e2 : zpowers (y:G) ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq (by rw [Nat.card_zpowers,hyG])
      (by simp [Nat.card_eq_fintype_card])
  obtain ⟨_,⟨eN⟩⟩ := literal_field_cubic_projective P hc A C a j hj
  refine ⟨B,y,K,hmem,⟨eB⟩,mem_map_of_mem L.subtype hfB0,yL.property,
    (orderOf_injective (inclusion hLN) (inclusion_injective hLN) yL).trans hyL,
    congrArg Subtype.val hiyL,hyB,rfl,hK,⟨hK.symm.QuotientMulEquiv.symm.trans eN⟩,
    hBK,hpair,?_⟩
  exact ⟨(MulEquiv.subgroupCongr (hpair.trans (sup_comm _ _))).trans
    (eprod.symm.trans (e2.prodCongr eB))⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
