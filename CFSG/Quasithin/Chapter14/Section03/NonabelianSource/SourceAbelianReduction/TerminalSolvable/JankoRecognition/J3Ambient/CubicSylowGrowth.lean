module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.DerivedCubicFusion
public import Theory.SpecificGroups.Janko3.SourceRecognition.PlaneCubicCentralizer

public import Theory.SpecificGroups.AlternatingSix.ElementaryAbelian
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.ElementaryAbelian.Join
public import Mathlib.Data.Fintype.Card
public import Theory.GroupTheory.AbelianCentralizerSylowFusion

/-!
# Actual cubic Sylow growth to order 243

The canonical derived A₆ factor supplies an elementary nine-group. Joining
it with the literal central cubic gives an elementary group E of order27.
Exactly18 of its elements are conjugate to that cubic. Since E is Sylow
in the full cubic centralizer, ambient fusion on those18 elements is already
realized by N_G(E). Orbit-stabilizer forces243 to divide that normalizer,
and subgroup growth produces an actual order243 overgroup of the same E.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

variable {G : Type*} [Group G] [Finite G]

private theorem elementary_cubic_fusion_count
    {G : Type*} [Group G] [Finite G]
    (s : G) (hs : orderOf s = 3)
    (D : Subgroup G) (eD : D ≃* alternatingGroup (Fin 6))
    (hDs : D ≤ centralizer ({s} : Set G)) (hd : Disjoint (zpowers s) D)
    (hi : IsConj s s⁻¹)
    (hpure : ∀ x ∈ D, orderOf x = 3 → ¬ IsConj s x)
    (hmix : ∀ x ∈ D, orderOf x = 3 → IsConj s (s*x) ∧ IsConj s (s⁻¹*x)) :
    ∃ E : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 27 ∧ s ∈ E ∧
      Nat.card {x : E // IsConj s (x : G)} = 18 := by
  classical
  obtain ⟨V₀,hV₀,hV₀card⟩ := alternatingGroup.exists_elementaryAbelian_nine_of_equiv eD
  let : IsElementaryAbelian 3 V₀ := hV₀
  let V := V₀.map D.subtype
  let : IsElementaryAbelian 3 V := IsElementaryAbelian.map D.subtype
  have hVD : V ≤ D := map_subtype_le _
  have hV : Nat.card V = 9 := (card_map_of_injective D.subtype_injective).trans hV₀card
  let Z := zpowers s
  let : IsElementaryAbelian 3 Z := IsElementaryAbelian.zpowers_of_pow_eq_one
    (by simpa only [hs] using pow_orderOf_eq_one s)
  have hZ : Nat.card Z = 3 := (Nat.card_zpowers s).trans hs
  have hc : Z ≤ centralizer (V : Set G) := by
    apply zpowers_le.mpr
    intro v hv
    exact mem_centralizer_singleton_iff.mp (hDs (hVD hv))
  have hdis : Disjoint Z V := hd.mono_right hVD
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting Z V hdis hc
  let E := Z ⊔ V
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hc)
  have hE : Nat.card E = 27 := by
    rw [←Nat.card_congr e.toEquiv,Nat.card_prod,hZ,hV]
  have hv3 (v : V) (hv : v ≠ 1) : orderOf (v : G) = 3 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (v : G) v.property)
      (fun hh => hv (Subtype.ext hh))
  have hzcase (z : Z) (hz : z ≠ 1) : (z : G) = s ∨ (z : G) = s⁻¹ := by
    have hzmem := z.property
    rw [mem_zpowers_iff_mem_range_orderOf,hs] at hzmem
    obtain ⟨n,hn,hnz⟩ := Finset.mem_image.mp hzmem
    have hn3 : n < 3 := Finset.mem_range.mp hn
    interval_cases n
    · exact (hz (Subtype.ext (by simpa only [pow_zero,OneMemClass.coe_one] using hnz.symm))).elim
    · exact Or.inl (by simpa only [pow_one] using hnz.symm)
    · right
      have hpow : s^2 = s⁻¹ := by
        apply mul_right_cancel (b := s)
        have hs3 : s^3 = 1 := by simpa only [hs] using pow_orderOf_eq_one s
        rw [←pow_succ,hs3,inv_mul_cancel]
      exact hnz.symm.trans hpow
  have hiff (z : Z) (v : V) : IsConj s (e (z,v) : G) ↔ z ≠ 1 := by
    rw [he]
    constructor
    · intro hh hz
      subst z
      simp only [OneMemClass.coe_one,one_mul] at hh
      by_cases hv : v = 1
      · subst v
        have hs1 := isConj_one_left.mp hh
        rw [hs1,orderOf_one] at hs
        contradiction
      · exact hpure v (hVD v.property) (hv3 v hv) hh
    · intro hz
      rcases hzcase z hz with hz | hz
      · rw [hz]
        by_cases hv : v = 1
        · subst v
          simpa only [OneMemClass.coe_one,mul_one] using (IsConj.refl s)
        · exact (hmix v (hVD v.property) (hv3 v hv)).1
      · rw [hz]
        by_cases hv : v = 1
        · subst v
          simpa using hi
        · exact (hmix v (hVD v.property) (hv3 v hv)).2
  let q : ({z : Z // z ≠ 1} × V) ≃ {x : E // IsConj s (x : G)} := {
    toFun := fun p => ⟨e (p.1.val,p.2),(hiff p.1.val p.2).mpr p.1.property⟩
    invFun := fun x => (⟨(e.symm x.val).1,(hiff (e.symm x.val).1 (e.symm x.val).2).mp (by
      simpa only [Prod.mk.eta,e.apply_symm_apply] using x.property)⟩,(e.symm x.val).2)
    left_inv := by
      rintro ⟨⟨z,hz⟩,v⟩
      simp only [e.symm_apply_apply]
    right_inv := by
      intro x
      apply Subtype.ext
      exact e.apply_symm_apply x.val }
  have hZne : Nat.card {z : Z // z ≠ 1} = 2 := by
    let : Fintype Z := Fintype.ofFinite Z
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,Fintype.card_subtype_eq,
      ←Nat.card_eq_fintype_card,hZ]
  refine ⟨E,inferInstance,hE,mem_sup_left (mem_zpowers s),?_⟩
  rw [←Nat.card_congr q,Nat.card_prod,hZne,hV]

omit [Finite G] in
private theorem conjugate_inverses {x y : G} (h : IsConj x y) : IsConj x⁻¹ y⁻¹ := by
  obtain ⟨g,hg⟩ := isConj_iff.mp h
  refine isConj_iff.mpr ⟨g,?_⟩
  simpa only [conj_inv] using congrArg Inv.inv hg

private theorem normalizer_cubic_cases (s n : G) (hs : orderOf s = 3)
    (hn : n ∈ normalizer (zpowers s : Set G)) :
    n*s*n⁻¹ = s ∨ n*s*n⁻¹ = s⁻¹ := by
  classical
  have hm := (mem_normalizer_iff.mp hn s).mp (mem_zpowers s)
  rw [mem_zpowers_iff_mem_range_orderOf,hs] at hm
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hm
  have hi3 : i < 3 := Finset.mem_range.mp hi
  interval_cases i
  · have hh := (MulAut.conj n).orderOf_eq s
    change orderOf (n*s*n⁻¹) = orderOf s at hh
    rw [←he,pow_zero,orderOf_one,hs] at hh
    contradiction
  · exact Or.inl (by simpa only [pow_one] using he.symm)
  · right
    have hp : s^2=s⁻¹ := by
      apply mul_right_cancel (b := s)
      have hs3 : s^3=1 := by simpa only [hs] using pow_orderOf_eq_one s
      rw [←pow_succ,hs3,inv_mul_cancel]
    exact he.symm.trans hp

private theorem mixed_class_transport (s w x n : G) (hs : orderOf s = 3)
    (hn : n ∈ normalizer (zpowers s : Set G)) (hnw : n*w*n⁻¹=x)
    (hp : IsConj s (s*w)) (hm : IsConj s (s⁻¹*w)) :
    IsConj s (s*x) ∧ IsConj s (s⁻¹*x) := by
  let e := MulAut.conj n
  have hew : e w=x := hnw
  have ht (v : G) (hv : IsConj s v) : IsConj s (e v) :=
    hv.trans (isConj_iff.mpr ⟨n,rfl⟩)
  rcases normalizer_cubic_cases s n hs hn with hn | hn
  · have hes : e s=s := hn
    exact ⟨by simpa only [map_mul,hes,hew] using ht (s*w) hp,
      by simpa only [map_mul,map_inv,hes,hew] using ht (s⁻¹*w) hm⟩
  · have hes : e s=s⁻¹ := hn
    exact ⟨by simpa only [map_mul,map_inv,hes,hew,inv_inv] using ht (s⁻¹*w) hm,
      by simpa only [map_mul,hes,hew] using ht (s*w) hp⟩

private theorem literal_derived_cubic_class_partition
    {D : Seed G} (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (ha : ∀ (c : C) (x : A), a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j) :
    let s := j cubic
    let Z := centralizer ({s} : Set G)
    let D0 := _root_.commutator Z
    let i : D0 →* G := Z.subtype.comp D0.subtype
    IsConj s s⁻¹ ∧
      (∀ x : D0, orderOf x = 3 → ¬ IsConj s (i x)) ∧
      (∀ x : D0, orderOf x = 3 → IsConj s (s*i x) ∧ IsConj s (s⁻¹*i x)) := by
  let s := j cubic
  let Z := centralizer ({s} : Set G)
  let D0 := _root_.commutator Z
  let i : D0 →* G := Z.subtype.comp D0.subtype
  let k : C →* G := (normalizer (A : Set G)).subtype.comp C.subtype
  have hk : Function.Injective k := Subtype.val_injective.comp Subtype.val_injective
  let c : C →* Z := k.codRestrict Z (fun x => mem_centralizer_singleton_iff.mpr
    (PlaneTransport.field_cubic_centralizes_complement A C l a ha j hj x).symm.eq)
  have hcder (x : C) (hx : x ∈ _root_.commutator C) : c x ∈ D0 := by
    have hh := mem_map_of_mem c hx
    rw [map_commutator_eq] at hh
    exact (commutator_mono le_top le_top) hh
  have hs : orderOf s=3 := (orderOf_injective j hj.1 _).trans cubic_order
  have hsf : Commute s (j SingerField.fieldElement) :=
    (cubic_commutes_complement ⟨SingerField.fieldElement,(mem_pointComplement _).mpr rfl⟩).map j
  have hf : orderOf (j SingerField.fieldElement)=2 := image_involution_order j hj.1
  have hsi : IsConj s s⁻¹ := literal_cubic_fusion_of_commuting_involutions P hc s s⁻¹
    (j SingerField.fieldElement) (j SingerField.fieldElement) hs
    (by simpa only [orderOf_inv] using hs) hf hf hsf hsf.inv_left
  obtain ⟨σ,τ,hσ,_hτ,hinv,hder,hsσ,hsτ,hσout,v,hv,hfixed⟩ :=
    PlaneTransport.field_cubic_nonfusion_witness A C l a ha j hj
  let w : D0 := ⟨c σ,hcder σ hder⟩
  have hw : orderOf w=3 := (orderOf_coe w).symm.trans
    ((orderOf_coe (c σ)).symm.trans ((orderOf_injective k hk σ).trans hσ))
  change Commute s (k σ) at hsσ
  change Commute s (k τ) at hsτ
  change k σ ∉ zpowers s at hσout
  have hprod : orderOf (s*k σ)=3 := by
    apply orderOf_eq_prime
    · rw [hsσ.mul_pow,show s^3=1 by simpa only [hs] using pow_orderOf_eq_one s,
        show (k σ)^3=1 by simpa only [(orderOf_injective k hk σ).trans hσ] using pow_orderOf_eq_one (k σ),one_mul]
    · intro he
      rw [eq_inv_of_mul_eq_one_right he] at hσout
      exact hσout ((zpowers s).inv_mem (mem_zpowers s))
  have hp : IsConj s (s*k σ) := (literal_cubic_fusion_of_commuting_involutions P hc
    (s*k σ) s v (j SingerField.fieldElement) hprod hs
      ((orderOf_coe v).trans hv) hf hfixed hsf).symm
  have hm : IsConj s (s⁻¹*k σ) := by
    let b := MulAut.conj (k τ)
    have hbs : b s=s := mul_inv_eq_iff_eq_mul.mpr hsτ.symm.eq
    have hbw : b (k σ)=(k σ)⁻¹ := by
      change k τ*k σ*(k τ)⁻¹=(k σ)⁻¹
      simpa only [map_mul,map_inv] using congrArg k hinv
    have hb : b ((s*k σ)⁻¹)=s⁻¹*k σ := by
      rw [map_inv,map_mul,hbs,hbw,mul_inv_rev,inv_inv]
      exact hsσ.inv_left.symm.eq
    exact (hsi.trans (conjugate_inverses hp)).trans (isConj_iff.mpr ⟨k τ,hb⟩)
  have hmix (x : D0) (hx : orderOf x=3) : IsConj s (s*i x) ∧ IsConj s (s⁻¹*i x) := by
    obtain ⟨n,hn,hnw⟩ := literal_derived_cubics_fuse P hc A C l a ha j hj w x hw hx
    exact mixed_class_transport s (k σ) (i x) n hs hn hnw hp hm
  obtain ⟨σ₀,hσ₀,hder₀,_hsσ₀,_hout₀,hnf⟩ := literal_cubic_nonfusion P hc A C l a ha j hj
  let w₀ : D0 := ⟨c σ₀,hcder σ₀ hder₀⟩
  have hw₀ : orderOf w₀=3 := (orderOf_coe w₀).symm.trans
    ((orderOf_coe (c σ₀)).symm.trans ((orderOf_injective k hk σ₀).trans hσ₀))
  have hpure (x : D0) (hx : orderOf x=3) : ¬ IsConj s (i x) := by
    intro hsx
    obtain ⟨n,_hn,hnx⟩ := literal_derived_cubics_fuse P hc A C l a ha j hj w₀ x hw₀ hx
    have hnx' : IsConj (i w₀) (i x) := isConj_iff.mpr ⟨n,hnx⟩
    exact hnf ((hnx'.trans hsx.symm).trans (hmix w₀ hw₀).1)
  exact ⟨hsi,hpure,hmix⟩


/-- The original cubic lies in an actual elementary27 inside an actual
order243 subgroup of its full normalizer, with the18-element fusion count. -/
theorem literal_cubic_three_growth
    {D : Seed G} (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (ha : ∀ (c : C) (x : A), a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j) :
    ∃ E Q : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 27 ∧ j cubic ∈ E ∧
      Nat.card {x : E // IsConj (j cubic) (x : G)} = 18 ∧
      E ≤ Q ∧ Q ≤ normalizer (E : Set G) ∧ Nat.card Q = 243 := by
  classical
  let s := j cubic
  let Z := centralizer ({s} : Set G)
  let D0 := _root_.commutator Z
  let Dg := D0.map Z.subtype
  have hs : orderOf s=3 := (orderOf_injective j hj.1 _).trans cubic_order
  obtain ⟨hcomp,⟨eD⟩⟩ := literal_cubic_derived_factor P hc A C l a ha j hj
  let eDg : Dg ≃* alternatingGroup (Fin 6) :=
    (D0.equivMapOfInjective Z.subtype Z.subtype_injective).symm.trans eD
  have hDg : Dg ≤ Z := map_subtype_le _
  have hdis : Disjoint (zpowers s) Dg := by
    apply disjoint_def.mpr
    rintro x hx ⟨y,hy,rfl⟩
    have hyk : y ∈ cubicKernel s := hx
    exact congrArg Subtype.val (disjoint_def.mp hcomp.disjoint hyk hy)
  obtain ⟨hi,hpure,hmix⟩ := literal_derived_cubic_class_partition P hc A C l a ha j hj
  have hpa : ∀ x ∈ Dg, orderOf x=3 → ¬ IsConj s x := by
    rintro x ⟨y,hy,rfl⟩ hx
    let yD : D0 := ⟨y,hy⟩
    exact hpure yD ((orderOf_coe yD).symm.trans ((orderOf_coe y).symm.trans hx))
  have hma : ∀ x ∈ Dg, orderOf x=3 → IsConj s (s*x) ∧ IsConj s (s⁻¹*x) := by
    rintro x ⟨y,hy,rfl⟩ hx
    let yD : D0 := ⟨y,hy⟩
    exact hmix yD ((orderOf_coe yD).symm.trans ((orderOf_coe y).symm.trans hx))
  obtain ⟨E,hEp,hE,hsE,hcount⟩ := elementary_cubic_fusion_count s hs Dg eDg hDg hdis hi hpa hma
  let : IsElementaryAbelian 3 E := hEp
  have hEZ : E ≤ Z := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm (⟨x,hx⟩ : E) (⟨s,hsE⟩ : E))
  have hEZcard : Nat.card (E.subgroupOf Z)=27 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEZ).toEquiv).trans hE
  obtain ⟨⟨eA⟩,_⟩ := literal_field_cubic_projective P hc A C a j hj
  have hZcard : Nat.card Z=1080 := cubic_centralizer_card s hs eA
  let S : Sylow 3 Z := Sylow.ofCard (E.subgroupOf Z) (by
    rw [hEZcard,hZcard]
    decide +kernel)
  have hd := fusion_card_mul_card_dvd_normalizer_of_centralizer_sylow E (⟨s,hsE⟩ : E) S rfl
  rw [hcount,hE] at hd
  have h243 : 3^5 ∣ Nat.card (normalizer (E : Set G)) :=
    (show 3^5 ∣ 18*27 by decide).trans hd
  let N := normalizer (E : Set G)
  have hEN : Nat.card (E.subgroupOf N)=3^3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe E.le_normalizer).toEquiv,hE]
    norm_num
  obtain ⟨Q,hQ,hEQ⟩ := Sylow.exists_subgroup_card_pow_prime_le (G := N) 3 h243
    (E.subgroupOf N) hEN (show 3≤5 by decide)
  refine ⟨E,Q.map N.subtype,hEp,hE,hsE,hcount,?_,map_subtype_le _,?_⟩
  · intro x hx
    exact mem_map_of_mem N.subtype (hEQ (show (⟨x,E.le_normalizer hx⟩ : N) ∈ E.subgroupOf N from hx))
  · rw [card_map_of_injective N.subtype_injective,hQ]
    norm_num

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
