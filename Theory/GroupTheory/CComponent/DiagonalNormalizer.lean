module

public import Theory.GroupTheory.PCoreQuotientBorelNormalizer
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.IndexNormal

/-!
# Diagonal Sylow-normalizer lifts from two conjugate components

When the normalizer of a C-component I has index two, its intersection
with an ambient Sylow two-subgroup T is Sylow in that normalizer. If
I/O₂(I) is centerless with odd outer automorphism group, the local Borel
of I normalizes this intersection. For t outside the component normalizer,
the product b(tbt⁻¹) then normalizes all of T: the two factors commute
modulo O₂(G), and t has square in the intersection.

A specified quotient of a subgroup containing both components retains the
original component projection. If its restriction to I is onto a centerless
group with kernel O₂(I), it kills the other component. Thus the diagonal
product retains precisely the requested quotient value. This proves the
normalizer-lifting step without replacing the original quotient map or
assuming that T fixes I.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
11.5.6(3), printed pp.780--781 (the two-component Borel normalizer).
-/

public noncomputable section

open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The diagonal product of a pair exchanged modulo an index-two subgroup
normalizes the entire extension. -/
theorem diagonal_mem_normalizer_of_index_two
    (T S : Subgroup G) (hST : S ≤ T) (hi : (S.subgroupOf T).index = 2)
    {t b : G} (ht : t ∈ T) (htS : t ∉ S)
    (hb : b ∈ normalizer (S : Set G))
    (hc : ⁅b, t * b * t⁻¹⁆ ∈ S) :
    b * (t * b * t⁻¹) ∈ normalizer (T : Set G) := by
  let : (S.subgroupOf T).Normal := (S.subgroupOf T).normal_of_index_eq_two hi
  have hTS : T ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST).mp inferInstance
  let N := normalizer (S : Set G)
  let S₀ := S.subgroupOf N
  let : S₀.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let q := QuotientGroup.mk' S₀
  let t₀ : N := ⟨t, hTS ht⟩
  let b₀ : N := ⟨b, hb⟩
  have ht2 : q t₀ * q t₀ = 1 := by
    rw [← map_mul]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact (S.subgroupOf T).mul_self_mem_of_index_two hi ⟨t, ht⟩
  have hcom : Commute (q b₀) (q (t₀ * b₀ * t₀⁻¹)) := by
    rw [← commutatorElement_eq_one_iff_commute]
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr hc
  have he : Commute (q (b₀ * (t₀ * b₀ * t₀⁻¹))) (q t₀) := by
    have htinv : (q t₀)⁻¹ = q t₀ := inv_eq_of_mul_eq_one_left ht2
    have hc' := hcom.eq
    simp only [map_mul, map_inv, htinv] at hc' ⊢
    change _ * _ = _ * _
    calc
      _ = q b₀ * (q t₀ * q b₀) := by simp only [mul_assoc, ht2, mul_one]
      _ = q t₀ * q b₀ * q t₀ * q b₀ * q t₀ := by
        have hh := congrArg (fun z => z * q t₀) hc'
        simpa only [mul_assoc, ht2, mul_one] using hh
      _ = _ := by simp only [mul_assoc]
  let d : N := b₀ * (t₀ * b₀ * t₀⁻¹)
  have hd : d.val * t * d.val⁻¹ * t⁻¹ ∈ S := by
    change ⁅d,t₀⁆ ∈ S₀
    apply (QuotientGroup.eq_one_iff _).mp
    change q ⁅d,t₀⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr he.eq
  change d.val ∈ normalizer (T : Set G)
  apply mem_normalizer_fintype
  intro x hx
  by_cases hxS : x ∈ S
  · exact hST ((mem_normalizer_iff.mp d.property x).mp hxS)
  · have hxt : x * t⁻¹ ∈ S := by
      apply ((S.subgroupOf T).mul_mem_iff_of_index_two hi
        (a := (⟨x,hx⟩ : T)) (b := (⟨t,ht⟩ : T)⁻¹)).mpr
      change x ∈ S ↔ t⁻¹ ∈ S
      simp only [S.inv_mem_iff, hxS, htS]
    have hdt : d.val * t * d.val⁻¹ ∈ T := by
      have := T.mul_mem (hST hd) ht
      simpa only [inv_mul_cancel_right] using this
    change d.val * x * d.val⁻¹ ∈ T
    have heq : d.val * x * d.val⁻¹ =
        (d.val * (x * t⁻¹) * d.val⁻¹) * (d.val * t * d.val⁻¹) := by group
    rw [heq]
    exact T.mul_mem (hST ((mem_normalizer_iff.mp d.property (x * t⁻¹)).mp hxt)) hdt
end Subgroup

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- In an index-two component normalizer, the local Borel normalizes the
intersection of the original Sylow subgroup with that normalizer. -/
theorem local_borel_normalizes_sylow_normalizer_intersection
    (T : Sylow 2 G) (I : Subgroup G)
    (hi : (normalizer (I : Set G)).index = 2)
    (hz : center (I ⧸ pCore 2 I) = ⊥)
    (ho : Nat.Coprime 2 (Nat.card (MulAut.Outer (I ⧸ pCore 2 I)))) :
    I ⊓ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G) ≤
      normalizer (((T : Subgroup G) ⊓ normalizer (I : Set G) : Subgroup G) : Set G) := by
  let N := normalizer (I : Set G)
  let : N.Normal := N.normal_of_index_eq_two hi
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal N
  let J := I.subgroupOf N
  let e : J ≃* I := subgroupOfEquivOfLe I.le_normalizer
  let eQ : (J ⧸ pCore 2 J) ≃* (I ⧸ pCore 2 I) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hzJ : center (J ⧸ pCore 2 J) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh : eQ x ∈ center (I ⧸ pCore 2 I) := (centerCongr eQ ⟨x,hx⟩).property
    rw [hz,mem_bot] at hh
    exact eQ.injective (hh.trans eQ.map_one.symm)
  have hoJ : Nat.Coprime 2 (Nat.card (MulAut.Outer (J ⧸ pCore 2 J))) := by
    rw [Nat.card_congr (MulAut.outerCongr eQ).toEquiv]
    exact ho
  have hNJ : (⊤ : Subgroup N) ≤ normalizer (J : Set N) := by
    rw [← subgroupOf_normalizer_eq I.le_normalizer]
    intro x _
    exact x.property
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow S J (le_top.trans hNJ)
  have hb := sylow_normalizer_le_of_coprime_outer S J (le_top.trans hNJ) hzJ hoJ P hP
  have hSN : (S : Subgroup N).map N.subtype = (T : Subgroup G) ⊓ N := by
    rw [hS]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨hy,y.property⟩
    · rintro ⟨hx,hn⟩
      exact ⟨⟨x,hn⟩,hx,rfl⟩
  intro b hbI
  have hbN : b ∈ N := I.le_normalizer hbI.1
  have hbJ : (⟨b,hbN⟩ : N) ∈ J := hbI.1
  have hbP : (⟨⟨b,hbN⟩,hbJ⟩ : J) ∈ normalizer (P : Set J) := by
    change (⟨⟨b,hbN⟩,hbJ⟩ : J) ∈ normalizer ((P : Subgroup J) : Set J)
    rw [hP,hS]
    apply mem_normalizer_iff.mpr
    intro j
    change (j : G) ∈ (T : Subgroup G) ↔ b * (j : G) * b⁻¹ ∈ (T : Subgroup G)
    have hh := mem_normalizer_iff.mp hbI.2 (j : G)
    have hjI : (j : G) ∈ I := j.property
    have hbjI : b * (j : G) * b⁻¹ ∈ I :=
      (mem_normalizer_iff.mp hbN (j : G)).mp hjI
    simpa only [mem_inf, hjI, hbjI, and_true] using hh
  have hnS := hb (mem_map_of_mem J.subtype hbP)
  have hn := (S : Subgroup N).le_normalizer_map N.subtype (mem_map_of_mem N.subtype hnS)
  rwa [hSN] at hn
end Subgroup
namespace Subgroup
open Theory.GroupTheory
open scoped commutatorElement Pointwise
variable {G Q : Type*} [Group G] [Finite G] [Group Q]

private theorem pair_commutes_mod_core
    {I : Subgroup G} (hI : I.IsCComponent)
    [IsQuasisimple (I ⧸ pCore 2 I)] (t : G) (ht : t ∉ normalizer (I : Set G)) :
    ⁅I.map (QuotientGroup.mk' (pCore 2 G)),
      (I.map (QuotientGroup.mk' (pCore 2 G))).conjBy (QuotientGroup.mk' (pCore 2 G) t)⁆ = ⊥ := by
  let _ := pCore_isNilpotent (p := 2) (G := G)
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := I.map q
  let e := cComponentTwoCoreQuotientEquiv hI
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e
  have hc : IsComponent (G ⧸ pCore 2 G) B := ⟨(hI.map_quotient _).subnormal,inferInstance⟩
  exact hc.commutator_eq_bot_of_ne (hc.map_conj (q t)) (fun he => ht (by
    have hh : q t ∈ normalizer (B : Set (G ⧸ pCore 2 G)) :=
      mem_normalizer_iff_map_conj_eq.mpr he.symm
    have hp : t ∈ (normalizer (I.map q)).comap q := hh
    rwa [normalizer_cComponent_quotient hI (pCore 2 G)] at hp))

/-- Diagonal lifts through a specified component projection. -/
theorem exists_diagonal_sylow_normalizer_lift
    (T : Sylow 2 G) (I : Subgroup G) (hI : I.IsCComponent)
    [IsQuasisimple (I ⧸ pCore 2 I)]
    (hi : (normalizer (I : Set G)).index = 2)
    (hz : center (I ⧸ pCore 2 I) = ⊥)
    (ho : Nat.Coprime 2 (Nat.card (MulAut.Outer (I ⧸ pCore 2 I))))
    (t : G) (ht : t ∈ T) (htI : t ∉ normalizer (I : Set G))
    (J : Subgroup G) (hIJ : I ≤ J) (hItJ : I.conjBy t ≤ J)
    (f : J →* Q) (hzQ : center Q = ⊥)
    (hf : Function.Surjective (f.comp (inclusion hIJ)))
    (hk : (f.comp (inclusion hIJ)).ker = pCore 2 I)
    (P : Sylow 2 I) (hP : (P : Subgroup I) = (T : Subgroup G).subgroupOf I)
    (y : Q) (hy : y ∈ normalizer (P.map (f.comp (inclusion hIJ)) : Set Q)) :
    ∃ d : J, (d : G) ∈ normalizer (T : Set G) ∧ f d = y := by
  let N := normalizer (I : Set G)
  let : N.Normal := N.normal_of_index_eq_two hi
  let S := (T : Subgroup G) ⊓ N
  have hsi : (S.subgroupOf T).index = 2 := by
    have hd : (N.subgroupOf T).index ∣ 2 := by
      simpa only [N,hi,relIndex] using N.relIndex_dvd_index_of_normal T
    have hn : (N.subgroupOf T).index ≠ 1 := by
      intro he
      have hh : (⟨t,ht⟩ : T) ∈ N.subgroupOf T := by rw [index_eq_one.mp he]; trivial
      exact htI hh
    have he := (Nat.prime_two.eq_one_or_self_of_dvd _ hd).resolve_left hn
    simpa only [S, inf_subgroupOf_left] using he
  let _ := pCore_isNilpotent (p := 2) (G := G)
  have hcoreN : pCore 2 G ≤ N := by
    rw [show N = normalizer (I : Set G) from rfl,
      ← normalizer_cComponent_quotient hI (pCore 2 G)]
    intro x hx
    change QuotientGroup.mk' (pCore 2 G) x ∈
      normalizer (I.map (QuotientGroup.mk' (pCore 2 G)) : Set (G ⧸ pCore 2 G))
    have hxq : QuotientGroup.mk' (pCore 2 G) x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
    rw [hxq]
    exact one_mem _
  have hcoreS : pCore 2 G ≤ S := le_inf (pCore_isPGroup.le_sylow_of_normal T) hcoreN
  have hcomm : ⁅I,I.conjBy t⁆ ≤ I.pCoreIn 2 := by
    have hc := pair_commutes_mod_core hI t htI
    have he : (I.conjBy t).map (QuotientGroup.mk' (pCore 2 G)) =
        (I.map (QuotientGroup.mk' (pCore 2 G))).conjBy
          (QuotientGroup.mk' (pCore 2 G) t) := by
      change (I.map (MulAut.conj t).toMonoidHom).map (QuotientGroup.mk' (pCore 2 G)) =
        (I.map (QuotientGroup.mk' (pCore 2 G))).map
          (MulAut.conj (QuotientGroup.mk' (pCore 2 G) t)).toMonoidHom
      rw [map_map, map_map]
      congr 1
    rw [← he] at hc
    exact (cComponent_commutator_le_twoCores_of_quotient_commutes hI
      (hI.map_equiv (MulAut.conj t)) hc).1.trans inf_le_left
  have he := P.normalizer_map_surjective (f.comp (inclusion hIJ)) hf
  obtain ⟨b,hb,hby⟩ := he.symm ▸ hy
  have hblocal : (b : G) ∈ I ⊓
      normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G) := by
    refine ⟨b.property, ?_⟩
    have hh := (P : Subgroup I).le_normalizer_map I.subtype (mem_map_of_mem I.subtype hb)
    rwa [hP, subgroupOf_map_subtype] at hh
  have hbS : (b : G) ∈ normalizer (S : Set G) :=
    local_borel_normalizes_sylow_normalizer_intersection T I hi hz ho hblocal
  have hbt : t * (b : G) * t⁻¹ ∈ I.conjBy t := ⟨b,b.property,rfl⟩
  have hbc := hcomm (commutator_mem_commutator b.property hbt)
  have hbcS : ⁅(b : G), t * (b : G) * t⁻¹⁆ ∈ S :=
    hcoreS (pCoreIn_le_of_subnormal 2 hI.subnormal hbc)
  let b₁ : J := inclusion hIJ b
  let b₂ : J := ⟨t * (b : G) * t⁻¹,hItJ hbt⟩
  have hb₂ : f b₂ = 1 := by
    have hh : f b₂ ∈ center Q := by
      apply mem_center_iff.mpr
      intro z
      obtain ⟨a,rfl⟩ := hf z
      have hc := hcomm (commutator_mem_commutator a.property hbt)
      obtain ⟨c,hc,r⟩ := hc
      have hc' : (f.comp (inclusion hIJ)) c = 1 := by
        apply MonoidHom.mem_ker.mp
        rwa [hk]
      have he : inclusion hIJ c = ⁅inclusion hIJ a,b₂⁆ := Subtype.ext r
      rw [MonoidHom.comp_apply, he, map_commutatorElement] at hc'
      exact commutatorElement_eq_one_iff_mul_comm.mp hc'
    rw [hzQ,mem_bot] at hh
    exact hh
  refine ⟨b₁*b₂, ?_, ?_⟩
  · change (b : G) * (t * (b : G) * t⁻¹) ∈ normalizer (T : Set G)
    exact diagonal_mem_normalizer_of_index_two (T : Subgroup G) S inf_le_left hsi
      (t := t) (b := (b : G)) ht
      (fun h => htI h.2) hbS hbcS
  · rw [map_mul,hb₂,mul_one]
    exact hby
end Subgroup