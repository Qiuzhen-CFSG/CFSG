module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionCentralizer
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionCentralizerThree
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.Models
public import Theory.SpecificGroups.Classical.BinaryLinearThreeRank
public import Theory.SpecificGroups.Symplectic.FundamentalPlane.ThreeRank
public import Theory.SpecificGroups.PSL3.SplitPrimeRank
public import Theory.NumberTheory.BinaryTorusParity
public import Theory.GroupTheory.CyclicSubgroupNormalizer
public import Theory.Alternating.PrimeRank

/-!
# The linear-three model in the chosen-seed centralizer argument

A characteristic seed-action kernel also centralizes the whole normalizer
orbit. Consequently the original component image on that orbit acts on the
seed through the same marked group and linear coordinates. Among the actual
D.3.10 constituent models, three-rank at most one leaves exactly the natural
SL₃ model over a binary field of odd degree; its central cover is retained.

An explicit inverted subgroup of order three in SL₃ and the prequotient
rank-two bound give three-rank at most one in the component centralizer.
Its three-core is therefore cyclic, so each subgroup of that core is normal
in the full action image. The actual chosen-module transports and use in the
three-core exclusion are in `SeedAlternativesMovedExhaustionThreeModels`.

Source: Aschbacher--Smith, D.3.14--15, printed p.202, in the proof of D.3.10
and the application to3.2.5, printed pp.201--204 and580.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325

/-- Three-rank one leaves precisely the odd-degree linear-three natural model. -/
theorem constituentModel_linearThree_of_three_rank_le_one {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (hm : ConstituentModel ρ)
    (hr : primeRank 3 A ≤ 1) :
    ∃ F : BinaryField, Odd F.degree ∧ Nonempty (ActionEquiv ρ (linearNatural F 3)) := by
  rcases hm with hm | hm | hm | hm | hm
  · obtain ⟨F, ⟨e⟩⟩ := hm
    have hF : primeRank 3 SL(3,F.Carrier) ≤ 1 := by
      rwa [← primeRank_congr 3 e.groupEquiv]
    refine ⟨F, ?_, ⟨e⟩⟩
    apply Nat.not_even_iff_odd.mp
    intro he
    have hd : 3 ∣ Nat.card F.Carrier - 1 := by
      rw [F.card_eq]
      exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff F.degree).mpr he
    have hh := Matrix.PSL3.SplitPrimeRank.special_rank F.Carrier hd
    omega
  · obtain ⟨F, _, ⟨e⟩⟩ := hm
    have hlo := Theory.SpecificGroups.Symplectic.FundamentalPlane.ThreeRank.rank_le_primeRank
      (F := F.Carrier) (k := 2)
    have hhi : primeRank 3 (Matrix.symplecticGroup (Fin 2) F.Carrier) ≤ 1 := by
      rwa [← primeRank_congr 3 e.groupEquiv]
    omega
  · obtain ⟨e⟩ := hm
    have hhi : primeRank 3 (alternatingGroup (Fin 6)) ≤ 1 := by
      rwa [← primeRank_congr 3 e.groupEquiv]
    rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 (by decide) (by decide)] at hhi
    norm_num at hhi
  · obtain ⟨n, hn, ⟨e⟩⟩ := hm
    have hlo := Theory.SpecificGroups.Classical.BinaryLinearThreeRank.two_le_primeRank
      (d := n) (by omega)
    have hhi : primeRank 3 SL(n,ZMod 2) ≤ 1 := by
      change primeRank 3 SL(n,BinaryField.two.Carrier) ≤ 1
      rwa [← primeRank_congr 3 e.groupEquiv]
    omega
  · obtain ⟨σ, _, ⟨e⟩⟩ := hm
    have hhi : primeRank 3 (alternatingGroup (Fin 7)) ≤ 1 := by
      rwa [← primeRank_congr 3 e.groupEquiv]
    rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 7 3 (by decide) (by decide)] at hhi
    norm_num at hhi


end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

open CFSG.Quasithin.ChapterD
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {G P E : Type*} [Group G] [Group P] [AddCommGroup E] [Module (ZMod 2) E]

/-- The kernel of faithful model coordinates is the literal seed centralizer inside L. -/
theorem ConjugationCoordinates.kernel_eq_centralizer
    {L V : Subgroup G} {τ : Representation (ZMod 2) P E} {f : L →* P}
    (c : ConjugationCoordinates L V τ f) (hτ : Function.Injective τ) :
    f.ker = (centralizer (V : Set G)).subgroupOf L := by
  ext l
  constructor
  · intro hl v hv
    let v' : V := ⟨v,hv⟩
    let w : V := ⟨l.val * v * l.val⁻¹,
      (mem_normalizer_iff.mp (c.normalizes l.property) v).mp hv⟩
    have he := c.intertwines l v' w rfl
    rw [show f l = 1 from hl,map_one] at he
    have hw : w = v' := c.equiv.injective (Multiplicative.toAdd.injective he)
    have he' := congrArg Subtype.val hw
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  · intro hl
    apply hτ
    rw [map_one]
    ext x
    obtain ⟨v,hv⟩ := c.equiv.surjective (Multiplicative.ofAdd x)
    have he : (v : G) = (l : G) * (v : G) * (l : G)⁻¹ := by
      have hh : (v : G) * (l : G) = (l : G) * (v : G) := hl v v.property
      rw [← hh,mul_inv_cancel_right]
    have hh := c.intertwines l v v he
    rw [hv] at hh
    exact hh.symm

/-- A characteristic seed centralizer centralizes every normalizer conjugate of the seed. -/
theorem centralizer_normalizerOrbit_eq_of_characteristic
    (L V : Subgroup G)
    [((centralizer (V : Set G)).subgroupOf L).Characteristic] :
    (centralizer (componentOrbit V (normalizer (L : Set G)) : Set G)).subgroupOf L =
      (centralizer (V : Set G)).subgroupOf L := by
  let C := (centralizer (V : Set G)).subgroupOf L
  let B := C.map L.subtype
  have hBC : B ≤ centralizer (V : Set G) := by
    rintro _ ⟨l,hl,rfl⟩
    exact hl
  have hn : normalizer (L : Set G) ≤ normalizer (B : Set G) :=
    normalizer_le_normalizer_characteristic_image L C
  have hU : componentOrbit V (normalizer (L : Set G)) ≤ centralizer (B : Set G) :=
    iSup_conjugates_le_of_le_normalizer V _ _ (le_centralizer_iff.mp hBC)
      (hn.trans (normalizer_le_normalizer_centralizer B))
  apply le_antisymm
  · exact subgroupOf_mono L (centralizer_le (le_componentOrbit V _))
  · intro l hl
    exact le_centralizer_iff.mp hU (mem_map_of_mem L.subtype hl)

/-- Identify the original component image on the normalizer orbit with the faithful seed model, retaining the original map from L. -/
theorem internal_component_equiv_of_characteristic_kernel
    {L V : Subgroup G} {τ : Representation (ZMod 2) P E} {f : L →* P}
    (c : ConjugationCoordinates L V τ f) (hτ : Function.Injective τ)
    (hf : Function.Surjective f) [f.ker.Characteristic] :
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let j := internalHom M U hn
    ∃ e : ((L.subgroupOf M).map j) ≃* P,
      ∀ l : L, e ((j.subgroupMap (L.subgroupOf M))
        ((subgroupOfEquivOfLe L.le_normalizer).symm l)) = f l := by
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let j := internalHom M U hn
  let N := L.subgroupOf M
  let K := N.map j
  let g : L →* K := (j.subgroupMap N).comp
    (subgroupOfEquivOfLe L.le_normalizer).symm.toMonoidHom
  have hg : Function.Surjective g := (j.subgroupMap_surjective N).comp
    (subgroupOfEquivOfLe L.le_normalizer).symm.surjective
  have hk : g.ker = f.ker := by
    have hcf := c.kernel_eq_centralizer hτ
    let : ((centralizer (V : Set G)).subgroupOf L).Characteristic := hcf ▸ inferInstance
    rw [hcf,← centralizer_normalizerOrbit_eq_of_characteristic L V]
    ext l
    change g l = 1 ↔ (l : G) ∈ centralizer (U : Set G)
    have he : g l = 1 ↔ j ⟨l.val,L.le_normalizer l.property⟩ = 1 :=
      Subtype.ext_iff
    rw [he]
    change (⟨l.val,L.le_normalizer l.property⟩ : M) ∈ j.ker ↔ _
    change (⟨l.val,L.le_normalizer l.property⟩ : M) ∈
      (UniqueFactor.actionHom M U hn).rangeRestrict.ker ↔ _
    rw [MonoidHom.ker_rangeRestrict,UniqueFactor.actionHom_ker]
    rfl
  let q := QuotientGroup.quotientKerEquivOfSurjective g hg
  let r := QuotientGroup.liftEquiv g.ker hf hk
  refine ⟨q.symm.trans r,?_⟩
  intro l
  change r (q.symm (g l)) = f l
  have hq : q (QuotientGroup.mk' g.ker l) = g l := rfl
  rw [←hq,q.symm_apply_apply]
  exact QuotientGroup.liftEquiv_mk g.ker hf hk l

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {G P E : Type*} [Group G] [Group P] [AddCommGroup E] [Module (ZMod 2) E]
/-- The component identification intertwines its literal action on the seed with the prescribed model action. -/
theorem internal_component_actionEquiv_of_characteristic_kernel
    {L V : Subgroup G} [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 (componentOrbit V (normalizer (L : Set G)))]
    {τ : Representation (ZMod 2) P E} {f : L →* P}
    (c : ConjugationCoordinates L V τ f) (hτ : Function.Injective τ)
    (hf : Function.Surjective f) [f.ker.Characteristic] :
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let j := internalHom M U hn
    ∃ e : ActionEquiv (internalImageSubrepresentation hn c.normalizes).toRepresentation τ,
      ∀ l : L, e.groupEquiv ((j.subgroupMap (L.subgroupOf M))
        ((subgroupOfEquivOfLe L.le_normalizer).symm l)) = f l := by
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let j := internalHom M U hn
  let N := L.subgroupOf M
  let K := N.map j
  let g : L →* K := (j.subgroupMap N).comp
    (subgroupOfEquivOfLe L.le_normalizer).symm.toMonoidHom
  have hg : Function.Surjective g := (j.subgroupMap_surjective N).comp
    (subgroupOfEquivOfLe L.le_normalizer).symm.surjective
  obtain ⟨e,he⟩ := internal_component_equiv_of_characteristic_kernel c hτ hf
  let a₀ : Additive V ≃+ E :=
    { toFun v := (c.equiv v.toMul).toAdd
      invFun v := Additive.ofMul (c.equiv.symm (Multiplicative.ofAdd v))
      left_inv v := congrArg Additive.ofMul (c.equiv.symm_apply_apply v.toMul)
      right_inv v := congrArg Multiplicative.toAdd (c.equiv.apply_symm_apply (Multiplicative.ofAdd v))
      map_add' v w := congrArg Multiplicative.toAdd (c.equiv.map_mul v.toMul w.toMul) }
  let a : Additive V ≃ₗ[ZMod 2] E := { a₀ with map_smul' := ZMod.map_smul a₀ }
  let b := (internalSectionEquiv (le_componentOrbit V M)).trans a
  refine ⟨⟨e,b,?_⟩,he⟩
  intro k v
  obtain ⟨l,rfl⟩ := hg k
  have hel : e (g l) = f l := he l
  change b ((internalImageSubrepresentation hn c.normalizes).toRepresentation (g l) v) =
    τ (e (g l)) (b v)
  rw [hel]
  exact c.intertwines l ((internalSectionEquiv (le_componentOrbit V M)) v).toMul
    ((internalSectionEquiv (le_componentOrbit V M))
      ((internalImageSubrepresentation hn c.normalizes).toRepresentation (g l) v)).toMul rfl
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325


namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {P H : Type*} [Group P] [Finite P] [Group H] [Finite H]

/-- An inverted three-subgroup in K bounds the three-rank of C(K), using the original rank-two cover. -/
theorem component_centralizer_three_rank_le_one_of_inverted_subgroup
    (f : P →* H) (hf : Function.Surjective f) (hr : primeRank 3 P ≤ 2)
    (K J : Subgroup H) (hJK : J ≤ K) (hJ : IsPGroup 3 J)
    (t : H) (htK : t ∈ K) (ht : orderOf t = 2)
    (htn : t ∈ normalizer (J : Set H)) (htc : t ∉ centralizer (J : Set H)) :
    primeRank 3 (centralizer (K : Set H)) ≤ 1 := by
  let C := centralizer (K : Set H)
  let R := (J ⊔ C) ⊔ zpowers t
  have hJR : J ≤ R := le_sup_left.trans le_sup_left
  have hCR : C ≤ R := le_sup_right.trans le_sup_left
  have htR : t ∈ R := (show zpowers t ≤ R from le_sup_right) (mem_zpowers t)
  have hRn : R ≤ normalizer (J : Set H) := sup_le
    (sup_le J.le_normalizer ((centralizer_le hJK).trans (Subgroup.centralizer_le_normalizer _)))
    (zpowers_le.mpr htn)
  let : (J.subgroupOf R).Normal := (normal_subgroupOf_iff_le_normalizer hJR).mpr hRn
  let q : R.comap f →* R := (f.comp (R.comap f).subtype).codRestrict R
    (fun x => x.property)
  have hq : Function.Surjective q := by
    intro r
    obtain ⟨p,hp⟩ := hf r.val
    exact ⟨⟨p,show f p ∈ R from hp ▸ r.property⟩,Subtype.ext hp⟩
  let s : R := ⟨t,htR⟩
  have hs : orderOf s = 2 := (orderOf_coe s).symm.trans ht
  have hsc : s ∉ centralizer (J.subgroupOf R : Set R) := by
    intro hc
    apply htc
    intro j hj
    exact congrArg Subtype.val (hc ⟨j,hJR hj⟩ hj)
  have hb := primeRank_involutionCentralizer_le_one_of_surjective_rank_le_two
    (by decide : Odd 3) q hq ((primeRank_subgroup_le 3 (R.comap f)).trans hr)
    (J.subgroupOf R) hJ.comap_subtype s hs hsc
  have hle : C.subgroupOf R ≤ centralizer ({s} : Set R) := by
    intro x hx y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact Subtype.ext (hx t htK)
  have hc := (primeRank_mono 3 hle).trans hb
  rwa [primeRank_congr 3 (subgroupOfEquivOfLe hCR)] at hc

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325


namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open scoped MatrixGroups
private def binaryCubic : SL(3,ZMod 2) :=
  ⟨!![0,1,0;1,1,0;0,0,1],by decide⟩
private def binaryInverter : SL(3,ZMod 2) :=
  ⟨!![1,1,0;0,1,0;0,0,1],by decide⟩
private theorem binaryCubic_order : orderOf binaryCubic = 3 :=
  orderOf_eq_prime (by decide : binaryCubic ^ 3 = 1) (by decide : binaryCubic ≠ 1)
private theorem binaryInverter_order : orderOf binaryInverter = 2 :=
  orderOf_eq_prime (by decide : binaryInverter ^ 2 = 1) (by decide : binaryInverter ≠ 1)
private theorem binaryInverter_inverts :
    binaryInverter * binaryCubic * binaryInverter⁻¹ = binaryCubic⁻¹ := by decide

/-- Transport an explicit binary S3 pair into the actual SL3 carrier over any binary field. -/
theorem linearThree_exists_inverted_three (F : BinaryField) :
    ∃ (J : Subgroup SL(3,F.Carrier)) (t : SL(3,F.Carrier)),
      Nat.card J = 3 ∧ orderOf t = 2 ∧
      t ∈ normalizer (J : Set _) ∧ t ∉ centralizer (J : Set _) := by
  let f : SL(3,ZMod 2) →* SL(3,F.Carrier) :=
    Matrix.SpecialLinearGroup.map (algebraMap (ZMod 2) F.Carrier)
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    ext i j
    exact (algebraMap (ZMod 2) F.Carrier).injective
      (congrArg (fun a : SL(3,F.Carrier) => a.val i j) he)
  let r := f binaryCubic
  let t := f binaryInverter
  have hr : orderOf r = 3 := (orderOf_injective f hf binaryCubic).trans binaryCubic_order
  have ht : orderOf t = 2 := (orderOf_injective f hf binaryInverter).trans binaryInverter_order
  have hi : t * r * t⁻¹ = r⁻¹ := by
    simpa only [map_mul,map_inv] using congrArg f binaryInverter_inverts
  refine ⟨zpowers r,t,by rw [Nat.card_zpowers,hr],ht,?_,?_⟩
  · rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    change zpowers (t * r * t⁻¹) = zpowers r
    rw [hi,zpowers_inv]
  · intro hc
    have he : r = r⁻¹ := by
      calc
        r = t * r * t⁻¹ := by rw [←hc r (mem_zpowers r),mul_inv_cancel_right]
        _ = r⁻¹ := hi
    have hsq : r ^ 2 = 1 := by
      rw [pow_two]
      exact (congrArg (fun x => r * x) he).trans (mul_inv_cancel r)
    have hd := orderOf_dvd_of_pow_eq_one hsq
    rw [hr] at hd
    norm_num at hd
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325


namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {P H : Type*} [Group P] [Finite P] [Group H] [Finite H]
/-- The marked SL3 model supplies the inverted subgroup needed by the centralizer rank bound. -/
theorem component_centralizer_three_rank_le_one_of_linearThree
    (f : P →* H) (hf : Function.Surjective f) (hr : primeRank 3 P ≤ 2)
    (K : Subgroup H) (F : BinaryField) (e : K ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) :
    primeRank 3 (centralizer (K : Set H)) ≤ 1 := by
  obtain ⟨J,t,hJ,ht,htn,htc⟩ := linearThree_exists_inverted_three F
  let i : Matrix.SpecialLinearGroup (Fin 3) F.Carrier →* H := K.subtype.comp e.symm.toMonoidHom
  have hi : Function.Injective i := K.subtype_injective.comp e.symm.injective
  have hJK : J.map i ≤ K := by
    rintro _ ⟨j,hj,rfl⟩
    exact (e.symm j).property
  have hJp : IsPGroup 3 (J.map i) := (IsPGroup.of_card (p := 3) (n := 1)
    (by simpa only [pow_one] using hJ)).map i
  have hn : i t ∈ normalizer (J.map i : Set H) :=
    le_normalizer_map i (mem_map_of_mem i htn)
  have hc : i t ∉ centralizer (J.map i : Set H) := by
    intro hc
    apply htc
    intro j hj
    apply hi
    simpa only [map_mul] using hc (i j) (mem_map_of_mem i hj)
  exact component_centralizer_three_rank_le_one_of_inverted_subgroup f hf hr K
    (J.map i) hJK hJp (i t) (e.symm t).property
    ((orderOf_injective i hi t).trans ht) hn hc
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H : Type*} [Group H] [Finite H]

/-- The cyclic three-core of the component centralizer has every subgroup normal in the full group. -/
theorem normal_of_le_three_core_centralizer_rank_one
    (K : Subgroup H) [K.Normal]
    (hr : primeRank 3 (centralizer (K : Set H)) ≤ 1)
    (X : Subgroup H)
    (hX : X ≤ (pCore 3 (centralizer (K : Set H))).map (centralizer (K : Set H)).subtype) :
    X.Normal := by
  let C := centralizer (K : Set H)
  let Q := (pCore 3 C).map C.subtype
  let : IsCyclic (pCore 3 C) := by
    apply IsPGroup.isCyclic_of_odd_of_elementary_card_le pCore_isPGroup (by decide : Odd 3)
    intro E hE
    let := hE
    exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one
      ((primeRank_subgroup_le 3 (pCore 3 C)).trans hr) E
  let : IsCyclic Q := isCyclic_of_surjective
    (C.subtype.subgroupMap (pCore 3 C)) (C.subtype.subgroupMap_surjective (pCore 3 C))
  have hn := normalizer_le_normalizer_of_le_cyclic X Q hX
  apply normalizer_eq_top_iff.mp
  apply top_unique
  exact (show (⊤ : Subgroup H) ≤ normalizer (Q : Set H) by rw [normalizer_eq_top]).trans hn
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
