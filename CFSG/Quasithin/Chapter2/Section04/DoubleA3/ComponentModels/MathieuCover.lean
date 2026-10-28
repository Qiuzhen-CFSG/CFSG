module
public import Theory.Mathieu.M22.Properties.FourNormalizers.LowIndex
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Ambient
public import Theory.Mathieu.M22.Properties.ThreeRank
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.GeneralizedFitting.ComponentCoprimeRankNormal
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.Mathieu
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree.NormalImage

/-!
# The binary Mathieu cover in the paired-cubic source

The original component is normal because its central quotient has three-rank two
and its center has order two. The first cubic block acts faithfully on that
quotient. Its normal four-group has normalizer index at most two in the actual
Sylow action image. The concrete Mathieu calculation then makes this four-group
commute with its marked conjugate, contradicting the original paired modules.

This supplies the binary M₂₂ exclusion in quasithin 2.4.32, retaining the literal
component, involution centralizer, and original paired-cubic markings.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open Sporadic.Mathieu M22ValueBound.Concrete

private theorem inner_low_index_commutes (P : Sylow 2 M22)
    (Q A : Subgroup (MulAut M22)) (hQ : IsPGroup 2 Q)
    (hPQ : (P : Subgroup M22).map MulAut.conj ≤ Q)
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 4)
    (hAQ : A ≤ Q) (hiA : A ≤ MulAut.innerSubgroup M22)
    (hi : (normalizer (A : Set (MulAut M22))).relIndex Q ≤ 2)
    (t : MulAut M22) (ht : t ∈ Q) :
    ∀ u ∈ A, ∀ v ∈ A, Commute u (t*v*t⁻¹) := by
  let V := A.comap (MulAut.conj : M22 →* MulAut M22)
  have hconj := MulAut.conj_injective_of_center_eq_bot m22_center_eq_bot
  have hVA : V.map MulAut.conj = A := map_comap_eq_self hiA
  let e := designAutEquiv.symm
  let R := Q.map e.toMonoidHom
  have hVE : IsElementaryAbelian 2 V := by
    let := hA
    exact IsElementaryAbelian.comap_of_injective (MulAut.conj : M22 →* MulAut M22) hconj A
  have hVc : Nat.card V = 4 := by
    rw [←card_map_of_injective (f:=(MulAut.conj : M22 →* MulAut M22)) hconj,hVA,hc]
  have hinc : e.toMonoidHom.comp (MulAut.conj : M22 →* MulAut M22) = M22ValueBound.Concrete.inclusion := by
    apply MonoidHom.ext
    intro k
    apply designAutEquiv.injective
    change designAutEquiv (e (MulAut.conj k)) = designAutEquiv (M22ValueBound.Concrete.inclusion k)
    rw [show designAutEquiv (e (MulAut.conj k))=MulAut.conj k from designAutEquiv.apply_symm_apply _,designAutEquiv_inclusion]
  have hVmap : V.map inclusion = A.map e.toMonoidHom := by
    rw [←hVA,map_map,hinc]
  have hPQ' : (P : Subgroup M22).map inclusion ≤ R := by
    rw [←hinc,←map_map]
    exact map_mono hPQ
  have hi' : (normalizer (V.map inclusion : Set m22DesignAut)).relIndex R ≤ 2 := by
    rw [hVmap,←map_equiv_normalizer_eq,show R=Q.map e.toMonoidHom from rfl,
      relIndex_map_map_of_injective _ _ e.injective]
    exact hi
  have hh := M22SmallFour.low_index_four_commutes R (hQ.map e.toMonoidHom) P hPQ'
    V (hVmap ▸ map_mono hAQ) hVE hVc hi' (e t) (mem_map_of_mem e.toMonoidHom ht)
  intro u hu v hv
  obtain ⟨u,hu,rfl⟩ := hVA.symm ▸ hu
  obtain ⟨v,hv,rfl⟩ := hVA.symm ▸ hv
  have hcuv := hh u hu v hv
  have ha : m22DesignAutToAut (e t) v=t v := by
    exact congrArg (fun a : MulAut M22 => a v) (designAutEquiv.apply_symm_apply t)
  rw [ha] at hcuv
  have he : MulAut.conj (t v) = t*MulAut.conj v*t⁻¹ := by
    apply MulEquiv.ext
    intro x
    simp only [MulAut.conj_apply,MulAut.mul_apply,MulAut.inv_apply,map_mul,map_inv,MulEquiv.apply_symm_apply]
  rw [←he]
  exact hcuv.map (MulAut.conj : M22 →* MulAut M22)

variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

theorem SourceCentralizerGeometry.binary_mathieu_action_false
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (hinner : α ∈ (MulAut.conj : K →* MulAut K).range)
    [K.Normal] (e : K ⧸ center K ≃* M22) : False := by
  let H := involutionCentralizer g.z₂
  let L := d.block.map d.H.subtype
  let : IsQuasisimple K := hK.2
  let φ₀ : H →* MulAut K := MulAut.conjNormal
  let φ : H →* MulAut M22 := (MulAut.centralQuotientAction e).comp φ₀
  have hLH : L ≤ H := g.first_block_le_second_centralizer
  let j : L →* H := inclusion hLH
  let x : H := ⟨c.x,g.x_second⟩
  let jx : L →* H := (MulAut.conj x⁻¹).toMonoidHom.comp j
  let f₀ := φ₀.comp j
  let f := φ.comp j
  let fx := φ.comp jx
  have hact (l : L) (k : K) : ((f₀ l k : H) : G) = (l:G)*(k:G)*(l:G)⁻¹ := rfl
  have hz := g.first_mem
  change g.z₁ ∈ (blockU L).map L.subtype at hz
  obtain ⟨a,ha,hea⟩ := hz
  have heG : (a:G) = g.z₁ := hea
  have hfa₀ : f₀ a = α := by
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    apply Subtype.ext
    have hkc : g.z₂*(k:G)*g.z₂⁻¹ = (k:G) := by
      rw [←mem_centralizer_singleton_iff.mp (k:H).property,mul_inv_cancel_right]
    calc
      ((f₀ a k:H):G) = g.z₁*(k:G)*g.z₁⁻¹ := by rw [hact,heG]
      _ = g.z₁*(g.z₂*(k:G)*g.z₂⁻¹)*g.z₁⁻¹ := by rw [hkc]
      _ = ((α k:H):G) := by rw [hα]; group
  have hfa : f a = MulAut.centralQuotientAction e α := congrArg (MulAut.centralQuotientAction e) hfa₀
  have hax : jx a = j a := by
    apply Subtype.ext
    change c.x⁻¹*(a:G)*(c.x⁻¹)⁻¹ = (a:G)
    rw [inv_inv,heG,mul_assoc,inv_mul_eq_iff_eq_mul]
    exact (mem_centralizer_singleton_iff.mp g.x_first).symm
  have hna : a ≠ 1 := by
    intro he
    have hh := g.order_first
    rw [←heG,he] at hh
    norm_num at hh
  have hai : f a ∈ MulAut.innerSubgroup M22 := by
    obtain ⟨k,hk⟩ := hinner
    refine ⟨e (QuotientGroup.mk' (center K) k),?_⟩
    rw [hfa,←hk,MulAut.centralQuotientAction_conj]
  have hiu := c.cubic_first.module_image_le_normal_of_nontrivial
    f (MulAut.innerSubgroup M22) a ha hna hai
  have hiv := c.cubic_first.module_image_le_normal_of_nontrivial
    fx (MulAut.innerSubgroup M22) a ha hna
      (by change φ (jx a) ∈ _; rw [hax]; exact hai)
  obtain ⟨f',hf',hact'⟩ := g.faithful_first_block_action hG h K hK
  have hf₀ : Function.Injective f₀ := by
    have he : f₀=f' := by
      ext l k
      exact (hact l k).trans (hact' l k).symm
    exact he ▸ hf'
  have hf : Function.Injective f := (MulAut.centralQuotientAction_injective e).comp hf₀
  have hcardU : Nat.card (blockU L) = 4 := by
    have hq : Nat.card (L ⧸ pCore 2 L)=3 := by
      obtain ⟨ea⟩ := c.cubic_first.2.2.quotient_iso
      rw [Nat.card_congr ea.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      rfl
    rw [←c.cubic_first.2.1.core_eq_blockU_of_quotient_three hq]
    exact c.cubic_first.2.1.core_card_four_of_quotient_three hq
  have hUR : c.U₁ ≤ sourceR d := c.baumann ▸ c.first.module_le
  have hVR : c.V₁ ≤ sourceR d := c.baumann ▸ c.first.conjugate_le (c.original.R_normal c.x_mem)
  have hRP : (sourceR d).subgroupOf H ≤ (g.P₂ : Subgroup H) := by
    intro r hr
    have hh : (r:G) ∈ (g.P₂ : Subgroup H).map H.subtype := by
      rw [g.second_span]
      exact mem_sup_left hr
    obtain ⟨s,hs,hes⟩ := hh
    exact (Subtype.ext hes : s=r) ▸ hs
  obtain ⟨Q,hQ⟩ := g.P₂.exists_subgroupOf_eq_of_normal K
  let q : K →* M22 := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let P := Q.mapSurjective (f:=q) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  let R := (g.P₂ : Subgroup H).map φ
  have hφK (k:K) : φ k=MulAut.conj (q k) := by
    have hk : φ₀ (k:H)=MulAut.conj k := by ext y; rfl
    change MulAut.centralQuotientAction e (φ₀ (k:H))=_
    rw [hk,MulAut.centralQuotientAction_conj]
    rfl
  have hPR : (P : Subgroup M22).map MulAut.conj ≤ R := by
    rintro _ ⟨s,⟨k,hk,rfl⟩,rfl⟩
    refine ⟨(k:H),?_,hφK k⟩
    rw [hQ] at hk
    exact hk
  have hAR : (blockU L).map f ≤ R := by
    rintro _ ⟨u,hu,rfl⟩
    exact ⟨j u,hRP (hUR (mem_map_of_mem L.subtype hu)),rfl⟩
  have hBR : (blockU L).map fx ≤ R := by
    rintro _ ⟨u,hu,rfl⟩
    exact ⟨jx u,hRP (hVR (mem_map_of_mem (MulAut.conj c.x⁻¹).toMonoidHom
      (mem_map_of_mem L.subtype hu))),rfl⟩
  have hRN : (sourceR d).subgroupOf H ≤ normalizer (((blockU L).map j) : Set H) := by
    intro r hr
    have hrL : (r:G) ∈ normalizer (L:Set G) :=
      c.first.normalizes (by change (r:G)∈ChapterB.baumann _; rwa [c.baumann])
    have hrU : (r:G) ∈ normalizer (c.U₁:Set G) :=
      (normalizer_le_normalizer_characteristic_image L (blockU L)) hrL
    apply mem_normalizer_iff.mpr
    intro y
    have hmem (v:H) : v∈(blockU L).map j ↔ (v:G)∈c.U₁ := by
      constructor
      · rintro ⟨u,hu,rfl⟩
        exact mem_map_of_mem L.subtype hu
      · rintro ⟨u,hu,heu⟩
        exact ⟨u,hu,Subtype.ext heu⟩
    rw [hmem,hmem]
    exact mem_normalizer_iff.mp hrU y
  have hidx : (normalizer ((blockU L).map f : Set (MulAut M22))).relIndex R ≤ 2 := by
    rw [show R=(g.P₂ : Subgroup H).map φ from rfl,←relIndex_comap]
    have hle : (sourceR d).subgroupOf H ≤
        (normalizer ((blockU L).map f : Set (MulAut M22))).comap φ := by
      intro r hr
      have hm := ((blockU L).map j).le_normalizer_map φ (mem_map_of_mem φ (hRN hr))
      change φ r ∈ normalizer ((blockU L).map f : Set (MulAut M22))
      simpa only [map_map,f] using hm
    apply (relIndex_le_of_le_left hle index_ne_zero_of_finite).trans
    have hh := relIndex_map_map_of_injective ((sourceR d).subgroupOf H)
      (g.P₂ : Subgroup H) H.subtype_injective
    have hRH : sourceR d ≤ H := fun r hr => mem_centralizer_singleton_iff.mpr (g.second_fixed r hr)
    rw [map_subgroupOf_eq_of_le hRH] at hh
    exact (hh.symm.trans g.second_index).le
  have hxP : x ∈ g.P₂ := by
    have hh : c.x ∈ (g.P₂ : Subgroup H).map H.subtype :=
      g.second_span.symm ▸ mem_sup_right (mem_zpowers c.x)
    obtain ⟨v,hv,he⟩ := hh
    exact (Subtype.ext he : v=x) ▸ hv
  have hAelem : IsElementaryAbelian 2 ((blockU L).map f) := by
    let : IsElementaryAbelian 2 (blockU L) := c.cubic_first.2.1.elementary
    exact IsElementaryAbelian.map f
  have hcc := inner_low_index_commutes P R ((blockU L).map f)
    (g.P₂.isPGroup'.map φ) hPR hAelem
    (by rw [card_map_of_injective hf,hcardU]) hAR hiu hidx
    (φ x⁻¹) (mem_map_of_mem φ ((g.P₂ : Subgroup H).inv_mem hxP))
  have hc : (blockU L).map f ≤ centralizer ((blockU L).map fx : Set (MulAut M22)) := by
    rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩
    have hh := hcc (f u) (mem_map_of_mem f hu) (f v) (mem_map_of_mem f hv)
    have he : φ x⁻¹*f v*(φ x⁻¹)⁻¹=fx v := by
      have hxv : jx v = x⁻¹*j v*x := by
        change (MulAut.conj x⁻¹) (j v)=_
        rw [MulAut.conj_apply,inv_inv]
      change φ x⁻¹*φ (j v)*(φ x⁻¹)⁻¹=φ (jx v)
      rw [hxv,map_mul,map_mul,map_inv]
      simp only [inv_inv]
    rw [he] at hh
    exact hh.symm
  apply c.noncommuting
  rintro v ⟨w,hw,rfl⟩ u hu
  obtain ⟨b,hb,rfl⟩ := hw
  obtain ⟨a',ha',rfl⟩ := hu
  have hcomm : f a' * fx b = fx b * f a' :=
    (hc (mem_map_of_mem f ha') (fx b) (mem_map_of_mem fx hb)).symm
  let v : G := (MulAut.conj c.x⁻¹) (b:G)
  have hvR : v ∈ sourceR d := hVR (mem_map_of_mem (MulAut.conj c.x⁻¹).toMonoidHom
    (mem_map_of_mem L.subtype hb))
  have hvL : v ∈ normalizer (L : Set G) :=
    c.first.normalizes (by change v ∈ ChapterB.baumann _; rwa [c.baumann])
  let y : L := ⟨v*(a':G)*v⁻¹,(mem_normalizer_iff.mp hvL _).mp a'.property⟩
  have hjy : j y = jx b * j a' * (jx b)⁻¹ := Subtype.ext rfl
  have hfy : f y = f a' := by
    change φ (j y)=_
    rw [hjy,map_mul,map_mul,map_inv]
    change fx b * f a' * (fx b)⁻¹=f a'
    rw [←hcomm,mul_inv_cancel_right]
  have hy := congrArg (fun l:L => (l:G)) (hf hfy)
  change (a':G)*v=v*(a':G)
  exact (mul_inv_eq_iff_eq_mul.mp hy).symm


/-- The binary Mathieu cover is excluded in the original paired-cubic data. -/
theorem SourceCentralizerGeometry.binary_mathieu_twentyTwo_component_false
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (_hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (_hpair : d.L0 ≠ d.block)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (hk : Nat.card (pCore 2 K) = 2) (e : (K ⧸ pCore 2 K) ≃* M22) : False := by
  let H := involutionCentralizer g.z₂
  let : IsQuasisimple K := hK.2
  let q : K →* M22 := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = pCore 2 K := by
    rw [show q=e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)) from rfl,
      MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hz : center K = pCore 2 K := by
    apply le_antisymm _ (IsQuasisimple.pCore_le_center 2)
    intro k hkc
    have hqc : q k ∈ center M22 := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨x,rfl⟩ := hq y
      exact (map_mul q x k).symm.trans ((congrArg q (mem_center_iff.mp hkc x)).trans (map_mul q k x))
    have heq : q k = 1 := by simpa only [m22_center_eq_bot,mem_bot] using hqc
    exact hqker ▸ heq
  let eZ := (QuotientGroup.quotientMulEquivOfEq hz).trans e
  have hZ : Nat.card (center K)=2 := hz ▸ hk
  have hcop : Nat.Coprime 3 (Nat.card (center K)) := by rw [hZ]; decide
  have hr : primeRank 3 H ≤ 2 :=
    (hG.twoLocal_sqtk (isTwoLocal_involution_centralizer g.order_second)).stronglyQuasithin
      3 Nat.prime_three (by decide)
  have hrK : 2 ≤ primeRank 3 K := by
    have hh := primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup
    rw [primeRank_congr 3 e,m22_primeRank_three] at hh
    exact hh
  let : K.Normal := hK.normal_of_coprime_center_primeRank 3 hcop (by
    change primeRank 3 H < 2*primeRank 3 K
    omega)
  have h := (g.lemma115 hG hM hTM hu).2
  obtain ⟨α,hα,hm⟩ := (Chapter1.lemma_1_1_5_three_knownSimple hG _ _ _ _ h K hK).2.2
  have hinner : α ∈ (MulAut.conj : K →* MulAut K).range := by
    rcases ComponentRefinement.inner_or_alternating_quotient_of_modelAction hm with hi | h6 | h7
    · exact hi
    · obtain ⟨e6⟩ := h6
      have hc := Nat.card_congr (eZ.symm.trans e6).toEquiv
      rw [m22_order,nat_card_alternatingGroup,Nat.card_fin] at hc
      norm_num [Nat.factorial] at hc
    · obtain ⟨e7⟩ := h7
      have hc := Nat.card_congr (eZ.symm.trans e7).toEquiv
      rw [m22_order,nat_card_alternatingGroup,Nat.card_fin] at hc
      norm_num [Nat.factorial] at hc
  exact g.binary_mathieu_action_false hG h K hK α hα hinner eZ

end CFSG.Quasithin.Chapter2.DoubleA3
