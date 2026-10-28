module
public import Theory.SpecificGroups.PSL3Four.CentralCover.SylowFixedInnerFrattini
public import Theory.SpecificGroups.PSL3.CubicComponentAction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCoprimeRankNormal
public import Theory.SpecificGroups.PSL3Even.ThompsonCentralCover
public import Theory.SpecificGroups.PSL3Four.CentralCover.ElementaryParabolic.Lifting
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentActionSource
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree.NormalImage
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.MarkedCentralizers
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.SylowSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.Overcomponents.CentralQuotient
public import Theory.SpecificGroups.PSL3Even.CubicFourNormalizer

/-!
# Excluding the exceptional PSL₃(4) cover in the paired cubic source

The original centralizer has three-rank at most two. The component's
central two-quotient has three-rank two, so distinct component conjugates
would violate that bound; hence the component is normal. Its marked inner
involution fixes a full Sylow subgroup, forcing an elementary center.
The exceptional-cover involution-lifting theorem and the elementary
Thompson calculation then put its Sylow intersection in the original R.

The two actual cubic four-groups act faithfully after taking the central
quotient. Both images are inner, and the component Sylow normalizes the
first. Their pullbacks under conjugation are normal-four geometry inside
one Sylow subgroup of PSL₃(4), forcing them to commute. Faithfulness returns
this to the source's noncommuting pair, a contradiction.

The only additional source equality used by the marked endpoint is
R = J(T); the original-source wrapper derives it from the earlier paired
cubic Sylow theorem. Neither component absorption nor a restriction on the
size of the elementary center is assumed.

Source: Aschbacher–Smith, inspection before 2.4.32, printed p.547, using
I.2.2(3), printed pp.409–410.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open Matrix.PSL3Four Matrix.PSL3Even.ThompsonCentralCover
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

private theorem inner_four_centralizes
    (P : Sylow 2 PSL) (R A B : Subgroup (MulAut PSL))
    (hR : IsPGroup 2 R) (hPR : (P : Subgroup PSL).map MulAut.conj ≤ R)
    (hA : Nat.card A = 4) (hAR : A ≤ R) (hBR : B ≤ R)
    (hiA : A ≤ MulAut.innerSubgroup PSL) (hiB : B ≤ MulAut.innerSubgroup PSL)
    (hPN : (P : Subgroup PSL).map MulAut.conj ≤ normalizer (A : Set (MulAut PSL))) :
    A ≤ centralizer (B : Set (MulAut PSL)) := by
  have hz : center PSL = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot SL
  have hconj := MulAut.conj_injective_of_center_eq_bot hz
  let A' := A.comap (MulAut.conj : PSL →* MulAut PSL)
  let B' := B.comap (MulAut.conj : PSL →* MulAut PSL)
  have hmapA : A'.map MulAut.conj = A := map_comap_eq_self hiA
  have hmapB : B'.map MulAut.conj = B := map_comap_eq_self hiB
  have hcard : Nat.card A' = 4 := by
    rw [←card_map_of_injective (f:=(MulAut.conj : PSL →* MulAut PSL)) hconj,hmapA,hA]
  have hAP : A' ≤ (P : Subgroup PSL) := fun a ha =>
    MulAut.inner_mem_image_sylow hz P R hR hPR (hAR ha)
  have hBP : B' ≤ (P : Subgroup PSL) := fun b hb =>
    MulAut.inner_mem_image_sylow hz P R hR hPR (hBR hb)
  have hPA : (P : Subgroup PSL) ≤ normalizer (A' : Set PSL) :=
    (map_le_iff_le_comap.mp hPN).trans (le_normalizer_comap _)
  have hc : A' ≤ centralizer (B' : Set PSL) := by
    by_contra hn
    have he := Matrix.PSL3Even.CubicFourNormalizer.field_card_two_of_sylow_normal_four_not_centralize
      F (n:=2) (by decide) (by simpa using card_F) P A' B' hcard hAP hBP hPA hn
    have hh := card_F
    omega
  intro a ha b hb
  obtain ⟨a',ha',rfl⟩ := hmapA.symm ▸ ha
  obtain ⟨b',hb',rfl⟩ := hmapB.symm ▸ hb
  simpa only [map_mul] using congrArg (MulAut.conj : PSL →* MulAut PSL) (hc ha' b' hb')

/-- The literal mark forces normality and an elementary component center. -/
theorem SourceCentralizerGeometry.linear_four_cover_structure
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (hinner : α ∈ (MulAut.conj : K →* MulAut K).range)
    (hZ : IsPGroup 2 (center K)) (e : K ⧸ center K ≃* PSL) :
    K.Normal ∧ frattini (center K) = ⊥ := by
  let H := involutionCentralizer g.z₂
  let : IsQuasisimple K := hK.2
  have hr : primeRank 3 H ≤ 2 :=
    (hG.twoLocal_sqtk (isTwoLocal_involution_centralizer g.order_second)).stronglyQuasithin
      3 Nat.prime_three (by decide)
  have hKrank := Matrix.PSL3.CubicComponentAction.component_rank hZ
    (n:=2) (by simpa using card_F) (by decide) e
  have hcop : Nat.Coprime 3 (Nat.card (center K)) := by
    obtain ⟨m,hm⟩ := hZ.exists_card_eq
    rw [hm]
    exact (by decide : Nat.Coprime 3 2).pow_right m
  have hnormal : K.Normal := hK.normal_of_coprime_center_primeRank 3 hcop (by
    change primeRank 3 H < 2 * primeRank 3 K
    omega)
  obtain ⟨_,β,P,hβ,hmark,_⟩ := h.component_inputs K hK
  have hab : α=β := by
    apply MulEquiv.ext
    intro k
    exact Subtype.ext (Subtype.ext ((hα k).trans (hβ k).symm))
  refine ⟨hnormal,inner_fixed_sylow_center_frattini e hZ P α
    (hab.symm ▸ hmark.order_two) hinner ?_⟩
  exact hab.symm ▸ hmark.fixes

/-- The original component Sylow intersection lies in the actual Thompson subgroup. -/
theorem SourceCentralizerGeometry.linear_four_cover_sylow_le_sourceR
    (g : SourceCentralizerGeometry c)
    (hRT : sourceR d = Stellmacher.elementaryAbelianMaxJ (T : Subgroup G))
    (K : Subgroup (involutionCentralizer g.z₂)) [K.Normal] [Group.IsPerfect K]
    (hZ : IsPGroup 2 (center K)) (e : K ⧸ center K ≃* PSL)
    (hphi : frattini (center K) = ⊥) :
    ((g.P₂ : Subgroup (involutionCentralizer g.z₂)) ⊓ K).map
      (involutionCentralizer g.z₂).subtype ≤ sourceR d := by
  let H := involutionCentralizer g.z₂
  let : Fact (IsPGroup 2 (center K)) := ⟨hZ⟩
  let : IsElementaryAbelian 2 (center K) :=
    (frattini_eq_bot_iff_isElementaryAbelian (p:=2)).mp hphi
  have hlift (W : Subgroup PSL) (hW : IsElementaryAbelian 2 W) :
      IsElementaryAbelian 2 (W.comap (projection K e)) := by
    let := hW
    apply ElementaryParabolic.elementary_comap (projection K e) (projection_surjective K e)
      ((projection_ker K e).le)
    · intro z hz
      rw [projection_ker] at hz
      exact elemPow_eq_one_of_isElementaryAbelian z hz
  have hle := sylow_component_le_thompson K e hZ hlift
    (n:=2) (by decide) (by simpa using card_F) g.P₂
  have hJT : Stellmacher.elementaryAbelianMaxJ
      ((g.P₂ : Subgroup H).map H.subtype) = sourceR d := by
    rw [hRT]
    apply Stellmacher.elementaryAbelianMaxJ_eq_of_intermediate_finite
    · rw [←hRT,g.second_span]
      exact le_sup_left
    · rw [g.second_intersection]
      exact inf_le_left
  have hm := map_mono (f:=H.subtype) hle
  rwa [←Stellmacher.elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hJT] at hm

/-- The literal faithful quotient action excludes the native exceptional cover. -/
theorem SourceCentralizerGeometry.linear_four_cover_action_false
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (hRT : sourceR d = Stellmacher.elementaryAbelianMaxJ (T : Subgroup G))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (hinner : α ∈ (MulAut.conj : K →* MulAut K).range)
    (hZ : IsPGroup 2 (center K)) (e : K ⧸ center K ≃* PSL) : False := by
  let H := involutionCentralizer g.z₂
  let L := d.block.map d.H.subtype
  let : IsQuasisimple K := hK.2
  obtain ⟨hn,hphi⟩ := g.linear_four_cover_structure hG h K hK α hα hinner hZ e
  let : K.Normal := hn
  let φ₀ : H →* MulAut K := MulAut.conjNormal
  let φ : H →* MulAut PSL := (MulAut.centralQuotientAction e).comp φ₀
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
  have hai : f a ∈ MulAut.innerSubgroup PSL := by
    obtain ⟨k,hk⟩ := hinner
    refine ⟨e (QuotientGroup.mk' (center K) k),?_⟩
    rw [hfa,←hk,MulAut.centralQuotientAction_conj]
  have hiu := c.cubic_first.module_image_le_normal_of_nontrivial
    f (MulAut.innerSubgroup PSL) a ha hna hai
  have hiv := c.cubic_first.module_image_le_normal_of_nontrivial
    fx (MulAut.innerSubgroup PSL) a ha hna
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
  let q := projection K e
  let P := Q.mapSurjective (f:=q) (projection_surjective K e)
  let R := (g.P₂ : Subgroup H).map φ
  have hφK (k:K) : φ k=MulAut.conj (q k) := by
    have hk : φ₀ (k:H)=MulAut.conj k := by ext y; rfl
    change MulAut.centralQuotientAction e (φ₀ (k:H))=_
    rw [hk,MulAut.centralQuotientAction_conj,projection_apply]
  have hPR : (P : Subgroup PSL).map MulAut.conj ≤ R := by
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
  have hQN : (P : Subgroup PSL).map MulAut.conj ≤
      normalizer ((blockU L).map f : Set (MulAut PSL)) := by
    rintro _ ⟨s,⟨k,hk,rfl⟩,rfl⟩
    rw [←hφK]
    have hkP : (k:H)∈g.P₂ := by
      rw [hQ] at hk
      exact hk
    have hkR : (k:G) ∈ sourceR d :=
      g.linear_four_cover_sylow_le_sourceR hRT K hZ e hphi
        (mem_map_of_mem H.subtype ⟨hkP,k.property⟩)
    have hkL : (k:G)∈normalizer (L:Set G) :=
      c.first.normalizes (by change (k:G)∈ChapterB.baumann _; rwa [c.baumann])
    have hkU : (k:G)∈normalizer (c.U₁:Set G) :=
      (normalizer_le_normalizer_characteristic_image L (blockU L)) hkL
    have hnj : (k:H)∈normalizer ((blockU L).map j : Set H) := by
      apply mem_normalizer_iff.mpr
      intro y
      have hmem (v:H) : v∈(blockU L).map j ↔ (v:G)∈c.U₁ := by
        constructor
        · rintro ⟨u,hu,rfl⟩
          exact mem_map_of_mem L.subtype hu
        · rintro ⟨u,hu,heu⟩
          exact ⟨u,hu,Subtype.ext heu⟩
      rw [hmem,hmem]
      exact mem_normalizer_iff.mp hkU y
    have hm := ((blockU L).map j).le_normalizer_map φ (mem_map_of_mem φ hnj)
    simpa only [map_map] using hm
  have hc := inner_four_centralizes P R ((blockU L).map f) ((blockU L).map fx)
    (g.P₂.isPGroup'.map φ) hPR
    (by rw [card_map_of_injective hf,hcardU]) hAR hBR hiu hiv hQN
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

/-- The actual exceptional central-cover row of the paired cubic inspection. -/
theorem SourceCentralizerGeometry.linear_three_four_cover_false
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (hRT : sourceR d = Stellmacher.elementaryAbelianMaxJ (T : Subgroup G))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (hinner : α ∈ (MulAut.conj : K →* MulAut K).range)
    (hcenter : center K = pCore 2 K)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) : False := by
  let : IsQuasisimple K := hK.2
  obtain ⟨_,⟨e⟩⟩ := ComponentRefinement.center_and_native_quotient_of_psl_four hmodel
  have hZ : IsPGroup 2 (center K) := hcenter.symm ▸ pCore_isPGroup
  exact g.linear_four_cover_action_false hG h hRT K hK α hα hinner hZ e

/-- The earlier original source geometry supplies the Thompson equality. -/
theorem SourceCentralizerGeometry.linear_three_four_cover_from_original
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (hinner : α ∈ (MulAut.conj : K →* MulAut K).range)
    (hcenter : center K = pCore 2 K)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) : False := by
  have hRT : sourceR d = Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) :=
    (d.paired_cubic_source_sylow_geometry hG T hM hTM hu hST hpair c.cubic_first).2.2.2.2.1
  exact g.linear_three_four_cover_false hG (g.lemma115 hG hM hTM hu).2 hRT
    K hK α hα hinner hcenter hmodel

end CFSG.Quasithin.Chapter2.DoubleA3



