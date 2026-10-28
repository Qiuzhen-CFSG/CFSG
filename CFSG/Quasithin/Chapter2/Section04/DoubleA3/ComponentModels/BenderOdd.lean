module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentActionNormalizer
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree.NormalImage
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.BenderTwoKernel
public import BenderSuzuki.SE.InnerSylowInvolutions

/-!
# Bender rows in the original paired-cubic component inspection

The normal component normalizer contains both actual cubic blocks L and
L conjugated by the source element x. Their common fixed involution has a
nontrivial inner action on K, so both four-group module images are inner.
Bender Sylow involutions commute, whereas these actual four-groups do not.
Faithfulness on L carries this contradiction back to the original source
configuration; no absorption of L into K is assumed.

Source: Aschbacher–Smith 2.4.32, printed p.547.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

private theorem component_normalizer_normal
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K) :
    (normalizer (K : Set (involutionCentralizer g.z₂))).Normal := by
  let H := involutionCentralizer g.z₂
  have hsq := hG.twoLocal_sqtk (isTwoLocal_involution_centralizer g.order_second)
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_,hsq.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hK.isCComponent with hk | hi
  · let := hk
    rw [normalizer_eq_top]
    infer_instance
  · exact normal_of_index_eq_two hi

/-- The literal noncommuting four-groups exclude a center-free Bender
component whose marked first fixed involution acts by an inner automorphism. -/
theorem SourceCentralizerGeometry.bender_component_action_false
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (hinner : α ∈ (MulAut.conj : K →* MulAut K).range)
    (hzK : center K = ⊥) (hm : ClassificationModels.IsBenderModel K) : False := by
  let H := involutionCentralizer g.z₂
  let N := normalizer (K : Set H)
  let L := d.block.map d.H.subtype
  let : N.Normal := component_normalizer_normal g hG K hK
  have hLH : L ≤ H := g.first_block_le_second_centralizer
  have hLN : L.subgroupOf H ≤ N := g.first_block_normalizes_component hG K hK
  let j : L →* N := (inclusion hLN).comp (subgroupOfEquivOfLe hLH).symm.toMonoidHom
  let x : H := ⟨c.x,g.x_second⟩
  let jx : L →* N := (MulAut.conjNormal (H := N) x⁻¹).toMonoidHom.comp j
  let φ := K.normalizerMonoidHom
  let f := φ.comp j
  let fx := φ.comp jx
  have hact (l : L) (k : K) : ((f l k : H) : G) = (l:G)*(k:G)*(l:G)⁻¹ := rfl
  have hz := g.first_mem
  change g.z₁ ∈ (blockU L).map L.subtype at hz
  obtain ⟨a,ha,he⟩ := hz
  have hea : (a:G) = g.z₁ := he
  have hfa : f a = α := by
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    apply Subtype.ext
    have hkc : g.z₂*(k:G)*g.z₂⁻¹ = (k:G) := by
      rw [←mem_centralizer_singleton_iff.mp (k : H).property,mul_inv_cancel_right]
    calc
      ((f a k : H) : G) = g.z₁*(k:G)*g.z₁⁻¹ := by rw [hact,hea]
      _ = g.z₁*(g.z₂*(k:G)*g.z₂⁻¹)*g.z₁⁻¹ := by rw [hkc]
      _ = ((α k : H) : G) := by rw [hα]; group
  have hax : jx a = j a := by
    apply Subtype.ext
    apply Subtype.ext
    change c.x⁻¹*(a:G)*(c.x⁻¹)⁻¹ = (a:G)
    rw [inv_inv,hea,mul_assoc,inv_mul_eq_iff_eq_mul]
    exact (mem_centralizer_singleton_iff.mp g.x_first).symm
  have hna : a ≠ 1 := by
    intro hh
    have ho := g.order_first
    rw [←hea,hh] at ho
    norm_num at ho
  have hiu := c.cubic_first.module_image_le_normal_of_nontrivial
    f (MulAut.innerSubgroup K) a ha hna (hfa.symm ▸ hinner)
  have hiv := c.cubic_first.module_image_le_normal_of_nontrivial
    fx (MulAut.innerSubgroup K) a ha hna (by change φ (jx a) ∈ _; rw [hax]; exact hfa.symm ▸ hinner)
  obtain ⟨f₀,hf₀,hact₀⟩ := g.faithful_first_block_action hG h K hK
  have hff : f = f₀ := by
    ext l k
    exact (hact l k).trans (hact₀ l k).symm
  have hf : Function.Injective f := hff ▸ hf₀
  have hRT : sourceR d ≤ (T : Subgroup G) := by
    rw [←c.baumann]
    exact (show ChapterB.baumann _ ≤ _ from inf_le_left).trans c.original.T_le
  have hUR : c.U₁ ≤ sourceR d := c.baumann ▸ c.first.module_le
  have hVR : c.V₁ ≤ sourceR d := c.baumann ▸ c.first.conjugate_le (c.original.R_normal c.x_mem)
  let Q := ((sourceR d).subgroupOf H).subgroupOf N
  have hQ : IsPGroup 2 Q := (T.isPGroup'.to_le hRT).comap_subtype.comap_subtype
  have hB := Chapter1.QuasisimpleInvolutions.isSimpleBenderGroup_of_benderModel hm
  let : IsElementaryAbelian 2 (blockU L) := c.first.short.elementary
  apply c.noncommuting
  rintro v ⟨w,hw,rfl⟩ u hu
  obtain ⟨b,hb,rfl⟩ := hw
  obtain ⟨a',ha',rfl⟩ := hu
  have hja : j a' ∈ Q := hUR (mem_map_of_mem L.subtype ha')
  have hjb : jx b ∈ Q := hVR (mem_map_of_mem (MulAut.conj c.x⁻¹).toMonoidHom
    (mem_map_of_mem L.subtype hb))
  have ha2 : a'^2=1 := by
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) a' ha'
  have hb2 : b^2=1 := by
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb
  have hc := hB.inner_squares_commute_in_twoSubgroup hzK (Q.map φ) (hQ.map φ)
    (f a') (fx b) (mem_map_of_mem φ hja) (mem_map_of_mem φ hjb)
    (hiu (mem_map_of_mem f ha')) (hiv (mem_map_of_mem fx hb))
    (by rw [←map_pow,ha2,map_one]) (by rw [←map_pow,hb2,map_one])
  let v : G := (MulAut.conj c.x⁻¹) (b:G)
  have hvR : v ∈ sourceR d := hVR (mem_map_of_mem (MulAut.conj c.x⁻¹).toMonoidHom
    (mem_map_of_mem L.subtype hb))
  have hvL : v ∈ normalizer (L : Set G) := c.first.normalizes (by change v ∈ ChapterB.baumann _; rwa [c.baumann])
  let y : L := ⟨v*(a':G)*v⁻¹,(mem_normalizer_iff.mp hvL _).mp a'.property⟩
  have hjy : j y = jx b * j a' * (jx b)⁻¹ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hfy : f y = f a' := by
    change φ (j y) = _
    rw [hjy,map_mul,map_mul,map_inv]
    change fx b * f a' * (fx b)⁻¹ = f a'
    rw [←hc.eq,mul_inv_cancel_right]
  have hy := congrArg (fun l : L => (l:G)) (hf hfy)
  change (a':G) * v = v * (a':G)
  exact (mul_inv_eq_iff_eq_mul.mp hy).symm
/-- Exact Bender subrow of the actual lie constructor of 1.1.5. -/
theorem SourceCentralizerGeometry.bender_model_false
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (hs : IsSimpleGroup K) (hm : ClassificationModels.IsBenderModel K)
    (hinner : α ∈ (MulAut.conj : K →* MulAut K).range) : False := by
  let := hs
  let : IsQuasisimple K := hK.2
  have hz : center K = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) inferInstance).resolve_right
      (fun hc => Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp hc))
  exact g.bender_component_action_false hG h K hK α hα hinner hz hm
end CFSG.Quasithin.Chapter2.DoubleA3
