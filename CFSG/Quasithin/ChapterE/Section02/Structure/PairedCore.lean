module
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.OriginalImage
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedComponents
public import Theory.GroupTheory.PerfectCentralCoverOddRankRigidity
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# The original core in the paired E.2.2 case

After quotienting by the ambient two-core, the selected C-component is
quasisimple and remains nonnormal. Its simple image in the actual star
quotient has every odd-prime rank at most one, because it has a distinct
commuting conjugate. The odd central kernel of the component map therefore
vanishes by perfect-cover transfer. Both commuting factors are centerless,
so the layer center, hence the minimal-parabolic core, is trivial.
Pulling back through the literal two-core quotient proves J = O₂(H).

Source: Aschbacher–Smith E.2.2(1), printed pp.215–216. The genuine earlier
Theorem A supplies SQTK for the star quotient; no simple-model or Schur
multiplier classification is required.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Structure.PairedCore
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

private theorem center_eq_bot_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : center A = ⊥ := by
  apply Subgroup.card_eq_one.mp
  rw [Nat.card_congr (centerCongr e).toEquiv, hz]
  simp

/-- The paired component has trivial center after the ambient two-core is removed. -/
theorem component_center_eq_bot
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (hO : pCore 2 H = ⊥)
    {K : Subgroup H} (hK : IsComponent H K)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal) : center K = ⊥ := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  have hC := hK.isCComponent
  have him := source_component_simple_image T hP hs K hC hgen
  let : IsSimpleGroup (K.map q) := him.1
  let : IsQuasisimple K := hK.2
  have hrad : solvableRadical (H ⧸ J) = ⊥ := by
    let e : (H ⧸ J) ≃* (H ⧸ solvableRadical H) := QuotientGroup.quotientMulEquivOfEq
      (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs)
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_solvableRadical_equiv,solvableRadical_quotient_solvableRadical,Subgroup.map_bot]
  have hnot : ¬ (K.map q).Normal := fun hh =>
    hn (cComponent_normal_of_quotient_normal hC J hh)
  have hnt : ¬ (⊤ : Subgroup (H ⧸ J)) ≤ normalizer (K.map q : Set (H ⧸ J)) :=
    fun hh => hnot (normalizer_eq_top_iff.mp (top_unique hh))
  obtain ⟨t,_,ht⟩ := SetLike.not_le_iff_exists.mp hnt
  have hr := paired_component_odd_rank_le_one
    (source_star_sqtk hA hH T hP hs).stronglyQuasithin hrad him.2.1 (hC.map_quotient J)
    t (fun he => ht (mem_normalizer_iff_map_conj_eq.mpr he))
  let f := q.subgroupMap K
  have hf := q.subgroupMap_surjective K
  have hfc : f.ker ≤ center K := by
    rcases IsQuasisimple.normal_le_center_or_eq_top f.ker with hc | he
    · exact hc
    · have hbot : f.range = ⊥ := MonoidHom.range_eq_bot_iff.mpr
        (MonoidHom.ker_eq_top_iff.mp he)
      exact (bot_ne_top (hbot.symm.trans (MonoidHom.range_eq_top.mpr hf))).elim
  let c : PerfectCentralCovering.Cover K (K.map q) :=
    { toMonoidHom := f, surjective := hf, isPerfect := inferInstance, ker_le_center := hfc }
  have hodd : Odd (Nat.card f.ker) := by
    change Odd (Nat.card (q.subgroupMap K).ker)
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact (core_odd_of_twoCore_eq_bot T hP hO).of_dvd_nat
      (card_comap_dvd_of_injective J K.subtype K.subtype_injective)
  have hk := c.ker_eq_bot_of_odd_of_odd_primeRank_le_one hodd hr
  have hz := center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hrad him.2.1.1
  rw [← c.comap_center, hz, MonoidHom.comap_bot]
  exact hk

/-- The core vanishes in the original paired case with trivial ambient two-core. -/
theorem core_eq_bot
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (hO : pCore 2 H = ⊥)
    {K : Subgroup H} (hK : IsComponent H K)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal) :
    ChapterB.minimalParabolicCore T hP = ⊥ := by
  have hzK := component_center_eq_bot hA hH T hP hs hO hK hgen hn
  rcases component_normal_or_pair hH.stronglyQuasithin T hK hgen with h |
    ⟨t,_,hD,hcomm,_,hR,_,_⟩
  · exact (hn h.1).elim
  let D := K.map (MulAut.conj (t:H)).toMonoidHom
  have hzD : center D = ⊥ :=
    center_eq_bot_of_equiv ((MulAut.conj (t:H)).subgroupMap K).symm hzK
  have hE : componentLayer H = K ⊔ D := (residual_eq_layer T hK hgen).symm.trans hR
  rw [core_eq_layer_center T hP hs hO hK hgen]
  apply le_bot_iff.mp
  rintro x ⟨z,hz,rfl⟩
  have hzc : (z:H) ∈ centralizer (componentLayer H : Set H) :=
    fun y hy => congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hy⟩)
  have hzE : (z:H) ∈ K ⊔ D := hE ▸ z.property
  have hzcE : (z:H) ∈ centralizer ((K ⊔ D : Subgroup H) : Set H) := hE ▸ hzc
  have hKD : K ≤ centralizer (D : Set H) := commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hDK := le_centralizer_iff.mp hKD
  have hzprod : (z:H) ∈ (K : Set H) * (D : Set H) := by
    rw [← coe_mul_of_right_le_normalizer_left K D (hDK.trans (Subgroup.centralizer_le_normalizer _))]
    exact hzE
  obtain ⟨a,ha,b,hb,hab⟩ := hzprod
  change a * b = (z:H) at hab
  have hzab : a * b ∈ centralizer ((K ⊔ D : Subgroup H) : Set H) := by
    rw [hab]
    exact hzcE
  have hca : a ∈ centralizer (K : Set H) :=
    (centralizer (K : Set H)).mul_mem_cancel_right (hDK hb) |>.mp
      ((centralizer_le (show K ≤ K ⊔ D from le_sup_left)) hzab)
  have hcb : b ∈ centralizer (D : Set H) :=
    (centralizer (D : Set H)).mul_mem_cancel_left (hKD ha) |>.mp
      ((centralizer_le (show D ≤ K ⊔ D from le_sup_right)) hzab)
  have hae : a = 1 := by
    have hac : (⟨a,ha⟩ : K) ∈ center K :=
      mem_center_iff.mpr (fun y => Subtype.ext (hca y y.property))
    rw [hzK,mem_bot] at hac
    exact congrArg Subtype.val hac
  have hbe : b = 1 := by
    have hbc : (⟨b,hb⟩ : D) ∈ center D :=
      mem_center_iff.mpr (fun y => Subtype.ext (hcb y y.property))
    rw [hzD,mem_bot] at hbc
    exact congrArg Subtype.val hbc
  apply mem_bot.mpr
  change (z:H) = 1
  simpa only [hae,hbe,one_mul] using hab.symm

/-- E.2.2(1): the actual original normal core is exactly the two-core. -/
theorem source
    (hA : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremA κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    {K : Subgroup H} (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal) :
    ChapterB.minimalParabolicCore T hP = pCore 2 H := by
  let N := pCore 2 H
  let q := QuotientGroup.mk' N
  have hq := QuotientGroup.mk'_surjective N
  let S := T.mapSurjective hq
  have hk : q.ker ≤ (T : Subgroup H) := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal T
  have hPq := ChapterB.minimalParabolic_surjective T hP q hq hk
  let : Group.IsNilpotent N := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  have hsQ : ¬ Group.IsSolvable (H ⧸ N) := fun hh =>
    hs ((Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance,hh⟩)
  let : IsQuasisimple (K ⧸ pCore 2 K) := hqK
  have hKQ : IsComponent (H ⧸ N) (K.map q) :=
    ⟨hK.subnormal.map hq, IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)⟩
  have hgenQ : K.map q ⊔ (S : Subgroup (H ⧸ N)) = ⊤ := by
    change K.map q ⊔ (T : Subgroup H).map q = ⊤
    rw [← Subgroup.map_sup,hgen,map_top_of_surjective q hq]
  have hnQ : ¬ (K.map q).Normal := fun hh =>
    hn (cComponent_normal_of_quotient_normal hK N hh)
  have hjQ := core_eq_bot (hA (H ⧸ N)) (sqtk_two_quotient hH N pCore_isPGroup)
    S hPq hsQ (pCore_quotient_pCore_eq_bot (G := H) 2) hKQ hgenQ hnQ
  have hm : (ChapterB.minimalParabolicCore T hP).map q = ⊥ :=
    (ChapterB.minimalParabolicCore_map T hP q hq hk).trans hjQ
  apply le_antisymm
  · simpa only [Subgroup.map_eq_bot_iff,q,QuotientGroup.ker_mk'] using hm
  · exact ChapterB.minimalParabolicTwoCore_le_core T hP
end CFSG.Quasithin.ChapterE.Structure.PairedCore
