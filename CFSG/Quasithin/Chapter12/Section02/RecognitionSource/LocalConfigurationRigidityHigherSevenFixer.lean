module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherSevenPlane
public import Theory.SpecificGroups.AlternatingSeven.SevenFixer

/-!
# Excluding the containing A₇ image through the original hyperplane

Write R=C_T(U), Y=O²(N_L(U∩V)), and let K be the actual normal containing
component in N_G(R). The Y-image is nonsolvable and has order divisible
by seven. V centralizes that image, so the pointwise automorphism-fixer
calculation forces V to centralize the entire K-image when it is A₇.
The literal displacement map r ↦ [r,v], with image U∩V, is consequently
K-equivariant. Thus K acts on the original hyperplane and surjects onto
its full automorphism group, since Y already does. This yields an impossible
surjection from A₇ onto GL₃(2) or GL₄(2).

This proves the exceptional exclusion without an assumed permutation-module
identification. Both embeddings and the actual conjugation/displacement maps
are retained. The containing-image catalogue is still needed to deduce
residual normality; HigherImageSieve records the actual conditional consumer.
Source: Aschbacher–Smith, original 12.2.25, printed p.805.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

theorem hyperplaneAut_card
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U) (hd : 3 < d) :
    Nat.card (MulAut (U ⊓ V : Subgroup G)) = if d = 4 then 168 else 20160 := by
  let := D.elementary
  let : IsElementaryAbelian 2 (U ⊓ V : Subgroup G) := IsElementaryAbelian.of_injective
    (inclusion (show U ⊓ V ≤ V from inf_le_right)) (inclusion_injective _)
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow (U ⊓ V : Subgroup G) (d-1) C.hyperplane]
  have he : d = 4 ∨ d = 5 := by have := A.dimension; omega
  rcases he with rfl | rfl <;> decide

theorem seven_dvd_residual_image
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d) :
    7 ∣ Nat.card (ThreeRigidity.image T U (rigidityHyperplaneResidual L U V)) := by
  let Y := rigidityHyperplaneResidual L U V
  have h7 : 7 ∣ Nat.card (MulAut (U ⊓ V : Subgroup G)) := by
    rw [hyperplaneAut_card D A C hd]
    split <;> decide
  have hY := h7.trans (card_dvd_of_surjective (residualHyperplaneAction L U V)
    (residualHyperplaneAction_surjective D A C hd))
  have hcard : Nat.card (ThreeRigidity.image T U Y) = (sectionRadical T U).relIndex Y := by
    rw [ThreeRigidity.image,← relIndex_ker]
    change (QuotientGroup.mk' ((sectionRadical T U).subgroupOf
      (normalizer (sectionRadical T U : Set G)))).ker.relIndex
        (Y.subgroupOf (normalizer (sectionRadical T U : Set G))) = _
    rw [QuotientGroup.ker_mk',relIndex_subgroupOf B.residual_normalizes]
  rw [hcard]
  have he := relIndex_mul_relIndex (⊥ : Subgroup G) (sectionRadical T U ⊓ Y) Y bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left] at he
  have hi : (sectionRadical T U ⊓ Y).relIndex Y = (sectionRadical T U).relIndex Y := by
    rw [inf_comm,inf_relIndex_left]
  rw [hi] at he
  rw [← he] at hY
  apply ((by decide : Nat.Prime 7).dvd_mul.mp hY).resolve_left
  obtain ⟨n,hn⟩ := (T.isPGroup'.to_le
    (show sectionRadical T U ⊓ Y ≤ (T : Subgroup G) from inf_le_left.trans inf_le_left)).exists_card_eq
  rw [hn]
  exact (by decide : Nat.Prime 7).coprime_iff_not_dvd.mp
    ((by decide : Nat.Coprime 7 2).pow_right n)

/-- The chosen-module action centralizes the containing A₇ image pointwise. -/
theorem chosen_centralizes_alternating_seven_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G))
    (e : ThreeRigidity.image T U K ≃* alternatingGroup (Fin 7))
    (v : V) :
    quotient (sectionRadical T U) ⟨v,sylow_normalizes_sectionRadical C (D.le_sylow v.property)⟩ ∈
      centralizer (ThreeRigidity.image T U K : Set (NormalizerQuotient (sectionRadical T U))) := by
  let R := sectionRadical T U
  let N := normalizer (R : Set G)
  let Kb := ThreeRigidity.image T U K
  let Yb := ThreeRigidity.image T U (rigidityHyperplaneResidual L U V)
  let vN : N := ⟨v,sylow_normalizes_sectionRadical C (D.le_sylow v.property)⟩
  let : (K.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hn
  let : Kb.Normal := Subgroup.Normal.map inferInstance (quotient R) (QuotientGroup.mk'_surjective _)
  let := residual_image_quasisimple h D structural A C B hd
  let : IsSimpleGroup (Yb ⧸ center Yb) := IsQuasisimple.simple
  let : Nontrivial Yb := (QuotientGroup.mk'_surjective (center Yb)).nontrivial
  have hns : ¬ Group.IsSolvable Yb := Group.IsPerfect.not_isSolvable Yb
  apply AlternatingSeven.SevenFixer.centralizes_of_centralizes_subgroup Kb Yb
    (map_mono (comap_mono hYK)) e hns (seven_dvd_residual_image D A C B hd)
    (quotient R vN) (by exact (normalizer_eq_top Kb).symm ▸ mem_top _)
  rintro yb ⟨y,hy,rfl⟩
  have hc := chosen_residual_actions_commute D A C B v ⟨y,hy⟩
  apply (action_injective R (sectionRadical_selfCentralizing h A C B))
  rw [map_mul,map_mul]
  change R.normalizerMonoidHom y * R.normalizerMonoidHom vN =
    R.normalizerMonoidHom vN * R.normalizerMonoidHom y
  exact hc.eq.symm

/-- The original displacement space is invariant under the containing image,
using the actual commutator map, not its dimension or an abstract module tag. -/
theorem containing_normalizes_hyperplane_of_seven_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G))
    (e : ThreeRigidity.image T U K ≃* alternatingGroup (Fin 7)) :
    K ≤ normalizer ((U ⊓ V : Subgroup G) : Set G) := by
  let R := sectionRadical T U
  let : IsElementaryAbelian 2 R := B.elementary
  let := D.elementary
  obtain ⟨v,δ,hv,hδ,hδval,_,_⟩ := exists_radical_displacement D A C B
    (((structural G T L h).2.2 V D).1)
  let vN : normalizer (R : Set G) := ⟨v,sylow_normalizes_sectionRadical C (D.le_sylow v.property)⟩
  have hvc := chosen_centralizes_alternating_seven_image h D structural A C B hd hYK hn e v
  apply le_normalizer_iff.mpr
  intro k hk w hw
  obtain ⟨r,hr⟩ := hδ ⟨w,hw⟩
  let kN : normalizer (R : Set G) := ⟨k,hKN hk⟩
  have hc : Commute (R.normalizerMonoidHom vN) (R.normalizerMonoidHom kN) := by
    have hh := congrArg (action R (by exact (sectionRadical_selfCentralizing h A C B).symm.le))
      (hvc (quotient R kN) (mem_map_of_mem (quotient R) hk))
    rw [map_mul,map_mul] at hh
    change R.normalizerMonoidHom kN * R.normalizerMonoidHom vN =
      R.normalizerMonoidHom vN * R.normalizerMonoidHom kN at hh
    exact hh.symm
  have he := congrArg (fun r : R => (r : G)) (ConjugationDisplacement.equivariant R vN kN hc r)
  have he' : (δ (R.normalizerMonoidHom kN r) : G) = k * w * k⁻¹ := by
    rw [hδval]
    rw [← ConjugationDisplacement.hom_apply R vN (R.normalizerMonoidHom kN r)]
    rw [he]
    change k * (ConjugationDisplacement.hom R vN r : G) * k⁻¹ = _
    rw [ConjugationDisplacement.hom_apply,← hδval r,hr]
  exact he' ▸ (δ (R.normalizerMonoidHom kN r)).property

/-- The literal A₇ containing image is impossible: its action on the original
hyperplane would surject onto GL₃(2) or GL₄(2), contrary to simplicity and order. -/
theorem no_alternating_seven_containing_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P) (hd : 3 < d)
    {K : Subgroup G} (hKN : K ≤ normalizer (sectionRadical T U : Set G))
    (hYK : rigidityHyperplaneResidual L U V ≤ K)
    (hn : normalizer (sectionRadical T U : Set G) ≤ normalizer (K : Set G)) :
    ¬ Chapter1.Section02.LocalModels.IsAlternating (ThreeRigidity.image T U K) 7 := by
  rintro ⟨e⟩
  let R := sectionRadical T U
  let W := U ⊓ V
  let Kb := ThreeRigidity.image T U K
  have hKW := containing_normalizes_hyperplane_of_seven_image h D structural A C B hd hKN hYK hn e
  let a : K →* MulAut W := W.normalizerMonoidHom.comp (inclusion hKW)
  have ha : Function.Surjective a := by
    intro b
    obtain ⟨y,hy⟩ := residualHyperplaneAction_surjective D A C hd b
    exact ⟨⟨y,hYK y.property⟩,hy⟩
  let q : K →* NormalizerQuotient R := (quotient R).comp (inclusion hKN)
  have hqrange : q.range = Kb := by
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨k,rfl⟩
      exact k.property
    · intro hx
      exact ⟨⟨x,hx⟩,Subtype.ext rfl⟩
  have hka : q.ker ≤ a.ker := by
    intro k hk
    have hkR : (k : G) ∈ R :=
      (QuotientGroup.eq_one_iff (⟨k,hKN k.property⟩ : normalizer (R : Set G))).mp hk
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hkR.2 w w.property.1).symm
  let g : (K ⧸ q.ker) →* MulAut W := QuotientGroup.lift q.ker a hka
  have hg : Function.Surjective g := QuotientGroup.lift_surjective_of_surjective _ _ ha hka
  let j : (K ⧸ q.ker) ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientKerEquivRange q).trans ((MulEquiv.subgroupCongr hqrange).trans e)
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (K ⧸ q.ker) := j.isSimpleGroup
  have hAut : Nat.card (MulAut W) = if d = 4 then 168 else 20160 := hyperplaneAut_card D A C hd
  rcases (inferInstance : g.ker.Normal).eq_bot_or_eq_top with hk | hk
  · have hi := (MonoidHom.ker_eq_bot_iff _).mp hk
    have he := Nat.card_congr (Equiv.ofBijective g ⟨hi,hg⟩)
    rw [Nat.card_congr j.toEquiv,nat_card_alternatingGroup,hAut] at he
    split at he <;> norm_num at he
  · have htriv : ∀ b : MulAut W, b = 1 := by
      intro b
      obtain ⟨k,rfl⟩ := hg b
      exact MonoidHom.mem_ker.mp (hk ▸ mem_top k)
    let : Subsingleton (MulAut W) := ⟨fun b c => (htriv b).trans (htriv c).symm⟩
    let : Unique (MulAut W) := ⟨⟨1⟩,htriv⟩
    have he : Nat.card (MulAut W) = 1 := Nat.card_unique
    rw [hAut] at he
    split at he <;> norm_num at he

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
