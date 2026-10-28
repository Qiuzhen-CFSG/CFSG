module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.LocalFactors
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.PostSylowInputs

/-!
# Simultaneous source LocalData after the overgroup Sylow theorem

The original two pairs and the whole-module conclusions of 15.4.12 produce
all four local configurations. The actual commutator modules, cubic factors,
index-three quotients, intersections and rank bounds are constructed here.
The 15.4.20 overgroup-Sylow conclusion is the sole later source input; the
proved post-Sylow transfer then supplies every 1.1.5 and fitting field.

This theorem constructs LocalData, never assumes it. Its overgroup-Sylow
premise remains with the contrary-case assembly.
Source: Aschbacher--Smith, 15.4.12, 15.4.19--20, printed pp.1160--1165.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
open FamilySource FamilySource.ModuleStructure TwoFactors TwoFactors.SourceFactors
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M M₁ M₂ X Y : Subgroup G}

private theorem thompson_le_baumann (T : Subgroup G) :
    ChapterB.thompsonJ T 0 ≤ ChapterB.baumann T := by
  refine le_inf (ChapterB.thompsonJ_le _ _) ?_
  intro j hj a ha
  rw [ChapterB.thompsonAlpha_eq] at ha
  exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp ha).2.2 j hj |>.symm

private theorem omega_le_baumann (T : Subgroup G) :
    Stellmacher.omegaOneCenterAmbient T ≤ ChapterB.baumann T := by
  intro z hz
  obtain ⟨hzT, _, hzc⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz
  refine ⟨hzT, fun a ha => ?_⟩
  rw [ChapterB.thompsonAlpha_eq] at ha
  exact hzc a (ChapterB.thompsonJ_le T 0
    ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp ha).1)

private theorem pair_indices (p : Pair T M X) (h : Input K T M X 2)
    (e : Earlier412 T M X) {U : Subgroup G}
    (hSU : ChapterB.baumann (T : Subgroup G) ≤ U) (hUT : U ≤ (T : Subgroup G))
    (hn : ∀ i, U ≤ normalizer (p.quotient.factor i : Set G)) :
    ∀ i, U.relIndex (p.quotient.factor i ⊔ U) = 3 ∧
      ∃ Q : Sylow 2 (p.quotient.factor i ⊔ U : Subgroup G),
        (Q : Subgroup (p.quotient.factor i ⊔ U : Subgroup G)).map
          (p.quotient.factor i ⊔ U : Subgroup G).subtype = U := by
  have hp : ∃ P : Sylow 2 ((p.quotient.factor false ⊔ p.quotient.factor true) ⊔
      ChapterB.baumann (T : Subgroup G) : Subgroup G),
      (P : Subgroup ((p.quotient.factor false ⊔ p.quotient.factor true) ⊔
        ChapterB.baumann (T : Subgroup G) : Subgroup G)).map
          ((p.quotient.factor false ⊔ p.quotient.factor true) ⊔
            ChapterB.baumann (T : Subgroup G) : Subgroup G).subtype =
              ChapterB.baumann (T : Subgroup G) := by
    have hgen : p.quotient.factor false ⊔ p.quotient.factor true = X :=
      p.quotient.factor_generate h
    rw [hgen]
    exact e.sylow
  obtain ⟨P, hP⟩ := hp
  exact factor_indices_from_whole_sylow p.quotient.factor hSU
    (T.isPGroup'.to_le hUT) hn p.quotient.factor_quotient_card P hP

private theorem rank_bound (hG : IsQuasithin G) (L V : Subgroup G)
    (he : IsElementaryAbelian 2 V) (hc : Nat.card V = 4)
    (hVL : V ≤ L) (hn : L ≤ normalizer (V : Set G)) :
    primeRank 3 (normalizer (L.pCoreIn 2 : Set G)) ≤ 2 := by
  let := he
  apply normalizer_three_rank_le_two hG (IsElementaryAbelian.isPGroup 2 V) _ hVL hn
  intro hb
  rw [hb, card_bot] at hc
  omega

/-- All LocalData fields are constructed on the same two original pairs,
from genuine earlier source conclusions and the full uniform 15.4.20 result. -/
theorem source_geometry_localData
    (hX : Input K T M₁ X 2) (hY : Input K T M₂ Y 2)
    (pX : Pair T M₁ X) (pY : Pair T M₂ Y)
    (earlierX : Earlier412 T M₁ X) (earlierY : Earlier412 T M₂ Y)
    (hM₁ : normalizer (X : Set G) = M₁) (hM₂ : normalizer (Y : Set G) = M₂)
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ (T : Subgroup G) ≤ M → M = M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y ⊔ (T : Subgroup G) ≤ M → M = M₂)
    (hne : M₁ ≠ M₂)
    (hZcard : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hCZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (X : Set G) ≠ ⊥)
    (hSylow : ∀ i j, ∀ H ∈ Chapter1.HOver G ((geometry pX pY).I i j : Set G),
      ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = (geometry pX pY).T₀) :
    Nonempty (Source.LocalData (geometry pX pY)) := by
  let d := geometry pX pY
  change Nonempty (Source.LocalData d)
  have ht : d.T = T := rfl
  have hx : d.wholeX = X := pX.quotient.factor_generate hX
  have hy : d.wholeY = Y := pY.quotient.factor_generate hY
  have hm₁ : d.M₁ = M₁ := by change normalizer (d.wholeX : Set G) = M₁; rw [hx, hM₁]
  have hm₂ : d.M₂ = M₂ := by change normalizer (d.wholeY : Set G) = M₂; rw [hy, hM₂]
  have hs : ChapterB.baumann (T : Subgroup G) ≤ d.T₀ := baumann_le_geometry_T₀ pX pY
  have hj : d.J ≤ d.T₀ := (thompson_le_baumann _).trans hs
  have hnX (i) : d.T₀ ≤ normalizer (d.X i : Set G) :=
    pX.normalizes hX.sylow_le d.T₀_le_T (inf_le_left.trans inf_le_right) i
  have hnY (i) : d.T₀ ≤ normalizer (d.Y i : Set G) :=
    pY.normalizes hY.sylow_le d.T₀_le_T inf_le_right i
  have hvX (i) : d.G₁ i ≤ normalizer (d.V₁ i : Set G) :=
    commutator_factors_normalized
      ((sup_le ((pX.factor_le hX i).trans hX.member_le)
        (d.T₀_le_T.trans hX.sylow_le)).trans (localV_normalized _ _))
      (sup_le (d.X i).le_normalizer (hnX i))
  have hvY (i) : d.G₂ i ≤ normalizer (d.V₂ i : Set G) :=
    commutator_factors_normalized
      ((sup_le ((pY.factor_le hY i).trans hY.member_le)
        (d.T₀_le_T.trans hY.sylow_le)).trans (localV_normalized _ _))
      (sup_le (d.Y i).le_normalizer (hnY i))
  have hiX := pair_indices pX hX earlierX hs d.T₀_le_T hnX
  have hiY := pair_indices pY hY earlierY hs d.T₀_le_T hnY
  have hc := source_geometry_conclusions hX hY pX pY earlierX earlierY hM₁ hM₂
    huniqueX huniqueY hne hZcard hCZ
  obtain ⟨P, hP, hN, h115, hfit⟩ := source_geometry_postSylow_inputs hX.ambient d rfl
    (fun i j => (hc.central_geometry i j).2.2.1) hSylow
  refine ⟨{
    J_le := hj
    Z_le := (omega_le_baumann _).trans hs
    Z_elementary := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
    Z_card := hZcard
    centralizer_Z := hX.center_centralizer
    VM₁_elementary := localV_elementary T M₁ hX.sylow_le
      (hX.ambient.evenCharacteristic T M₁ hX.maximal hX.sylow_le)
    VM₂_elementary := localV_elementary T M₂ hY.sylow_le
      (hY.ambient.evenCharacteristic T M₂ hY.maximal hY.sylow_le)
    VM₁_le := (localV_le _ _).trans_eq hm₁.symm
    VM₂_le := (localV_le _ _).trans_eq hm₂.symm
    VM₁_normalized := hm₁.le.trans (localV_normalized (T : Subgroup G) M₁)
    VM₂_normalized := hm₂.le.trans (localV_normalized (T : Subgroup G) M₂)
    T_normalizes_X := by simpa only [hx, ht, hM₁] using hX.sylow_le
    T_normalizes_Y := by simpa only [hy, ht, hM₂] using hY.sylow_le
    X_normalized := hnX
    Y_normalized := hnY
    normalizer_X_eq := pX.normalizer_eq hX.sylow_le
    normalizer_Y_eq := pY.normalizer_eq hY.sylow_le
    X_commutator := pX.thompson_commutator hX
    Y_commutator := pY.thompson_commutator hY
    X_perfect := pX.quotient.factor_perfect
    Y_perfect := pY.quotient.factor_perfect
    wholeX_quotient_elementary := hx.symm ▸ hX.quotient_elementary
    wholeY_quotient_elementary := hy.symm ▸ hY.quotient_elementary
    wholeX_quotient_card := hx.symm ▸ hX.quotient_card
    wholeY_quotient_card := hy.symm ▸ hY.quotient_card
    X_quotient_card := pX.quotient.factor_quotient_card
    Y_quotient_card := pY.quotient.factor_quotient_card
    V₁_le := pX.module_le_factor hX
    V₂_le := pY.module_le_factor hY
    V₁_elementary := pX.module_elementary hX
    V₂_elementary := pY.module_elementary hY
    V₁_card := pX.module_card
    V₂_card := pY.module_card
    V₁_normalized := hvX
    V₂_normalized := hvY
    V₁_disjoint := pX.module_disjoint
    V₂_disjoint := pY.module_disjoint
    V₁_full_commutator := pX.module_full_commutator hX
    V₂_full_commutator := pY.module_full_commutator hY
    siblings_X := pX.sibling_commutator hX
    siblings_Y := pY.sibling_commutator hY
    X_outside := hc.outside_X
    Y_outside := hc.outside_Y
    intersection := hc.intersections
    sylow := P
    sylow_image := hP
    sylow_core_normalizer := hN
    quotient₁ := ?_
    quotient₂ := ?_
    local115 := h115
    fitting_of_Z_meets_core := hfit
    central_intersection := fun i j => (hc.central_geometry i j).2.2.2
    normalizer_rank := fun i => rank_bound hX.ambient.quasithin (d.X i) (d.V₁ i)
      (pX.module_elementary hX i) (pX.module_card i) (pX.module_le_factor hX i)
      (le_sup_left.trans (hvX i)) }⟩
  · intro i
    obtain ⟨Q, hQ⟩ := (hiX i).2
    exact pX.local_symmetricThree hX i d.T₀ hj Q hQ (hiX i).1
  · intro i
    obtain ⟨Q, hQ⟩ := (hiY i).2
    exact pY.local_symmetricThree hY i d.T₀ hj Q hQ (hiY i).1

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
