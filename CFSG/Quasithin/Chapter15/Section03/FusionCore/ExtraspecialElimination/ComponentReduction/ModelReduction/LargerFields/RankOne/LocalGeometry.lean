module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.BorelMarking
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.LocalNormalizer
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.LocalSections

/-!
# Intrinsic cubic control on the component closure

The source Sylow subgroup restricts to the relatively normal closure and
then maps to a Sylow subgroup of L₀*. The literal Y₀* is normalized by this
Sylow subgroup. Its cubes lie in its two-core, while an element of order
three survives the star quotient. The local normalizer identity and exact
three-rank restriction therefore hold inside L₀*, with no model conclusion
assumed. These facts are packaged in `CubicSylowControl` for model geometry.

If a Borel contains this subgroup and its Sylow subgroup, its abelian
quotient by the unipotent group forces it to normalize their product.
Taking theta recovers the cubic subgroup, so the Borel's theta has
three-rank at most one. The remaining model calculations must prove Borel
containment and exploit this bound.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49 after (k), printed p.1144.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.Chapter1
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne
variable {G : Type*} [Group G] [Finite G]

/-- The literal Sylow intersection maps to a Sylow subgroup of the closure image. -/
theorem closure_sylow (H L Y T : Subgroup G)
    (hgen : H = reducedOvergroup L Y T) (hcomm : L = ⁅L,Y⁆)
    (hn : T ≤ normalizer (Y : Set G)) (hT : IsSylowIn 2 T H) :
    IsSylowIn 2 (starImage H (T ⊓ localSpan L T)) (starImage H (localSpan L T)) := by
  have hLH : localSpan L T ≤ H := hgen ▸ le_sup_left
  have hN := componentClosure_normal_in_replacement L Y T
    (le_normalizer_iff_commutator_le_left.mpr hcomm.ge) hn
  rw [← hgen] at hN
  have hs := Section02.IndexTwo.isSylowIn_inf_of_subnormal hT hLH hN.isSubnormal
  exact BinaryModels.starImage_isSylowIn H _ _ (inf_le_right.trans hLH) hLH hs

omit [Finite G] in
/-- Normalization descends to the literal local quotient. -/
theorem star_normalizes (H A B : Subgroup G) (hn : A ≤ normalizer (B : Set G)) :
    starImage H A ≤ normalizer (starImage H B : Set (H ⧸ pCore 2 H)) :=
  (map_mono ((comap_mono hn).trans (B.le_normalizer_comap H.subtype))).trans
    ((B.subgroupOf H).le_normalizer_map (QuotientGroup.mk' (pCore 2 H)))

omit [Finite G] in
/-- The order-three quotient forces cubes into the two-core of the star image. -/
theorem star_cubes (H Y : Subgroup G) (hYH : Y ≤ H)
    (hcard : Nat.card (Y ⧸ pCore 2 Y) = 3) :
    ∀ y : starImage H Y, y ^ 3 ∈ pCore 2 (starImage H Y) := by
  let e := (subgroupOfEquivOfLe hYH).symm
  let f := ((QuotientGroup.mk' (pCore 2 H)).subgroupMap (Y.subgroupOf H)).comp e.toMonoidHom
  exact RankOne.cubes_mem_core_of_surjective f
    (((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective (Y.subgroupOf H)).comp e.surjective)
    (RankOne.cubes_mem_core_of_card hcard)

/-- A cubic element survives a quotient whose kernel is a two-group. -/
theorem star_cubic (H Y : Subgroup G) (hYH : Y ≤ H)
    (hY : Nat.card (Y ⧸ pCore 2 Y) = 3) :
    ∃ y : starImage H Y, orderOf y = 3 := by
  have hd : 3 ∣ Nat.card Y := hY ▸ (pCore 2 Y).index_dvd_card
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 hd
  let f : Y →* H ⧸ pCore 2 H := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hYH)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (((QuotientGroup.mk' (pCore 2 H)).comp (inclusion hYH)).ker)
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hYH)
  have ho : orderOf (f y) = 3 :=
    (f.orderOf_map_eq_of_coprime_of_isPGroup_ker hk y
      (hy ▸ (by decide : Nat.Coprime 2 3))).trans hy
  have hm : f y ∈ starImage H Y := ⟨⟨y, hYH y.property⟩, y.property, rfl⟩
  exact ⟨⟨f y, hm⟩, (Subgroup.orderOf_coe _).symm.trans ho⟩

/-- A Sylow subgroup of the closure image normalizes its intrinsic Y₀ image. -/
theorem star_sylow_normalizes (H L Y T : Subgroup G)
    (hgen : H = reducedOvergroup L Y T) (hcomm : L = ⁅L,Y⁆)
    (hn : T ≤ normalizer (Y : Set G)) (hT : IsSylowIn 2 T H) :
    ∃ S : Sylow 2 (starImage H (localSpan L T)),
      (S : Subgroup (starImage H (localSpan L T))) ≤
        normalizer ((starImage H Y).subgroupOf (starImage H (localSpan L T)) :
          Set (starImage H (localSpan L T))) := by
  obtain ⟨S,hS⟩ := closure_sylow H L Y T hgen hcomm hn hT
  refine ⟨S, ?_⟩
  have hnorm := star_normalizes H (T ⊓ localSpan L T) Y (inf_le_left.trans hn)
  have hcomap := (comap_mono hnorm).trans
    ((starImage H Y).le_normalizer_comap (starImage H (localSpan L T)).subtype)
  rw [← hS, comap_map_eq_self_of_injective (starImage H (localSpan L T)).subtype_injective] at hcomap
  exact hcomap

/-- The local theta identity inside the closure, rather than the ambient quotient. -/
theorem star_theta_normalizer (H M K Y : Subgroup G)
    (hθ : theta (M ⊓ H) = Y) (hN : normalizer (Y : Set G) = M)
    (hcore : localTwoCore H ≤ M) (hYK : Y ≤ K) :
    theta (normalizer ((starImage H Y).subgroupOf (starImage H K) : Set (starImage H K))) =
      (starImage H Y).subgroupOf (starImage H K) := by
  have hle : starImage H Y ≤ starImage H K := map_mono (comap_mono hYK)
  apply map_injective (starImage H K).subtype_injective
  rw [theta_map_of_injective _ (starImage H K).subtype_injective,
    ← subgroupOf_normalizer_eq hle, subgroupOf_map_subtype, inf_comm,
    theta_star_component_normalizer H M K Y hθ hN hcore hYK,
    map_subgroupOf_eq_of_le hle]


omit [Finite G] in
/-- An abelian Borel quotient promotes Sylow normalization to Borel normalization. -/
theorem borel_le_normalizer (B U C : Subgroup G)
    (hCB : C ≤ B) (hUB : U ≤ B) (hUC : U ≤ normalizer (C : Set G))
    (hcomm : ⁅B,B⁆ ≤ U) (hθ : theta (normalizer (C : Set G)) = C) :
    B ≤ normalizer (C : Set G) := by
  have hfix : theta C = C := by rw [← hθ, theta_idempotent]
  have hsup : theta (C ⊔ U) = C := by
    apply le_antisymm
    · exact (theta_mono (sup_le C.le_normalizer hUC)).trans_eq hθ
    · exact hfix.symm.le.trans (theta_mono le_sup_left)
  have hn : B ≤ normalizer ((C ⊔ U : Subgroup G) : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono (sup_le hCB hUB) le_rfl).trans (hcomm.trans le_sup_right))
  simpa only [hsup] using hn.trans (normalizer_le_normalizer_theta (C ⊔ U))

/-- Intrinsic local restrictions, with no model identification as a premise. -/
structure CubicSylowControl (D : Type*) [Group D] (C : Subgroup D) : Prop where
  normalized : ∃ S : Sylow 2 D, (S : Subgroup D) ≤ normalizer (C : Set D)
  cubes : ∀ c : C, c ^ 3 ∈ pCore 2 C
  cubic : ∃ c : C, orderOf c = 3
  theta_normalizer : theta (normalizer (C : Set D)) = C
  rank : primeRank 3 C = 1

/-- Construct all intrinsic restrictions from the genuine earlier local hypotheses. -/
theorem cubicSylowControl_star (H M L Y T : Subgroup G)
    (hgen : H = reducedOvergroup L Y T) (hcomm : L = ⁅L,Y⁆)
    (hn : T ≤ normalizer (Y : Set G)) (hT : IsSylowIn 2 T H) (hTM : T ≤ M)
    (hθ : theta (M ⊓ H) = Y) (hN : normalizer (Y : Set G) = M)
    (hY : Nat.card (Y ⧸ pCore 2 Y) = 3) (hYL : Y ≤ localSpan L T) :
    CubicSylowControl (starImage H (localSpan L T))
      ((starImage H Y).subgroupOf (starImage H (localSpan L T))) := by
  have hLH : localSpan L T ≤ H := hgen ▸ le_sup_left
  have hYH := hYL.trans hLH
  have hle : starImage H Y ≤ starImage H (localSpan L T) := map_mono (comap_mono hYL)
  let C := (starImage H Y).subgroupOf (starImage H (localSpan L T))
  let a : starImage H Y ≃* C := (subgroupOfEquivOfLe hle).symm
  obtain ⟨y,hy⟩ := star_cubic H Y hYH hY
  have hne : starImage H (localSpan L T) ≠ ⊥ := by
    intro he
    have hyy : (y : H ⧸ pCore 2 H) = 1 := by
      have hm := hle y.property
      rwa [he, mem_bot] at hm
    have hy1 : y = 1 := Subtype.ext hyy
    simp [hy1] at hy
  have hcard : Nat.card ((Y.subgroupOf H) ⧸ pCore 2 (Y.subgroupOf H)) = 3 := by
    let e := subgroupOfEquivOfLe hYH
    exact (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).trans hY
  refine ⟨star_sylow_normalizes H L Y T hgen hcomm hn hT,
    RankOne.cubes_mem_core_of_surjective a.toMonoidHom a.surjective (star_cubes H Y hYH hY),
    ⟨a y, (a.orderOf_eq y).trans hy⟩,
    star_theta_normalizer H M (localSpan L T) Y hθ hN
      (localTwoCore_le_of_sylow H M T hT hTM) hYL, ?_⟩
  exact (Theory.GroupTheory.primeRank_equiv 3 a).symm.trans
    (star_threeRank_eq_one H M (localSpan L T) Y hLH hθ
      (componentClosure_commutator L Y T hcomm hn) hne hcard)

/-- A Borel satisfying its usual commutator bound has cubic rank at most one. -/
theorem CubicSylowControl.borel_rank_le_one (C : Subgroup G)
    (hC : CubicSylowControl G C) (B U : Subgroup G)
    (hCB : C ≤ B) (hUB : U ≤ B) (hUC : U ≤ normalizer (C : Set G))
    (hcomm : ⁅B,B⁆ ≤ U) : primeRank 3 (theta B) ≤ 1 := by
  have hB := borel_le_normalizer B U C hCB hUB hUC hcomm hC.theta_normalizer
  have hle : theta B ≤ C := (theta_mono hB).trans_eq hC.theta_normalizer
  exact (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hle)
    (inclusion_injective hle)).trans_eq hC.rank

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne
