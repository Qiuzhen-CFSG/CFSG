module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.NoncontainedLocalRank
public import Theory.GroupTheory.PResidual.NormalizedImageContainment
public import Theory.GroupTheory.SylowCoreRestriction
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The original noncontained local subgroup in H-star

The two-perfect source residual remains outside a normal component after
quotienting by the two-core: containment in the quotient would lift through
the two-group kernel. Its established Sylow commutator identity passes
through the same quotient map. The earlier local A₄ quotient excludes a
factor 5 from its order, and its exact three-part excludes a factor 9.

The ambient two-core lies in the local core because the local subgroup
contains the actual Sylow subgroup. The two-core image theorem then gives
the literal core of the local image, with no change of quotient conventions.
The final packet is the actual source consumer of these identities.

Source: Aschbacher–Smith, 13.7.19, printed pp.944–945.
-/

public section
open Subgroup BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion Section08.Source
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)

theorem source_noncontained_star_not_le
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M)
    (hKH : K ≤ H) (hKn : H ≤ normalizer (K : Set G))
    (hout : ¬ sourceOne L T V₁ ≤ K) :
    ¬ starImage H (sourceOne L T V₁) ≤ starImage H K := by
  intro hi
  have hJH : sourceOne L T V₁ ≤ H := le_sup_left.trans hH.1.2
  let X := (sourceOne L T V₁).subgroupOf H
  let Y := K.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let : Y.Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  have hp : IsPPerfect 2 X :=
    (isPPerfect_embedded_pResidual 2
      ((L ⊔ (T : Subgroup G)) ⊓ normalizer (V₁ : Set G))).of_surjective
      (subgroupOfEquivOfLe hJH).symm.toMonoidHom (subgroupOfEquivOfLe hJH).symm.surjective
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hXY : X ≤ Y := isPPerfect_le_of_map_le_of_kernel_normalizes q X Y hp hk
    le_normalizer_of_normal hi
  apply hout
  intro x hx
  exact hXY (show (⟨x, hJH hx⟩ : H) ∈ X from hx)

include d in
theorem source_local_star_eq_commutator
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (UH H V₃))
    (hV : ¬ IsMulCommutative (VH H V)) :
    starImage H (sourceOne L T V₁) =
      ⁅starImage H (sourceOne L T V₁), starImage H (T : Subgroup G)⁆ := by
  have hJH : sourceOne L T V₁ ≤ H := le_sup_left.trans hH.1.2
  have hTH : (T : Subgroup G) ≤ H := h.T_le_H
  have hc : (sourceOne L T V₁).subgroupOf H =
      ⁅(sourceOne L T V₁).subgroupOf H, (T : Subgroup G).subgroupOf H⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hJH,
      map_subgroupOf_eq_of_le hTH]
    exact source_local_eq_commutator_sylow d h hU hV
  have he := congrArg (map (QuotientGroup.mk' (pCore 2 H))) hc
  rwa [map_commutator] at he

include d in
theorem source_local_star_card_constraints
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (UH H V₃))
    (hV : ¬ IsMulCommutative (VH H V)) :
    ¬ 5 ∣ Nat.card (starImage H (sourceOne L T V₁)) ∧
      ¬ 9 ∣ Nat.card (starImage H (sourceOne L T V₁)) := by
  have hJH : sourceOne L T V₁ ≤ H := le_sup_left.trans hH.1.2
  have hd : Nat.card (starImage H (sourceOne L T V₁)) ∣ Nat.card (sourceOne L T V₁) := by
    have hh := card_map_dvd ((sourceOne L T V₁).subgroupOf H)
      (QuotientGroup.mk' (pCore 2 H))
    rwa [Nat.card_congr (subgroupOfEquivOfLe hJH).toEquiv] at hh
  have h5 : ¬ 5 ∣ Nat.card (sourceOne L T V₁) := by
    obtain ⟨f, hf, hker⟩ := source_local_residual_surjection d h hU hV
    have hp : IsPGroup 2 f.ker := by
      rw [hker]
      exact (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).comap_subtype
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have he := card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
      nat_card_alternatingGroup, Nat.card_fin, hn,
      PlusAction.source_local_residual_eq d h] at he
    norm_num at he
    rw [he]
    intro hh
    rcases (by decide : Nat.Prime 5).dvd_mul.mp hh with hh | hh
    · exact (by decide : ¬ 5 ∣ 12) hh
    · exact (by decide : ¬ 5 ∣ 2) ((by decide : Nat.Prime 5).dvd_of_dvd_pow hh)
  have h9 : ¬ 9 ∣ Nat.card (sourceOne L T V₁) := by
    have he : (Nat.card (sourceOne L T V₁)).factorization 3 = 1 :=
      (Nat.pow_right_injective (by decide : 2 ≤ 3))
        (by simpa only [pow_one] using source_local_threePart d h hU hV)
    intro hh
    have hh' : 3 ^ 2 ∣ Nat.card (sourceOne L T V₁) := hh
    have hb := (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hh'
    rw [he] at hb
    omega
  exact ⟨fun hh => h5 (hh.trans hd), fun hh => h9 (hh.trans hd)⟩

omit [Finite G] in
theorem source_twoCore_le_local_twoCore
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M) :
    H.pCoreIn 2 ≤ (sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2 :=
  Theory.GroupTheory.pCoreIn_le_of_sylow_le T le_sup_right hH.1.2

/-- The actual H-star quotient commutes with the local two-core. -/
theorem source_local_twoCore_star_eq
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M) :
    starImage H ((sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2) =
      (starImage H (sourceOne L T V₁ ⊔ (T : Subgroup G))).pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have he := map_pCoreIn_of_ker_isPGroup q hk
    ((sourceOne L T V₁ ⊔ (T : Subgroup G)).subgroupOf H)
  rwa [pCoreIn_subgroupOf 2 _ H hH.1.2] at he

include d in
/-- Literal source packet for the noncontained local-image argument. -/
theorem source_noncontained_star_inputs
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (UH H V₃))
    (hV : ¬ IsMulCommutative (VH H V))
    (hKH : K ≤ H) (hKn : H ≤ normalizer (K : Set G))
    (hout : ¬ sourceOne L T V₁ ≤ K) :
    (¬ starImage H (sourceOne L T V₁) ≤ starImage H K) ∧
      starImage H (sourceOne L T V₁) =
        ⁅starImage H (sourceOne L T V₁), starImage H (T : Subgroup G)⁆ ∧
      (¬ 5 ∣ Nat.card (starImage H (sourceOne L T V₁))) ∧
      (¬ 9 ∣ Nat.card (starImage H (sourceOne L T V₁))) ∧
      H.pCoreIn 2 ≤ (sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      starImage H ((sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2) =
        (starImage H (sourceOne L T V₁ ⊔ (T : Subgroup G))).pCoreIn 2 := by
  obtain ⟨h5, h9⟩ := source_local_star_card_constraints d hH h hU hV
  exact ⟨source_noncontained_star_not_le hH hKH hKn hout,
    source_local_star_eq_commutator d hH h hU hV, h5, h9,
    source_twoCore_le_local_twoCore hH, source_local_twoCore_star_eq hH⟩

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
