module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.SecondKernel
public import Theory.GroupTheory.CentralBinaryKernelBound

/-!
# Reducing the quintic core bound to its radius-two kernel

Put Q=O₂(H), U=⟨Vᴴ⟩ and C=C_H(U). The original source action gives
16|C|≤|Q|. Central commutator duality, using [Q,U]≤Z and |Z|=2,
gives 2|Q|≤|C|². Hence |Q|≤512 if and only if |C|≤32.
The earlier source identifies C with the literal radius-two ball kernel.
Since C is a two-group, either |Q|=512 and |C|=32, or |Q|≥1024 and
|C|≥64. No quotient-model choice, path transitivity or endpoint
identification is assumed in this reduction.

The actual whole-parabolic consumer is `QuinticFirstParabolic.lean`.
Exclusion of the large-kernel branch, and thus final discharge of the
core upper bound, remains with qt-e-quintic-first-parabolic.
Source: Aschbacher--Smith F.9.7, p.321;14.2.6 and14.2.20--21,
pp.982,988--989. The radius-two kernel identity uses F.3.2--4.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

private theorem source_span_centralizer_le_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G) ≤ H.pCoreIn 2 := by
  rw [← source_quintic_crossing_core_normalCore hG T hempty hM hu hmany hcard e H hH]
  exact (map_mono (f := H.subtype)
    ((H.pCoreIn 2 ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf H).normalCore_le).trans (by
      rw [map_subgroupOf_eq_of_le (inf_le_left.trans (pCoreIn_le 2 H))]
      exact inf_le_left)

/-- The original action kernel bounds the core on both sides; the upper bound uses commutator duality. -/
theorem source_span_centralizer_order_bounds
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let C := H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G)
    16 * Nat.card C ≤ Nat.card (pCore 2 H) ∧
      2 * Nat.card (pCore 2 H) ≤ Nat.card C ^ 2 := by
  let Q := H.pCoreIn 2
  let U := conjugateSpanBy (localModule T M) H
  let Z := centralInvolutions T
  let C := H ⊓ centralizer (U : Set G)
  have hCQ : C ≤ Q := source_span_centralizer_le_core
    hG T hempty hM hu hmany hcard e H hH
  let : IsElementaryAbelian 2 U :=
    (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).1
  obtain ⟨he, F, hp, _, _, hloc⟩ := source_lemma_14_2_6 hG T hempty hM hu hmany hcard e
  let := he
  obtain ⟨_, hl, _, _, _, _⟩ := hloc H hH.1
  have hUQ : U ≤ Q := by
    have hh := hl.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [rankTwoSeed_eq_localModule] using hh
  have hcomm : ⁅Q, U⁆ ≤ Z := by
    have hh := hl.commutator_U_core_le_point
    change ⁅conjugateSpanBy (rankTwoSeed T M) H, H.pCoreIn 2⁆ ≤ F.Vi 1 at hh
    simpa only [rankTwoSeed_eq_localModule, hp, commutator_comm] using hh
  have hZU : Z ≤ U := (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  have hQZ : Q ≤ centralizer (Z : Set G) := (pCoreIn_le 2 H).trans
    (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  let UQ := U.subgroupOf Q
  let ZQ := Z.subgroupOf Q
  let : IsElementaryAbelian 2 UQ := IsElementaryAbelian.subgroupOf hUQ
  let : UQ.Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 H).trans (le_normalizer_conjugateSpanBy _ _))
  have hZc : ZQ ≤ center Q := by
    intro z hz
    apply mem_center_iff.mpr
    intro q
    exact Subtype.ext ((mem_centralizer_iff.mp (hQZ q.property) _ hz).symm)
  have hZcard : Nat.card ZQ = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (hZU.trans hUQ)).toEquiv]
    exact plane_centralInvolutions_card T M hM.1.2 hcard e
  have hcommQ : ⁅(⊤ : Subgroup Q), UQ⁆ ≤ ZQ := by
    apply commutator_le.mpr
    intro q _ u hu
    change ⁅(q : G), (u : G)⁆ ∈ Z
    exact hcomm (commutator_mem_commutator q.property hu)
  have hCeq : centralizer (UQ : Set Q) = C.subgroupOf Q := by
    ext q
    constructor
    · intro hq
      refine ⟨pCoreIn_le 2 H q.property, ?_⟩
      intro u hu
      exact congrArg Q.subtype (hq ⟨u, hUQ hu⟩ hu)
    · intro hq u hu
      exact Subtype.ext (hq.2 u hu)
  have hb := twice_card_le_centralizer_card_sq_of_central_binary_commutators
    UQ ZQ (fun _ hz => hZU hz) hZc hZcard hcommQ
  rw [hCeq, Nat.card_congr (subgroupOfEquivOfLe hCQ).toEquiv,
    show Nat.card Q = Nat.card (pCore 2 H) from card_map_of_injective H.subtype_injective] at hb
  exact ⟨source_quintic_action_core_lower hG T hempty hM hu hmany hcard e H hH hi, hb⟩

/-- The missing intrinsic core bound is equivalent to a bound on the actual span centralizer. -/
theorem source_core_upper_iff_span_centralizer_upper
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    Nat.card (pCore 2 H) ≤ 512 ↔
      Nat.card (H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G) : Subgroup G) ≤ 32 := by
  obtain ⟨hl, hu⟩ := source_span_centralizer_order_bounds hG T hempty hM hu hmany hcard e H hH hi
  constructor
  · omega
  · intro hc
    nlinarith

/-- The power-of-two kernel order separates the recognized endpoint from every larger core. -/
theorem source_span_centralizer_order_gap
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let C := H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G)
    (Nat.card (pCore 2 H) = 512 ∧ Nat.card C = 32) ∨
      (1024 ≤ Nat.card (pCore 2 H) ∧ 64 ≤ Nat.card C) := by
  let C := H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G)
  have hCQ : C ≤ H.pCoreIn 2 := source_span_centralizer_le_core
    hG T hempty hM hu hmany hcard e H hH
  have hC2 : IsPGroup 2 C := (isPGroup_pCoreIn 2 H).of_injective
    (inclusion hCQ) (inclusion_injective hCQ)
  obtain ⟨n, hn⟩ := hC2.exists_card_eq
  obtain ⟨hl, hupp⟩ := source_span_centralizer_order_bounds hG T hempty hM hu hmany hcard e H hH hi
  change 16 * Nat.card C ≤ Nat.card (pCore 2 H) at hl
  change 2 * Nat.card (pCore 2 H) ≤ Nat.card C ^ 2 at hupp
  have hQlower : 512 ≤ Nat.card (pCore 2 H) := by
    have hh := source_quintic_core_lower hG T hempty hM hu hmany hcard e H hH hi
    have hU := (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).2
    rcases hU with hU | hU <;> rw [hU] at hh <;> omega
  by_cases hc : Nat.card C ≤ 32
  · have hq := (source_core_upper_iff_span_centralizer_upper
      hG T hempty hM hu hmany hcard e H hH hi).mpr hc
    left
    have hceq : Nat.card C = 32 := by nlinarith
    exact ⟨by omega, hceq⟩
  · have hn6 : 6 ≤ n := by
      by_contra! hh
      have hb := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show n ≤ 5 by omega)
      omega
    have hc64 : 64 ≤ Nat.card C := by
      rw [hn]
      exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn6
    exact Or.inr ⟨by omega, hc64⟩

/-- The equivalence uses the literal coset-geometry kernel and its original ambient embedding. -/
theorem source_core_upper_iff_second_kernel_upper
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    Nat.card (pCore 2 H) ≤ 512 ↔
      Nat.card (ChapterF.Section07.Geometry.ballKernel X H
        (ChapterF.Section07.Geometry.base X H true) 2) ≤ 32 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  have hh := congrArg (fun A : Subgroup G => Nat.card A)
    (source_quintic_second_ball_kernel hG T hempty hM hu hmany hcard e H hH hi)
  rw [card_map_of_injective (X ⊔ H).subtype_injective] at hh
  change Nat.card (pCore 2 H) ≤ 512 ↔ _
  rw [hh]
  exact source_core_upper_iff_span_centralizer_upper hG T hempty hM hu hmany hcard e H hH hi

/-- The original radius-two kernel has order 32 at the small core, or at least 64. -/
theorem source_second_kernel_order_gap
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let K := ChapterF.Section07.Geometry.ballKernel X H
      (ChapterF.Section07.Geometry.base X H true) 2
    (Nat.card (pCore 2 H) = 512 ∧ Nat.card K = 32) ∨
      (1024 ≤ Nat.card (pCore 2 H) ∧ 64 ≤ Nat.card K) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  have hh := congrArg (fun A : Subgroup G => Nat.card A)
    (source_quintic_second_ball_kernel hG T hempty hM hu hmany hcard e H hH hi)
  rw [card_map_of_injective (X ⊔ H).subtype_injective] at hh
  dsimp only
  rw [hh]
  exact source_span_centralizer_order_gap hG T hempty hM hu hmany hcard e H hH hi

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic
