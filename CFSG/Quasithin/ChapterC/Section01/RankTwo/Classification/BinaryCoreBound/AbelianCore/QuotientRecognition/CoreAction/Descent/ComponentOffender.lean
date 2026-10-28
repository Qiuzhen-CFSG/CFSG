module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.Descent.ComponentImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.Descent.ComponentOffender.BestProjection
public import Theory.GroupTheory.NormalizedSupCard

/-!
# A component offender on the elementary MS core

Write D=[O₂(J),L]. For an actual maximum elementary E≤R, maximality identifies
C_D(E)=D∩E. Comparing E with B C_D(B), and cancelling the common action kernel
for preimages B of subgroups of the image of E, proves every best-offender
weight inequality on D. MS3 supplies such an E outside O₂(J).

The ambient action image maps onto the marked SL₃(2), with kernel the actual
image of O₂(J). Under the explicit intrinsic centrality premise, inverting the
component projection gives a retraction onto the component action image.
Its kernel is a commuting two-group, and the best offender has nontrivial
projection. The best-offender transfer then constructs an offender for the
component action on the whole core, using quadratic replacement and the
central-twist bound. The two-core action kernel may remain nontrivial.

The resulting FF conclusion retains only the explicit intrinsic centrality
premise, which the source-theorem assembly owner must discharge separately.
No module coordinates or whole-core classification are assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.5,
printed p.76, and the genuine MS hypotheses of C.1.31–34, pp.135–137.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.ComponentOffender
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite G] in
private theorem elementary_of_le (B A : Subgroup G) [IsElementaryAbelian 2 A]
    (hBA : B ≤ A) : IsElementaryAbelian 2 B := by
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · exact ⟨⟨fun x y => Subtype.ext (setLike_mul_comm (hBA x.property) (hBA y.property))⟩⟩
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (A := A) (x : G) (hBA x.property))

private theorem fixed_eq_inf (S V E : Subgroup G) [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups S) :
    V ⊓ centralizer (E : Set G) = V ⊓ E := by
  let _ : IsElementaryAbelian 2 E := hE.2.1
  let F := V ⊓ centralizer (E : Set G)
  let _ : IsElementaryAbelian 2 F := elementary_of_le F V inf_le_left
  have hj : IsElementaryAbelian 2 (E ⊔ F : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer inf_le_right
  have he : E ⊔ F = E := (Subgroup.eq_of_le_of_card_ge le_sup_left
    (hE.2.2 _ (sup_le hE.1 (inf_le_left.trans hVS)) hj)).symm
  apply le_antisymm (le_inf inf_le_left ((he ▸ le_sup_right : F ≤ E)))
  exact inf_le_inf_left V (le_centralizer_iff_isMulCommutative.mpr inferInstance)

omit [Finite G] [Finite H] in
private theorem card_kernel_map (q : G →* H) (E : Subgroup G) :
    Nat.card (E ⊓ q.ker : Subgroup G) * Nat.card (E.map q) = Nat.card E := by
  have ht := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (q.ker ⊓ E) E bot_le inf_le_right
  rw [inf_relIndex_right, relIndex_ker] at ht
  simpa only [relIndex_bot_left, inf_comm] using ht

private theorem fixed_card_comparison (S V E B : Subgroup G) [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups S)
    (hBE : B ≤ E) :
    Nat.card B * Nat.card (V ⊓ centralizer (B : Set G) : Subgroup G) ≤
      Nat.card E * Nat.card (V ⊓ centralizer (E : Set G) : Subgroup G) := by
  let _ : IsElementaryAbelian 2 E := hE.2.1
  let _ : IsElementaryAbelian 2 B := elementary_of_le B E hBE
  let F := V ⊓ centralizer (B : Set G)
  let _ : IsElementaryAbelian 2 F := elementary_of_le F V inf_le_left
  have hj : IsElementaryAbelian 2 (B ⊔ F : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer inf_le_right
  have hm := hE.2.2 _ (sup_le (hBE.trans hE.1) (inf_le_left.trans hVS)) hj
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes B F
    ((inf_le_right : F ≤ centralizer (B : Set G)).trans (Subgroup.centralizer_le_normalizer _))
  have hi : B ⊓ F ≤ V ⊓ centralizer (E : Set G) := by
    rw [fixed_eq_inf S V E hVS hE]
    exact le_inf (inf_le_right.trans inf_le_left) (inf_le_left.trans hBE)
  have hn := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hi)
  calc
    Nat.card B * Nat.card F = _ := hc
    _ ≤ Nat.card (V ⊓ centralizer (E : Set G) : Subgroup G) * Nat.card E :=
      Nat.mul_le_mul hn hm
    _ = _ := Nat.mul_comm _ _

omit [Finite H] in
private theorem image_fixed_card_comparison (S V E : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] (hVS : V ≤ S)
    (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups S)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (A : Subgroup H) (hA : A ≤ E.map q) :
    Nat.card A * Nat.card (fixedSpace
      (Representation.NormalElementaryQuotient.representation V q hq hker) A) ≤
    Nat.card (E.map q) * Nat.card (fixedSpace
      (Representation.NormalElementaryQuotient.representation V q hq hker) (E.map q)) := by
  let B := E ⊓ A.comap q
  have hb : B.map q = A := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro ha
      obtain ⟨e, he, rfl⟩ := hA ha
      exact ⟨e, ⟨he, ha⟩, rfl⟩
  have hk : B ⊓ q.ker = E ⊓ q.ker := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1.1, hx.2⟩
    · intro hx
      exact ⟨⟨hx.1, by change q x ∈ A; rw [show q x = 1 from hx.2]; exact A.one_mem⟩, hx.2⟩
  have hc := fixed_card_comparison S V E B hVS hE inf_le_left
  have hbcard := card_kernel_map q B
  rw [hk, hb] at hbcard
  have hecard := card_kernel_map q E
  rw [← hbcard, ← hecard] at hc
  have hpos : 0 < Nat.card (E ⊓ q.ker : Subgroup G) := Nat.card_pos
  have hc' : Nat.card A * Nat.card (V ⊓ centralizer (B : Set G) : Subgroup G) ≤
      Nat.card (E.map q) * Nat.card (V ⊓ centralizer (E : Set G) : Subgroup G) := by
    nlinarith
  rw [← Nat.card_congr (Representation.NormalElementaryQuotient.fixedSpaceEquiv V q hq hker B),
    ← Nat.card_congr (Representation.NormalElementaryQuotient.fixedSpaceEquiv V q hq hker E),
    hb] at hc'
  exact hc'

private theorem maxElementary_isBestOffender (S V E : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] (hVS : V ≤ S)
    (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups S)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G)) (hne : ¬ E ≤ q.ker) :
    IsBestOffender (Representation.NormalElementaryQuotient.representation V q hq hker)
      (E.map q) := by
  let _ : IsElementaryAbelian 2 E := hE.2.1
  let _ : IsElementaryAbelian 2 (E.map q) := IsElementaryAbelian.map q
  have helem : IsElementaryTwo (E.map q) :=
    ⟨fun he => hne ((map_eq_bot_iff E).mp he), inferInstance⟩
  refine ⟨helem, ?_⟩
  intro A hA
  let _ : IsElementaryAbelian 2 A := elementary_of_le A (E.map q) hA
  have hc := image_fixed_card_comparison S V E hVS hE q hq hker A hA
  have hcard (B : Subgroup H) [IsElementaryAbelian 2 B] : Nat.card B = 2 ^ rank B := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
    rw [rank, hn, Nat.log_pow (by decide : 1 < 2)]
  have hfixed (B : Subgroup H) : Nat.card (fixedSpace
      (Representation.NormalElementaryQuotient.representation V q hq hker) B) =
      2 ^ Module.finrank (ZMod 2) (fixedSpace
        (Representation.NormalElementaryQuotient.representation V q hq hker) B) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hcard A, hcard (E.map q), hfixed A, hfixed (E.map q), ← pow_add, ← pow_add] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
end CFSG.Quasithin.ChapterC.BinaryMS.ComponentOffender


open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R)

/-- The marked matrix quotient factors through the actual ambient action on D. -/
noncomputable def Input.coreAmbientProjection :
    h.coreAmbientConjugation.range →* AbelianCore.QuotientRecognition.SL :=
  h.coreAmbientConjugation.rangeRestrict.liftOfSurjective
    h.coreAmbientConjugation.rangeRestrict_surjective ⟨h.coreProjection, by
      rw [h.coreAmbientConjugation_rangeKernel, h.coreProjection_kernel]
      exact h.core_centralizer_le⟩

/-- The factorization retains each literal ambient representative. -/
theorem Input.coreAmbientProjection_apply (j : J) :
    h.coreAmbientProjection (h.coreAmbientConjugation.rangeRestrict j) =
      h.coreProjection j := by
  simp only [Input.coreAmbientProjection, MonoidHom.liftOfSurjective,
    MonoidHom.liftOfRightInverse_comp_apply]

/-- The remaining kernel is exactly the ambient two-core action image. -/
theorem Input.coreAmbientProjection_kernel :
    h.coreAmbientProjection.ker = (pCore 2 J).map h.coreAmbientConjugation.rangeRestrict := by
  ext a
  obtain ⟨j, rfl⟩ := h.coreAmbientConjugation.rangeRestrict_surjective a
  constructor
  · intro hj
    have hj' : j ∈ h.coreProjection.ker := by
      change h.coreProjection j = 1
      exact (h.coreAmbientProjection_apply j).symm.trans hj
    rw [h.coreProjection_kernel] at hj'
    exact mem_map_of_mem _ hj'
  · rintro ⟨n, hn, he⟩
    change h.coreAmbientProjection (h.coreAmbientConjugation.rangeRestrict j) = 1
    rw [← he, h.coreAmbientProjection_apply]
    have hn' : n ∈ h.coreProjection.ker := by rwa [h.coreProjection_kernel]
    exact hn'

/-- Restriction recovers the previously constructed component projection. -/
theorem Input.coreAmbientProjection_component (a : h.coreConjugation.range) :
    h.coreAmbientProjection (h.coreComponentEmbedding a) = h.coreComponentProjection a := by
  obtain ⟨l, rfl⟩ := h.coreConjugation.rangeRestrict_surjective a
  rw [h.coreComponentEmbedding_apply, h.coreAmbientProjection_apply,
    h.coreProjection_component, h.coreComponentProjection_apply]

/-- Intrinsic centrality identifies the actual component image with the marked SL₃(2). -/
noncomputable def Input.coreOffenderEquiv
    (hz : commutatorCore L ≤ centralizer ((pCore 2 L).map L.subtype : Set J)) :
    h.coreConjugation.range ≃* AbelianCore.QuotientRecognition.SL :=
  MulEquiv.ofBijective h.coreComponentProjection
    ⟨h.componentCore_centralizes_iff_componentProjection_injective.mp hz,
      h.coreComponentProjection_surjective⟩

/-- Project ambient actions onto the actual component image, retaining the two-core kernel. -/
noncomputable def Input.coreActionRetraction
    (hz : commutatorCore L ≤ centralizer ((pCore 2 L).map L.subtype : Set J)) :
    h.coreAmbientConjugation.range →* h.coreConjugation.range :=
  (h.coreOffenderEquiv hz).symm.toMonoidHom.comp h.coreAmbientProjection

/-- The projection is a left inverse to the literal component embedding. -/
theorem Input.coreActionRetraction_component
    (hz : commutatorCore L ≤ centralizer ((pCore 2 L).map L.subtype : Set J))
    (a : h.coreConjugation.range) :
    h.coreActionRetraction hz (h.coreComponentEmbedding a) = a := by
  change (h.coreOffenderEquiv hz).symm
    (h.coreAmbientProjection (h.coreComponentEmbedding a)) = a
  rw [h.coreAmbientProjection_component]
  exact (h.coreOffenderEquiv hz).symm_apply_apply a

/-- The retraction kills precisely the image of O₂(J), which need not be trivial. -/
theorem Input.coreActionRetraction_kernel
    (hz : commutatorCore L ≤ centralizer ((pCore 2 L).map L.subtype : Set J)) :
    (h.coreActionRetraction hz).ker =
      (pCore 2 J).map h.coreAmbientConjugation.rangeRestrict := by
  rw [← h.coreAmbientProjection_kernel]
  ext a
  change (h.coreOffenderEquiv hz).symm (h.coreAmbientProjection a) = 1 ↔
    h.coreAmbientProjection a = 1
  exact (h.coreOffenderEquiv hz).symm.map_eq_one_iff

/-- Projecting an ambient subgroup uses the original matrix marking on J. -/
theorem Input.coreActionRetraction_map
    (hz : commutatorCore L ≤ centralizer ((pCore 2 L).map L.subtype : Set J))
    (E : Subgroup J) :
    (E.map h.coreAmbientConjugation.rangeRestrict).map (h.coreActionRetraction hz) =
      (E.map h.coreProjection).map (h.coreOffenderEquiv hz).symm.toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  apply MonoidHom.ext
  intro j
  change (h.coreOffenderEquiv hz).symm
    (h.coreAmbientProjection (h.coreAmbientConjugation.rangeRestrict j)) = _
  rw [h.coreAmbientProjection_apply]
  rfl

/-- A subgroup outside O₂(J) has nontrivial component projection. -/
theorem Input.coreActionRetraction_map_ne_bot
    (hz : commutatorCore L ≤ centralizer ((pCore 2 L).map L.subtype : Set J))
    {E : Subgroup J} (hE : ¬ E ≤ pCore 2 J) :
    (E.map h.coreAmbientConjugation.rangeRestrict).map (h.coreActionRetraction hz) ≠ ⊥ := by
  rw [h.coreActionRetraction_map]
  intro he
  have hb : E.map h.coreProjection = ⊥ := by
    apply Subgroup.map_injective (f := (h.coreOffenderEquiv hz).symm.toMonoidHom)
      (h.coreOffenderEquiv hz).symm.injective
    simpa only [Subgroup.map_bot] using he
  apply hE
  have hh := (map_eq_bot_iff E).mp hb
  rwa [h.coreProjection_kernel] at hh

end CFSG.Quasithin.ChapterC.BinaryMS
namespace CFSG.Quasithin.ChapterC.BinaryMS
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R)
variable [IsElementaryAbelian 2 (commutatorCore L)]

omit [IsElementaryAbelian 2 (commutatorCore L)] in
/-- The kernel discarded by component projection is a two-group. -/
theorem Input.coreActionRetraction_kernel_isPGroup
    (hz : commutatorCore L ≤ centralizer ((pCore 2 L).map L.subtype : Set J)) :
    IsPGroup 2 (h.coreActionRetraction hz).ker := by
  rw [h.coreActionRetraction_kernel]
  exact pCore_isPGroup.map _

/-- This two-group kernel commutes with the component, without being assumed trivial. -/
theorem Input.coreActionRetraction_kernel_centralizes
    (hz : commutatorCore L ≤ centralizer ((pCore 2 L).map L.subtype : Set J)) :
    (h.coreActionRetraction hz).ker ≤ centralizer (h.coreComponentEmbedding.range : Set _) := by
  rw [h.coreActionRetraction_kernel]
  exact commutator_eq_bot_iff_le_centralizer.mp
    (h.abelianCore_componentImage_commutes_twoCore inferInstance)

/-- B.2.5 strengthens maximum-elementary counting to every subgroup weight comparison. -/
theorem Input.exists_coreAmbientBestOffender :
    ∃ E ∈ Stellmacher.elementaryAbelianMaxSubgroups R, ¬ E ≤ pCore 2 J ∧
      IsBestOffender h.coreAmbientRepresentation (E.map h.coreAmbientConjugation.rangeRestrict) := by
  let := h.component_normal
  obtain ⟨E, hE, hEN⟩ := h.exists_maxElementary_not_le_core
  have hDR : commutatorCore L ≤ R :=
    h.commutatorCore_le.trans (h.componentCore_eq_inf.le.trans
      (inf_le_left.trans h.radical.twoCore_le))
  refine ⟨E, hE, hEN, ?_⟩
  have hrep : h.coreAmbientRepresentation =
      Representation.NormalElementaryQuotient.representation (commutatorCore L)
        h.coreAmbientConjugation.rangeRestrict
        h.coreAmbientConjugation.rangeRestrict_surjective
        h.coreAmbientConjugation_rangeKernel := by
    apply MonoidHom.ext
    intro a
    apply LinearMap.ext
    intro v
    obtain ⟨j, rfl⟩ := h.coreAmbientConjugation.rangeRestrict_surjective a
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (h.coreAmbientRepresentation_apply j v).trans
      (Representation.NormalElementaryQuotient.representation_apply _ _ _ _ j v).symm
  rw [hrep]
  apply ComponentOffender.maxElementary_isBestOffender R (commutatorCore L) E hDR hE
    h.coreAmbientConjugation.rangeRestrict h.coreAmbientConjugation.rangeRestrict_surjective
    h.coreAmbientConjugation_rangeKernel
  rw [h.coreAmbientConjugation_rangeKernel]
  exact fun hc => hEN (hc.trans h.core_centralizer_le)

/-- MS3 supplies a best offender whose projection to the component is nontrivial. -/
theorem Input.exists_coreAmbientBestOffender_nontrivial_projection
    (hz : commutatorCore L ≤ centralizer ((pCore 2 L).map L.subtype : Set J)) :
    ∃ A : Subgroup h.coreAmbientConjugation.range,
      IsBestOffender h.coreAmbientRepresentation A ∧
      A.map (h.coreActionRetraction hz) ≠ ⊥ := by
  obtain ⟨E, _, hEN, hbest⟩ := h.exists_coreAmbientBestOffender
  exact ⟨E.map h.coreAmbientConjugation.rangeRestrict, hbest,
    h.coreActionRetraction_map_ne_bot hz hEN⟩

/-- Intrinsic centrality gives an offender for the component action on the
whole elementary core, by best-offender transfer across the commuting kernel. -/
theorem Input.coreComponentRepresentation_isFFModule_of_centralizes
    (hz : commutatorCore L ≤ centralizer ((pCore 2 L).map L.subtype : Set J)) :
    IsFFModule h.coreComponentRepresentation := by
  have heq : h.coreAmbientRepresentation.comp h.coreComponentEmbedding =
      h.coreComponentRepresentation := by
    apply MonoidHom.ext
    intro a
    apply LinearMap.ext
    intro v
    obtain ⟨l, rfl⟩ := h.coreConjugation.rangeRestrict_surjective a
    change h.coreAmbientRepresentation
      (h.coreComponentEmbedding (h.coreConjugation.rangeRestrict l)) v = _
    rw [h.coreComponentEmbedding_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((h.coreAmbientRepresentation
      (h.coreAmbientConjugation.rangeRestrict l) v).toMul : J) =
      ((h.coreComponentRepresentation (h.coreConjugation.rangeRestrict l)
        (Additive.ofMul v.toMul)).toMul : J)
    rw [h.coreAmbientRepresentation_apply, h.coreComponentRepresentation_apply]
    exact (h.coreConjugate_val l v.toMul).symm
  obtain ⟨A, hA, hproj⟩ := h.exists_coreAmbientBestOffender_nontrivial_projection hz
  rw [← heq]
  apply ComponentOffender.BestProjection.isFFModule_of_bestOffender_nontrivial_projection
    h.coreAmbientRepresentation h.coreComponentEmbedding (h.coreActionRetraction hz)
    (h.coreActionRetraction_component hz) (h.coreActionRetraction_kernel_centralizes hz)
    (h.coreOffenderEquiv hz) (h.coreActionRetraction_kernel_isPGroup hz)
    h.coreAmbientRepresentation_injective _ hA hproj
  rw [heq]
  exact h.coreComponentRepresentation_full_commutator
end CFSG.Quasithin.ChapterC.BinaryMS
