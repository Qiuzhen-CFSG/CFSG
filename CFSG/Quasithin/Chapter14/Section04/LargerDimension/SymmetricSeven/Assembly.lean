module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.SymmetricSeven.ModuleCalculation
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.SymmetricSeven.PermutationCalculation
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu
public import Theory.Representation.BinaryOffender.ConjugationImage
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# The conditional source proof of Lemma 14.4.11

An actual S₇ conjugate-pair action on U/Z(U) supplies two moved planes and
fixes the third residual's distinguished line. The extraspecial central
kernel lifts each plane to an eight-element commutator. The earlier bound
[W,Wᵍ] ≤ E, together with the index-two hyperplane W in U, places both
commutators in E. Relative normality and order eight identify Wᵍ* with the
three disjoint transpositions. The exhaustive residual catalogue then gives
exactly two members of Y, and the literal overlap quotient is S₃ × S₃.

`CentralAction` retains the actual quotient map U → U/Z(U), its coordinates,
and its conjugation equation over H → H/O₂(H) → S₇. `EarlierGeometry` lists
the independent earlier local inputs: the marked T-fixed line, the central
line containments, W's index, Wᵍ ≤ T, 12.8.11(1)'s commutator bound,
12.8.12(2)'s relative normality, and 14.4.2's order eight. It contains no actor
calculation or family conclusion. Their discharge remains with the source
assembly in `qt-14-04-large-dimension`.

`lemma_14_4_11` chooses Sylow-compatible coordinates, transports the given
action, and uses the literal pointwise-stabilizer residuals. Here W=C_U(V₂),
Wᵍ=g⁻¹Wg and E=W∩Wᵍ are actual ambient subgroups. `exists_partner` supplies
the distinct partner and line-vertex quotient needed by 14.4.13, using only
the earlier L₁-membership from 14.4.8(1). The displacement inclusions avoid
the printed final equality with a T-fixed vector, which is not needed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 14.4.11, printed p.1011/PDF p.1028; case 14.4.2(4), printed p.1006.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.AlternatingSevenConjugatePair
open Representation.AlternatingSevenConjugatePair.SourceLineGeometry
open Theory.SpecificGroups.SymmetricSeven.LocalResidualModels
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.SymmetricSeven

variable {G Q : Type*} [Group G] [Group Q] [IsMulCommutative Q]
  [Module (ZMod 2) (Additive Q)]

/-- A marking of the actual central quotient, with its literal conjugation action. -/
structure CentralAction (H U : Subgroup G) (q : H →* S7) where
  coordinates : (U ⧸ center U) ≃* Q
  pair : Pair (Additive Q)
  normalizes : H ≤ normalizer (U : Set G)
  equivariant : ∀ (h : H) (u : U),
    pair.representation (q h) (Additive.ofMul (coordinates (QuotientGroup.mk' (center U) u))) =
      Additive.ofMul (coordinates (QuotientGroup.mk' (center U)
        ⟨(h : G) * u * (h : G)⁻¹,
          le_normalizer_iff.mp normalizes h h.property u u.property⟩))

namespace CentralAction
variable {H U : Subgroup G} {q : H →* S7} (d : CentralAction (Q := Q) H U q)

def projection : U →* Q :=
  d.coordinates.toMonoidHom.comp (QuotientGroup.mk' (center U))

theorem projection_surjective : Function.Surjective d.projection :=
  d.coordinates.surjective.comp (QuotientGroup.mk'_surjective _)

theorem projection_ker : d.projection.ker = center U := by
  rw [projection, MonoidHom.ker_comp_of_injective _ _ d.coordinates.injective,
    QuotientGroup.ker_mk']

def image (P : Subgroup G) : Submodule (ZMod 2) (Additive Q) :=
  quotientImage U d.projection P

def actor (q : H →* S7) (X : Subgroup G) (hX : X ≤ H) : X →* S7 :=
  q.comp (Subgroup.inclusion hX)

theorem actor_range (X : Subgroup G) (hX : X ≤ H) :
    (actor q X hX).range = (X.subgroupOf H).map q := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y, hX y.property⟩, y.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

theorem conjugation (X : Subgroup G) (hX : X ≤ H) (x : X) (u : U) :
    d.pair.representation (actor q X hX x) (Additive.ofMul (d.projection u)) =
      Additive.ofMul (d.projection ⟨(x : G) * u * (x : G)⁻¹,
        le_normalizer_iff.mp (hX.trans d.normalizes) x x.property u u.property⟩) :=
  d.equivariant ⟨x, hX x.property⟩ u

theorem image_commutator (P X : Subgroup G) (hP : P ≤ U) (hX : X ≤ H) :
    d.image ⁅P,X⁆ = subspaceCommutator d.pair.representation (d.image P)
      ((X.subgroupOf H).map q) := by
  rw [image, quotientImage_commutator d.pair.representation U P X
    (hX.trans d.normalizes) hP (actor q X hX) d.projection d.projection_surjective
    (d.conjugation X hX), actor_range]
  rfl

theorem image_mono {P R : Subgroup G} (h : P ≤ R) : d.image P ≤ d.image R := by
  rintro v ⟨u, hu, rfl⟩
  exact ⟨u, h hu, rfl⟩

theorem le_of_image_le (P E : Subgroup G) (hPU : P ≤ U)
    (hZE : center U ≤ E.subgroupOf U) (h : d.image P ≤ d.image E) : P ≤ E := by
  have hm : (P.subgroupOf U).map d.projection ≤ (E.subgroupOf U).map d.projection := h
  have hc := (map_le_iff_le_comap.mp hm)
  rw [comap_map_eq, d.projection_ker, sup_eq_left.mpr hZE] at hc
  intro x hx
  exact hc (show (⟨x,hPU hx⟩ : U) ∈ P.subgroupOf U from hx)

theorem image_card [Finite Q] (P : Subgroup G) :
    Nat.card ((P.subgroupOf U).map d.projection) =
      2 ^ Module.finrank (ZMod 2) (d.image P) := by
  let e : ((P.subgroupOf U).map d.projection) ≃ d.image P := {
    toFun u := ⟨Additive.ofMul u, u.property⟩
    invFun u := ⟨u.val.toMul, u.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  let _ := Fintype.ofFinite (d.image P)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

theorem lifted_actor_image (A : Subgroup H) :
    (((A.map H.subtype).subgroupOf H).map q) = A.map q := by
  rw [Subgroup.subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]

theorem lifted_moved_image (A : Subgroup H) (P : Subgroup G) (hPU : P ≤ U) :
    d.image (movedSpace P (A.map H.subtype)) =
      subspaceCommutator d.pair.representation (d.image P) (A.map q) := by
  rw [movedSpace, d.image_commutator P _ hPU (map_subtype_le _), lifted_actor_image]

theorem displacement_le_image (W N : Subgroup G)
    (hUW : ⁅U,N⁆ ≤ W) (t : S7) (ht : t ∈ (N.subgroupOf H).map q) :
    SourceLineGeometry.displacement d.pair.representation t ≤ d.image W := by
  rintro v ⟨w, rfl⟩
  obtain ⟨h, hh, rfl⟩ := ht
  obtain ⟨u, hu⟩ := d.projection_surjective w.toMul
  have hw : w = Additive.ofMul (d.projection u) := congrArg Additive.ofMul hu.symm
  subst w
  change d.pair.representation (q h) (Additive.ofMul (d.projection u)) -
    Additive.ofMul (d.projection u) ∈ d.image W
  have he := d.equivariant h u
  change d.pair.representation (q h) (Additive.ofMul (d.projection u)) = _ at he
  rw [he]
  let c : U := ⟨(h : G) * u * (h : G)⁻¹,
    le_normalizer_iff.mp d.normalizes h h.property u u.property⟩
  change d.projection c / d.projection u ∈ (W.subgroupOf U).map d.projection
  rw [div_eq_mul_inv]
  refine ⟨c * u⁻¹, ?_, by simp⟩
  apply hUW
  change ⁅(h : G), (u : G)⁆ ∈ ⁅U,N⁆
  rw [commutator_comm]
  exact commutator_mem_commutator hh u.property

end CentralAction


/-- The earlier local geometry, before the S₇ actor calculation. The image
normality is 12.8.12(2), its order is 14.4.2, and the commutator bound is
12.8.11(1). No actor, moved-plane or family conclusion is a field. -/
structure EarlierGeometry {H U : Subgroup G} {q : H →* S7}
    (d : CentralAction (Q := Q) H U q) (T V₂ W N : Subgroup G) where
  U_le_T : U ≤ T
  V₂_le_U : V₂ ≤ U
  center_le_V₂ : center U ≤ V₂.subgroupOf U
  W_le_U : W ≤ U
  W_index : W.relIndex U = 2
  N_le_T : N ≤ T
  center_le_E : center U ≤ (W ⊓ N).subgroupOf U
  commutator_le_E : ⁅W,N⁆ ≤ W ⊓ N
  s : Additive Q
  nonzero : s ≠ 0
  marked : d.image V₂ = line s
  fixed : ∀ t ∈ (T.subgroupOf H).map q, d.pair.representation t s = s
  image_card : Nat.card ((N.subgroupOf H).map q) = 8
  image_normal : ∀ t : S7, d.pair.representation t s = s →
    t ∈ normalizer (((N.subgroupOf H).map q) : Set S7)

private theorem commutator_subspace_mono {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) S7 V)
    {P R : Submodule (ZMod 2) V} (h : P ≤ R) (A : Subgroup S7) :
    subspaceCommutator ρ P A ≤ subspaceCommutator ρ R A := by
  apply Submodule.span_mono
  rintro v ⟨a, ha, p, hp, rfl⟩
  exact ⟨a, ha, p, h hp, rfl⟩

private theorem B8_compatibility :
    Theory.SpecificGroups.SymmetricSeven.ResidualTripleGeometry.B8 = B8 := by
  rw [Theory.SpecificGroups.SymmetricSeven.ResidualTripleGeometry.B8_eq_closure, B8]
  congr 1
  ext x
  simp only [a, b, c, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

namespace EarlierGeometry
variable [Finite Q]
variable {H T U V₂ W N : Subgroup G} {q : H →* S7}
  {d : CentralAction (Q := Q) H U q} (h : EarlierGeometry d T V₂ W N)
  (hT : (T.subgroupOf H).map q = standardTwo)

include h hT

omit [Finite Q] in
theorem fixed_standard : ∀ t ∈ standardTwo, d.pair.representation t h.s = h.s :=
  hT ▸ h.fixed

/-- The actual image W^{g*} is exactly the subgroup generated by the three swaps. -/
theorem image_eq_B8 : (N.subgroupOf H).map q = B8 := by
  rw [← B8_compatibility]
  apply Theory.SpecificGroups.SymmetricSeven.ResidualTripleGeometry.normal_eight_eq_B8
  · have hm := map_mono (f := q) (show N.subgroupOf H ≤ T.subgroupOf H from fun _ hx => h.N_le_T hx)
    exact hm.trans (hT ▸ (show standardTwo ≤ synthemeOvergroup from inf_le_right))
  · intro t ht
    exact h.image_normal t ((stabilizer_iff d.pair h.s h.nonzero (h.fixed_standard hT) t).mpr ht)
  · exact h.image_card

/-- Both swap displacements lie in the actual hyperplane W/Z(U). -/
theorem displacement_le_W (hTH : T ≤ H) (t : S7) (ht : t ∈ B8) :
    SourceLineGeometry.displacement d.pair.representation t ≤ d.image W := by
  apply d.displacement_le_image W N
  · exact commutator_le_of_normalized_index_two U W N h.W_le_U h.W_index
      ((h.N_le_T.trans hTH).trans d.normalizes)
      (le_normalizer_iff_commutator_le_left.mpr (h.commutator_le_E.trans inf_le_left))
  · rwa [h.image_eq_B8 hT]

/-- The earlier cross-commutator bound controls the whole linear commutator in W. -/
theorem W_commutator_le_E (hTH : T ≤ H) :
    subspaceCommutator d.pair.representation (d.image W) B8 ≤ d.image (W ⊓ N) := by
  rw [← h.image_eq_B8 hT, ← d.image_commutator W N h.W_le_U (h.N_le_T.trans hTH)]
  exact d.image_mono h.commutator_le_E

variable [Finite G] [IsExtraspecial 2 U]

/-- The two computed planes lift to eight-element commutator subgroups in E. -/
theorem actor_calculation (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (hTH : T ≤ H) :
    (Nat.card (movedSpace V₂ ((firstActor q).map H.subtype)) = 8 ∧
      movedSpace V₂ ((firstActor q).map H.subtype) ≤ W ⊓ N) ∧
    (Nat.card (movedSpace V₂ ((secondActor q).map H.subtype)) = 8 ∧
      movedSpace V₂ ((secondActor q).map H.subtype) ≤ W ⊓ N) := by
  have firstX : (firstActor q).map H.subtype ∈ XFamily H T := by
    simpa only [XFamily, Set.mem_ofPred_eq, range_subtype, map_subgroupOf_eq_of_le hTH] using
      threeExtension_map H.subtype H.subtype_injective (T.subgroupOf H) (firstActor q)
        (firstActor_mem_XFamily q hq hk _ hT)
  have secondX : (secondActor q).map H.subtype ∈ XFamily H T := by
    simpa only [XFamily, Set.mem_ofPred_eq, range_subtype, map_subgroupOf_eq_of_le hTH] using
      threeExtension_map H.subtype H.subtype_injective (T.subgroupOf H) (secondActor q)
        (secondActor_mem_XFamily q hq hk _ hT)
  have firstImage : d.image (movedSpace V₂ ((firstActor q).map H.subtype)) =
      movedLine d.pair.representation h.s cubicOvergroup := by
    rw [d.lifted_moved_image _ _ h.V₂_le_U, h.marked, firstActor, residualLift_map q hq]
    rfl
  have secondImage : d.image (movedSpace V₂ ((secondActor q).map H.subtype)) =
      movedLine d.pair.representation h.s duadOvergroup := by
    rw [d.lifted_moved_image _ _ h.V₂_le_U, h.marked, secondActor, residualLift_map q hq]
    rfl
  have hc (X : Subgroup G) (hX : X ∈ XFamily H T)
      (hdim : Module.finrank (ZMod 2) (d.image (movedSpace V₂ X)) = 2) :
      Nat.card (movedSpace V₂ X) = 8 := by
    apply Mathieu.movedSpace_card_eight_of_extraspecial_image H T U V₂ X hX
      h.U_le_T d.normalizes h.V₂_le_U h.center_le_V₂ d.projection d.projection_ker
    rw [d.image_card, hdim]
    rfl
  have hle (X : Subgroup G) (hX : X ∈ XFamily H T)
      (hb : d.image (movedSpace V₂ X) ≤ d.image (W ⊓ N)) : movedSpace V₂ X ≤ W ⊓ N := by
    apply d.le_of_image_le _ _ _ h.center_le_E hb
    exact (commutator_mono h.V₂_le_U le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hX.le_H.trans d.normalizes))
  refine ⟨⟨hc _ firstX ?_, hle _ firstX ?_⟩, ⟨hc _ secondX ?_, hle _ secondX ?_⟩⟩
  · rw [firstImage]
    exact first_moved_finrank d.pair h.s h.nonzero
  · rw [firstImage]
    exact (first_moved_le d.pair h.s (h.fixed_standard hT)).trans
      ((commutator_subspace_mono _ (h.displacement_le_W hT hTH a
        (subset_closure (Or.inl rfl))) B8).trans (h.W_commutator_le_E hT hTH))
  · rw [secondImage]
    exact second_moved_finrank d.pair h.s h.nonzero (h.fixed_standard hT)
  · rw [secondImage]
    exact (second_moved_le d.pair h.s (h.fixed_standard hT)).trans
      ((commutator_subspace_mono _ (h.displacement_le_W hT hTH c
        (subset_closure (Or.inr (Or.inr rfl)))) B8).trans (h.W_commutator_le_E hT hTH))

/-- Fixing the quotient line leaves the third commutator inside Z(U), of order two. -/
theorem third_not_mem (hq : Function.Surjective q) :
    (thirdActor q).map H.subtype ∉ YFamily H T V₂ (W ⊓ N) := by
  let X := (thirdActor q).map H.subtype
  have hX : X ≤ H := map_subtype_le _
  apply Mathieu.not_mem_YFamily_of_fixed_quotient_point d.pair.representation
    H T U V₂ (W ⊓ N) X (hX.trans d.normalizes) h.V₂_le_U
    (CentralAction.actor q X hX) d.projection (d.conjugation X hX) (line h.s)
  · intro u hu
    rw [← h.marked]
    exact ⟨u, hu, rfl⟩
  · rw [d.projection_ker, IsExtraspecial.center_order_p 2 U]
    decide
  · rw [CentralAction.actor_range, CentralAction.lifted_actor_image,
      thirdActor, residualLift_map q hq]
    exact third_fixes_line d.pair h.s (h.fixed_standard hT)

end EarlierGeometry

variable [Finite G]

/-- The equivalence induced by the literal inclusion H↪G on the overlap. -/
def overlapEmbedding (H T : Subgroup G) (q : H →* S7) (hTH : T ≤ H) :
    (firstActor q ⊔ secondActor q ⊔ T.subgroupOf H : Subgroup H) ≃*
      ((firstActor q).map H.subtype ⊔ (secondActor q).map H.subtype ⊔ T : Subgroup G) := by
  let J := firstActor q ⊔ secondActor q ⊔ T.subgroupOf H
  have he : J.map H.subtype =
      (firstActor q).map H.subtype ⊔ (secondActor q).map H.subtype ⊔ T := by
    rw [Subgroup.map_sup, Subgroup.map_sup, map_subgroupOf_eq_of_le hTH]
  exact (J.equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr he)

/-- The concrete overlap equivalence embedded back into the original ambient group. -/
def ambientOverlapEquiv (H T : Subgroup G) (q : H →* S7)
    (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker) (hTH : T ≤ H)
    (hT : (T.subgroupOf H).map q = standardTwo) :
    coreQuotient ((firstActor q).map H.subtype ⊔ (secondActor q).map H.subtype ⊔ T) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
  (QuotientGroup.congr _ _ (overlapEmbedding H T q hTH)
    (pCore_map_iso 2 (overlapEmbedding H T q hTH))).symm.trans
    (PermutationCalculation.sourceOverlapQuotientEquiv q hq hk (T.subgroupOf H) hT)

/-- Compatibility of the ambient overlap isomorphism with the actual quotient
maps and the permutation projection, not merely an abstract isomorphism type. -/
theorem ambientOverlapEquiv_mk (H T : Subgroup G) (q : H →* S7)
    (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker) (hTH : T ≤ H)
    (hT : (T.subgroupOf H).map q = standardTwo)
    (x : (firstActor q ⊔ secondActor q ⊔ T.subgroupOf H : Subgroup H)) :
    ambientOverlapEquiv H T q hq hk hTH hT
      (QuotientGroup.mk' (pCore 2 _) (overlapEmbedding H T q hTH x)) =
    Theory.SpecificGroups.SymmetricSeven.ResidualTripleGeometry.overlapProjection
      ⟨q x.val, by
        change q x.val ∈ modelOverlap
        rw [← overlap_map q hq (T.subgroupOf H) hT]
        exact mem_map_of_mem q x.property⟩ := by
  change PermutationCalculation.sourceOverlapQuotientEquiv q hq hk (T.subgroupOf H) hT
    ((QuotientGroup.congr _ _ (overlapEmbedding H T q hTH)
      (pCore_map_iso 2 (overlapEmbedding H T q hTH))).symm
        (QuotientGroup.mk' _ (overlapEmbedding H T q hTH x))) = _
  have hm := QuotientGroup.congr_mk'
    (pCore 2 (firstActor q ⊔ secondActor q ⊔ T.subgroupOf H : Subgroup H))
    (pCore 2 ((firstActor q).map H.subtype ⊔ (secondActor q).map H.subtype ⊔ T : Subgroup G))
    (overlapEmbedding H T q hTH) (pCore_map_iso 2 (overlapEmbedding H T q hTH)) x
  rw [← hm, MulEquiv.symm_apply_apply]
  exact PermutationCalculation.sourceOverlapQuotientEquiv_mk q hq hk (T.subgroupOf H) hT x

variable [Finite Q]

/-- Lemma 14.4.11 in aligned coordinates, conditional only on the stated earlier
local geometry and the actual case-(4) action. -/
theorem yFamily_and_output (H T U V₂ W N : Subgroup G) [IsExtraspecial 2 U]
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (e : coreQuotient H ≃* S7)
    (hT : (S : Subgroup H).map (starProjection e) = standardTwo)
    (d : CentralAction (Q := Q) H U (starProjection e))
    (h : EarlierGeometry d T V₂ W N) :
    YFamily H T V₂ (W ⊓ N) =
      {(firstActor (starProjection e)).map H.subtype,
        (secondActor (starProjection e)).map H.subtype} ∧
    S7Output H T V₂ (W ⊓ N)
      ((firstActor (starProjection e)).map H.subtype)
      ((secondActor (starProjection e)).map H.subtype) := by
  have hTH : T ≤ H := hS ▸ map_subtype_le _
  have hTS : T.subgroupOf H = (S : Subgroup H) := by
    rw [← hS, Subgroup.subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
  have ht : (T.subgroupOf H).map (starProjection e) = standardTwo := hTS ▸ hT
  have hq := starProjection_surjective e
  have hk : IsPGroup 2 (starProjection e).ker := by
    rw [starProjection_ker]
    exact pCore_isPGroup
  obtain ⟨⟨h₁,h₁E⟩,⟨h₂,h₂E⟩⟩ := h.actor_calculation ht hq hk hTH
  have hY := Mathieu.yFamily_eq_pair_of_three_actor_calculation H T V₂ (W ⊓ N)
    _ _ _ (ambient_XFamily_eq H T _ hq hk S hS hT)
    h₁ h₂ h₁E h₂E (h.third_not_mem ht hq)
  refine ⟨hY, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hY]; simp
  · rw [hY]; simp
  · intro he
    exact firstActor_ne_secondActor _ hq (map_injective H.subtype_injective he)
  · exact ⟨ambientOverlapEquiv H T _ hq hk hTH ht⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.SymmetricSeven

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.SymmetricSeven
variable {G Q : Type*} [Group G] [Group Q] [IsMulCommutative Q]
  [Module (ZMod 2) (Additive Q)]

namespace CentralAction
variable {H U : Subgroup G} {q : H →* S7} (d : CentralAction (Q := Q) H U q)

/-- The representation operator gives the change of vector coordinates
corresponding to an inner relabelling of the seven points. -/
def vectorEquiv (r : S7) : Additive Q ≃ₗ[ZMod 2] Additive Q :=
  LinearEquiv.ofBijective (d.pair.representation r) (d.pair.representation.apply_bijective r)

def vectorMulEquiv (r : S7) : Q ≃* Q where
  toFun x := (d.vectorEquiv r (Additive.ofMul x)).toMul
  invFun x := ((d.vectorEquiv r).symm (Additive.ofMul x)).toMul
  left_inv x := congrArg Additive.toMul ((d.vectorEquiv r).symm_apply_apply (Additive.ofMul x))
  right_inv x := congrArg Additive.toMul ((d.vectorEquiv r).apply_symm_apply (Additive.ofMul x))
  map_mul' x y := congrArg Additive.toMul ((d.vectorEquiv r).map_add (Additive.ofMul x) (Additive.ofMul y))

private theorem conjugated_operator (r t : S7) (v : Additive Q) :
    d.pair.representation (r*t*r⁻¹) (d.pair.representation r v) =
      d.pair.representation r (d.pair.representation t v) := by
  simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]

/-- Relabel the seven points and simultaneously change central-quotient
coordinates. The supplied conjugate-pair representation itself is retained. -/
def relabel (r : S7) : CentralAction (Q := Q) H U
    ((MulAut.conj r).toMonoidHom.comp q) where
  coordinates := d.coordinates.trans (vectorMulEquiv d r)
  pair := d.pair
  normalizes := d.normalizes
  equivariant h u := by
    change d.pair.representation (r * q h * r⁻¹)
      (d.pair.representation r (Additive.ofMul (d.projection u))) = _
    rw [CentralAction.conjugated_operator d]
    exact congrArg (d.pair.representation r) (d.equivariant h u)

theorem relabel_image (r : S7) (P : Subgroup G) :
    (d.relabel r).image P = (d.image P).map (d.vectorEquiv r).toLinearMap := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨Additive.ofMul (d.projection u), ⟨u, hu, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, rfl⟩

end CentralAction

namespace EarlierGeometry
variable {H T U V₂ W N : Subgroup G} {q : H →* S7}
  {d : CentralAction (Q := Q) H U q} (h : EarlierGeometry d T V₂ W N)

/-- The earlier geometric hypotheses transport with the literal conjugation
of the star image; no new action-equivalence premise is required. -/
def relabel (r : S7) : EarlierGeometry (d.relabel r) T V₂ W N where
  U_le_T := h.U_le_T
  V₂_le_U := h.V₂_le_U
  center_le_V₂ := h.center_le_V₂
  W_le_U := h.W_le_U
  W_index := h.W_index
  N_le_T := h.N_le_T
  center_le_E := h.center_le_E
  commutator_le_E := h.commutator_le_E
  s := d.vectorEquiv r h.s
  nonzero := by
    intro hz
    apply h.nonzero
    exact (d.vectorEquiv r).injective (hz.trans (map_zero _).symm)
  marked := by
    rw [d.relabel_image, h.marked, line, Submodule.map_span]
    rw [Set.image_singleton]
    rfl
  fixed := by
    rintro t ⟨x, hx, rfl⟩
    change d.pair.representation (r*q x*r⁻¹) (d.pair.representation r h.s) =
      d.pair.representation r h.s
    rw [CentralAction.conjugated_operator d, h.fixed (q x) (mem_map_of_mem q hx)]
  image_card := by
    rw [← map_map, card_map_of_injective (MulAut.conj r).injective]
    exact h.image_card
  image_normal := by
    intro t ht
    have hf : d.pair.representation (r⁻¹*t*r) h.s = h.s := by
      have he := congrArg (d.pair.representation r⁻¹) ht
      change d.pair.representation r⁻¹ (d.pair.representation t
        (d.pair.representation r h.s)) =
          d.pair.representation r⁻¹ (d.pair.representation r h.s) at he
      simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply, mul_assoc] using he
    have hn := h.image_normal (r⁻¹*t*r) hf
    have hm := (le_normalizer_map (MulAut.conj r).toMonoidHom)
      (mem_map_of_mem (MulAut.conj r).toMonoidHom hn)
    rw [map_map] at hm
    convert hm using 1
    change t = r * (r⁻¹ * t * r) * r⁻¹
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

end EarlierGeometry
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.SymmetricSeven

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.SymmetricSeven
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [IsMulCommutative Q]
  [Module (ZMod 2) (Additive Q)] [Finite Q]

/-- W=C_U(V₂), as an actual subgroup of the original ambient group. -/
def sourceW (U V₂ : Subgroup G) : Subgroup G := U ⊓ centralizer (V₂ : Set G)

/-- Right conjugation, the book's W^g=g⁻¹Wg. -/
def sourceWg (U V₂ : Subgroup G) (g : G) : Subgroup G :=
  (sourceW U V₂).map (MulAut.conj g⁻¹).toMonoidHom

/-- The source intersection E=W∩W^g. -/
def sourceE (U V₂ : Subgroup G) (g : G) : Subgroup G := sourceW U V₂ ⊓ sourceWg U V₂ g

/-- The residual of the literal pointwise stabilizer of source letters 1,2,3,4. -/
def firstSourceActor (H : Subgroup G) (e : coreQuotient H ≃* S7) : Subgroup G :=
  (residualLift (starProjection e)
    Theory.SpecificGroups.SymmetricSeven.ResidualTripleGeometry.fourFixer).map H.subtype

/-- The residual of the literal pointwise stabilizer of source letters 5,6,7. -/
def secondSourceActor (H : Subgroup G) (e : coreQuotient H ≃* S7) : Subgroup G :=
  (residualLift (starProjection e)
    Theory.SpecificGroups.SymmetricSeven.ResidualTripleGeometry.threeFixer).map H.subtype

/-- Genuine conditional Lemma 14.4.11. Coordinates are chosen from the supplied
quotient isomorphism and the supplied case-(4) action is transported explicitly.
The hypotheses are the earlier local geometry; neither a family-recognition
certificate nor any moved-space conclusion is assumed. Source letters
(1,2,3,4,5,6,7) correspond to Fin 7 coordinates (2,3,4,5,0,1,6). -/
theorem lemma_14_4_11 (H T U V₂ : Subgroup G) (g : G) [IsExtraspecial 2 U]
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (e₀ : coreQuotient H ≃* S7)
    (d : CentralAction (Q := Q) H U (starProjection e₀))
    (h : EarlierGeometry d T V₂ (sourceW U V₂) (sourceWg U V₂ g)) :
    ∃ e : coreQuotient H ≃* S7,
      (S : Subgroup H).map (starProjection e) = standardTwo ∧
      (∀ t ∈ (S : Subgroup H),
        ({2,3,4,5} : Finset (Fin 7)).image (starProjection e t) = {2,3,4,5} ∧
        ({0,1} : Finset (Fin 7)).image (starProjection e t) = {0,1} ∧
          starProjection e t 6 = 6) ∧
      XFamily H T = {firstSourceActor H e, secondSourceActor H e,
        (thirdActor (starProjection e)).map H.subtype} ∧
      ((sourceWg U V₂ g).subgroupOf H).map (starProjection e) = B8 ∧
      YFamily H T V₂ (sourceE U V₂ g) = {firstSourceActor H e, secondSourceActor H e} ∧
      S7Output H T V₂ (sourceE U V₂ g) (firstSourceActor H e) (secondSourceActor H e) := by
  let q₀ := starProjection e₀
  let S₀ := S.mapSurjective (starProjection_surjective e₀)
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq S7 S₀ standardSylow
  let e := e₀.trans (MulAut.conj r)
  have ht : (S : Subgroup H).map (starProjection e) = standardTwo := by
    have hh := congrArg Sylow.toSubgroup hr
    change ((S : Subgroup H).map q₀).map (MulAut.conj r).toMonoidHom = standardTwo at hh
    rw [map_map] at hh
    exact hh
  have hTH : T ≤ H := hS ▸ map_subtype_le _
  have hTS : T.subgroupOf H = (S : Subgroup H) := by
    rw [← hS, Subgroup.subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
  have ht' : (T.subgroupOf H).map (starProjection e) = standardTwo := hTS ▸ ht
  let d' : CentralAction (Q := Q) H U (starProjection e) := d.relabel r
  let h' : EarlierGeometry d' T V₂ (sourceW U V₂) (sourceWg U V₂ g) := h.relabel r
  have hq := starProjection_surjective e
  have hk : IsPGroup 2 (starProjection e).ker := by
    rw [starProjection_ker]
    exact pCore_isPGroup
  have hfirst : (firstActor (starProjection e)).map H.subtype = firstSourceActor H e := by
    rw [PermutationCalculation.firstActor_eq_pointwise_lift _ hq hk]
    rfl
  have hsecond : (secondActor (starProjection e)).map H.subtype = secondSourceActor H e := by
    rw [PermutationCalculation.secondActor_eq_pointwise_lift _ hq hk]
    rfl
  have hout := yFamily_and_output H T U V₂ _ _ S hS e ht d' h'
  have hcat := ambient_XFamily_eq H T _ hq hk S hS ht
  rw [hfirst, hsecond] at hout hcat
  refine ⟨e, ht, ?_, hcat, h'.image_eq_B8 ht', hout⟩
  exact PermutationCalculation.sourceSylow_preserves_blocks (starProjection e) S ht

/-- The source application needed in 14.4.13: the earlier distinguished
member L₁ has a distinct partner, with the required line-vertex quotient.
The L₁-membership premise is exactly 14.4.8(1). -/
theorem exists_partner (H T U V₂ L₁ : Subgroup G) (g : G) [IsExtraspecial 2 U]
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (e₀ : coreQuotient H ≃* S7)
    (d : CentralAction (Q := Q) H U (starProjection e₀))
    (h : EarlierGeometry d T V₂ (sourceW U V₂) (sourceWg U V₂ g))
    (hL₁ : L₁ ∈ YFamily H T V₂ (sourceE U V₂ g)) :
    ∃ X : Subgroup G, X ∈ YFamily H T V₂ (sourceE U V₂ g) ∧ X ≠ L₁ ∧
      Nonempty (coreQuotient (L₁ ⊔ X ⊔ T) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  obtain ⟨e, _, _, _, _, hY, ho⟩ := lemma_14_4_11 H T U V₂ g S hS e₀ d h
  rw [hY] at hL₁
  rcases (show L₁ = firstSourceActor H e ∨ L₁ = secondSourceActor H e from hL₁) with h₁ | h₂
  · subst L₁
    exact ⟨secondSourceActor H e, ho.X₂_mem_Y, Ne.symm ho.distinct, ho.overlap_quotient⟩
  · subst L₁
    refine ⟨firstSourceActor H e, ho.X₁_mem_Y, ho.distinct, ?_⟩
    rw [sup_comm (secondSourceActor H e) (firstSourceActor H e)]
    exact ho.overlap_quotient

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.SymmetricSeven
