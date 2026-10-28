module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentification
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictAction

/-!
# The strict central quotient on the whole reduced Chapter 12 layer

These applications retain R₂(LT), the actual layer [R₂(LT),L], the chosen
involution centralizer and the literal quotient U/Z(U). The strict branch
constructs an extraspecial central factor with common center ⟨z⟩ and a
faithful symplectic action of H/C_H(U/Z(U)) in dimension at least four.
The image of U ∩ [R₂(LT),L] in that quotient has order four.

This discharges the central-product and symplectic-space inputs preceding
6.2.16--18. It does not assert the crossing geometry or the final
contradiction. The local-analysis premise is discharged by the existing
identification assembly qt-d-1222-rankone-recognition-identification.

Source: Aschbacher--Smith, 6.2.15--16 and 12.2.2(3d), pp.688--689 and 795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The source extraspecial factor and central plane on the actual reduced layer. -/
theorem strict_reduced_central_geometry
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L (wholeReduced T L) <
      sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L) :
    let U := sourceClosure (T : Subgroup G) L (wholeReduced T L) z
    (∃ F : Subgroup U, IsExtraspecial 2 F ∧ F ⊔ center U = ⊤ ∧
      ((center F).map F.subtype).map U.subtype = zpowers z) ∧
    (center U).map U.subtype ⊓ commutatorLayer T L = zpowers z ∧
    Nat.card (((U ⊓ commutatorLayer T L).subgroupOf U).map
      (QuotientGroup.mk' (center U))) = 4 :=
  ⟨A.strict_extraspecial_factor h611 hnatural hz horder hstrict,
    A.strict_layer_center_intersection h611 hnatural hz horder hstrict,
    A.strict_central_quotient_plane_card h611 hnatural hz horder hstrict⟩

/-- The dotted quotient acts faithfully and symplectically on the literal
central quotient. This constructs the space used by the later G.11 argument. -/
theorem strict_reduced_faithful_symplectic_action
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L (wholeReduced T L) <
      sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L) :
    ∃ he : IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z),
      letI := he
      ∃ B : LinearMap.BilinForm (ZMod 2)
        (Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z)),
        B.IsAlt ∧ B.Nondegenerate ∧
        4 ≤ Module.finrank (ZMod 2)
          (Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z)) ∧
        Function.Injective (strictRepresentation (T : Subgroup G) L (wholeReduced T L) z) ∧
        Nat.card (((commutatorLayer T L).subgroupOf (centralizer ({z} : Set G))).map
          (QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L (wholeReduced T L) z).ker)) = 2 ∧
        ∀ a x y, B (strictRepresentation (T : Subgroup G) L (wholeReduced T L) z a x)
          (strictRepresentation (T : Subgroup G) L (wholeReduced T L) z a y) = B x y := by
  obtain ⟨he, B, ha, hn, hd, hf, hi⟩ :=
    A.strict_faithful_symplectic_action h611 hnatural hz horder hstrict
  exact ⟨he, B, ha, hn, hd, hf,
    A.strict_layer_actor_image_card h611 hnatural hz horder hstrict, hi⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
