module

public import Stellmacher.Recognition.NormalEightQuaternionFourElementaryGeometry
public import Stellmacher.Recognition.NormalEightLargeCoreIndexTwoInside
public import Stellmacher.Recognition.NormalEightQuaternionDihedralWitness
public import Theory.GroupTheory.PGroup.ExtraspecialDerivedSquares
public import Theory.GroupTheory.QuaternionFourQuotientFactorNormality
public import Theory.GroupTheory.QuaternionFourQuotientDerivedSquare

/-!
# A derived-square obstruction to fusion of the normal four

Fusion of the three involutions in the unique normal four makes its
centralizer have no characteristic subgroup of order two. The extraspecial
core and the elementary core quotient then force every element of the
centralizer's derived subgroup to have square one. A nontrivial derived
square therefore separates the central involution from the other two.

For the quaternion core of index four, the normal-only elementary-eight
bound forces both quaternion factors to be normal. Their independent actions
produce the required derived square. The fixed-four identity is supplied by
the existing geometry, without assuming elementary structure of an
outside-involution centralizer or global coverage of involution classes.

Source: Janko–Thompson, Math. Z. 113 (1970), §4 case (b)(ii), printed p.391;
the source separation cites the structural results 1.3–1.5 on p.386.
-/

open Subgroup
open Stellmacher.Recognition.NormalFourCentralOmegaTwo
namespace Stellmacher.Recognition.NormalEightNonnormalImage
variable {G : Type*} [Group G] [Finite G]

/-- Fusion of the normal four forces exponent at most two in the derived
subgroup of its centralizer. Only normal elementary eights are excluded. -/
public theorem quaternion_four_fused_derived_square_eq_one
    (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hquot : IsElementaryAbelian 2 (S ⧸ omegaCorePreimage S))
    (hfused : ∀ x y : W, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G)) :
    ∀ x : centralizer (W : Set S), x ∈ _root_.commutator (centralizer (W : Set S)) →
      x ^ 2 = 1 := by
  let : IsExtraspecial 2 (omegaCorePreimage S) :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  let : IsMulCommutative (S ⧸ omegaCorePreimage S) := hquot.toIsMulCommutative
  apply derived_square_eq_one_of_no_characteristic_two_of_normal_extraspecial
    (omegaCorePreimage S) (centralizer (W : Set S))
  intro K hK
  let : K.Characteristic := hK
  exact S.centralizer_fused_four_no_characteristic_two hno hZ W hW hunique hfused K

/-- A nontrivial square in the four-centralizer's derived subgroup supplies
exactly the class separation needed by the elementary fixed-core assembly. -/
public theorem quaternion_four_normal_four_separation_of_derived_square
    (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hquot : IsElementaryAbelian 2 (S ⧸ omegaCorePreimage S))
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (hderived : ∃ x : centralizer (W : Set S),
      x ∈ _root_.commutator (centralizer (W : Set S)) ∧ x ^ 2 ≠ 1) :
    ∀ w : S, w ∈ W → w ≠ 1 → w ≠ z → ¬ IsConj (z : G) (w : G) := by
  intro w hw _ hwz hzw
  have hfused := normal_four_fused_of_distinct_central_conjugate
    S hZ hno W hW z w hz hzc hw hwz hzw
  obtain ⟨x, hx, hx2⟩ := hderived
  exact hx2 (quaternion_four_fused_derived_square_eq_one S hZ hno W hW hunique hquot hfused x hx)

/-- In the quaternion index-four branch, the other two involutions of the
unique normal four are not conjugate to the central involution. Factor
normality, the derived-square witness, and the fixed-four identity are all
discharged from the local hypotheses. -/
public theorem quaternion_four_normal_four_separation
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup _) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (z t : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S)
    (hindex : (omegaCorePreimage S).index = 4)
    (hquot : IsElementaryAbelian 2 (S ⧸ omegaCorePreimage S))
    (hfixed : IsElementaryAbelian 2 ((omegaCorePreimage S).subgroupOf
      (centralizer ({t} : Set S))))
    (hfixed_card : Nat.card ((omegaCorePreimage S).subgroupOf
      (centralizer ({t} : Set S))) ≤ 4) :
    ∀ w : S, w ∈ W → w ≠ 1 → w ≠ z → ¬ IsConj (z : G) (w : G) := by
  have hfixedW := (quaternion_four_elementary_fixed_eq_and_coset
    hN S hZ W hunique B C hB hC hjoin hinter hcomm t ht hout hindex
      hfixed hfixed_card).1
  obtain ⟨B', C', hB', hC', hj, hi, hc, _, _, hself⟩ :=
    quaternion_dihedral_actual_factors hN S hZ hH B C hB hC hjoin hinter hcomm
  let P := omegaCorePreimage S
  let : IsExtraspecial 2 P :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  let : IsElementaryAbelian 2 (S ⧸ P) := hquot
  obtain ⟨hBn, hCn⟩ := quaternion_factors_normal_of_elementary_quotient
    P B' C' hB' hC' hj hi hc hno
  let : B'.Normal := hBn
  let : C'.Normal := hCn
  apply quaternion_four_normal_four_separation_of_derived_square
    S hZ hno W hW hunique hquot z hz hzc
  exact quaternion_four_quotient_exists_derived_square S.isPGroup' P
    ((card_omegaCorePreimage S).trans hH) hindex
    (by simpa only [hj] using hself) B' C' hB' hC' hj hi hc W t ht hfixedW

end Stellmacher.Recognition.NormalEightNonnormalImage
