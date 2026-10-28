module

public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Automorphisms
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.FirstParabolic
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SecondParabolic
public import Theory.GroupTheory.Amalgam.LocalStructure

/-!
# The verified outer M₁₂ pair

The marked inner model is now supplied by the proved faithful block restriction
and full automorphism equivalence. Thus all calculations below are unconditional.
The two parabolics generate the carrier, share a Sylow two-subgroup of order 128,
and have that subgroup as both local Sylow normalizers. Their inclusion maps
form the concrete Aut(M₁₂) amalgam.

The first core has order 64 and its residual commutator is Q₈ * Q₈. Its quotient
by the original Z = Ω₁(Z(T)) is E₄ wr C₂; the equality with the core's center is
proved separately. The first core is nonsplit, and is not C₄ * Q₈ * Q₈. The
second core is the actual centralizer of the natural four and also has order 64.
Both parabolic quotients are PSL₂(2). The re-marked split quaternion-swap
embedding used for whole-overlap movement is compared literally with the first
parabolic's quaternion embeddings, without identifying the two order-64 groups.

Sources: Aschbacher--Smith, F.1.12(I)(13), printed p.263, E.2.16, p.228,
and 14.2.21, p.988, refs/quasithin.pdf. This corrects the printed first-core
central product, while retaining the precise marked quotient in 14.2.21.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M12ExceptionalExtension.VerifiedPair
open Subgroup Theory.GroupTheory FirstParabolic

/-- The actual common Sylow subgroup, with the inner-model premise discharged. -/
def commonSylow : Sylow 2 Carrier := SecondCoordinates.commonSylow innerModel

theorem commonSylow_coe : (commonSylow : Subgroup Carrier) = overlap := rfl

theorem first_sylow_normalizer : firstParabolic ⊓ Subgroup.normalizer (overlap : Set Carrier) = overlap := by
  let T := (SecondCoordinates.commonSylow innerModel).subtype
    (show overlap ≤ firstParabolic from inf_le_left)
  have hT : Nat.card T = 128 := by
    change Nat.card (overlap.subgroupOf firstParabolic) = 128
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show overlap ≤ firstParabolic from inf_le_left)).toEquiv,
      SecondCoordinates.card_overlap innerModel]
  have hi : (T : Subgroup firstParabolic).index = 3 := by
    have h := (T : Subgroup firstParabolic).index_mul_card
    rw [card_firstParabolic innerModel, hT] at h
    omega
  have hn : Subgroup.normalizer ((T : Subgroup firstParabolic) : Set firstParabolic) = T := by
    have hd := Subgroup.index_dvd_of_le (T : Subgroup firstParabolic).le_normalizer
    rw [hi] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · have hn : (T : Subgroup firstParabolic).Normal :=
        Subgroup.normalizer_eq_top_iff.mp (Subgroup.index_eq_one.mp h)
      have hl : (T : Subgroup firstParabolic) ≤ pCore 2 firstParabolic :=
        le_sSup ⟨hn, T.isPGroup'⟩
      have hb := Subgroup.card_le_of_le hl
      rw [hT, card_pCore innerModel] at hb
      omega
    · apply (Subgroup.eq_of_le_of_card_ge (T : Subgroup firstParabolic).le_normalizer _).symm
      have hm := (Subgroup.normalizer ((T : Subgroup firstParabolic) : Set firstParabolic)).index_mul_card
      rw [h, card_firstParabolic innerModel] at hm
      rw [hT]
      omega
  change Subgroup.normalizer (overlap.subgroupOf firstParabolic : Set firstParabolic) =
    overlap.subgroupOf firstParabolic at hn
  rw [← Subgroup.subgroupOf_normalizer_eq (show overlap ≤ firstParabolic from inf_le_left)] at hn
  ext g
  constructor
  · rintro ⟨hg, hgN⟩
    exact (show (⟨g, hg⟩ : firstParabolic) ∈ overlap.subgroupOf firstParabolic from hn ▸ hgN)
  · intro hg
    exact ⟨hg.1, Subgroup.le_normalizer hg⟩


/-- The full inclusion amalgam of the two literal outer parabolics. -/
def amalgam : RankTwoAmalgam firstParabolic overlap secondParabolic :=
  RankTwoAmalgam.ofSubgroups _ _ _ inf_le_left inf_le_right

/-- Both first and second quotients use their own intrinsic two-cores. -/
def firstPSLQuotient : firstParabolic ⧸ pCore 2 firstParabolic ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2) :=
  firstParabolicPcoreQuotientPSL innerModel

def secondPSLQuotient : secondParabolic ⧸ pCore 2 secondParabolic ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2) :=
  (SecondCoordinates.secondCoreQuotient innerModel).trans
    ((Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).symm.trans
      Matrix.SpecialLinearGroup.sl2TwoEquivPSL2Two)

/-- The intrinsic residual commutator has the actual quaternion product structure. -/
def residualQuaternionData : QuaternionCentralProductData
    (⁅pCore 2 firstParabolic, pResidual 2 firstParabolic⁆ : Subgroup firstParabolic) :=
  (quaternionData innerModel).map
    ((Subgroup.equivMapOfInjective _ firstParabolic.subtype firstParabolic.subtype_injective).trans
      (MulEquiv.subgroupCongr (mapped_pCore_residual_commutator innerModel))).symm

/-- The source denominator is the image of Ω₁(Z(T)), not an arbitrary central subgroup. -/
theorem source_Z :
    (omega₁ (Subgroup.center overlap) (p := 2)).map
      (overlap.subtype.comp (Subgroup.center overlap).subtype) = distinguished :=
  SecondCoordinates.omega_center_image innerModel

/-- Independently, that same marked subgroup is the image of the first core's center. -/
theorem firstCore_center_image :
    (center (pCore 2 firstParabolic)).map
      (firstParabolic.subtype.comp (pCore 2 firstParabolic).subtype) = distinguished :=
  intrinsicCore_center_image innerModel

/-- The marked source quotient O₂(H)/Z. -/
def markedCoreQuotient : (pCore 2 firstParabolic) ⧸ intrinsicDistinguished ≃*
    QuaternionSwapModel.W := intrinsicCoreQuotientEquiv innerModel

/-- The center quotient is a consequence of the proved identification of Z. -/
def centerCoreQuotient : (pCore 2 firstParabolic) ⧸ center (pCore 2 firstParabolic) ≃*
    QuaternionSwapModel.W :=
  (QuotientGroup.quotientMulEquivOfEq (intrinsicCore_center innerModel)).trans
    markedCoreQuotient

/-- Actual first-parabolic conjugation on the source wreath quotient. -/
def wreathAction : firstParabolic →* MulAut QuaternionSwapModel.W :=
  FirstParabolic.wreathAction innerModel

theorem wreathAction_marked (h : firstParabolic)
    (x : (pCore 2 firstParabolic) ⧸ intrinsicDistinguished) :
    wreathAction h (markedCoreQuotient x) =
      markedCoreQuotient (intrinsicQuotientAction innerModel h x) :=
  wreathAction_intrinsicQuotientEquiv innerModel h x

theorem markedCoreQuotient_base :
    (intrinsicQuaternion.map (QuotientGroup.mk' intrinsicDistinguished)).map
      markedCoreQuotient.toMonoidHom = QuaternionSwapModel.base :=
  intrinsicCoreQuotientEquiv_base innerModel

/-- Unconditional compatible whole-overlap movement, including all four actor equations. -/
def secondGeometry : QuaternionSwapModel.MarkedSylow.SecondGeometry
    SecondCoordinates.movement overlap secondParabolic :=
  SecondCoordinates.secondGeometry innerModel

/-- Literal comparison of the first quaternion embedding with the movement marking. -/
theorem movement_left (q : QuaternionGroup 2) :
    SecondCoordinates.movement (QuaternionSwapModel.leftEmbedding q) =
      leftLift (SecondCoordinates.leftChange q) := by
  rw [SecondCoordinates.movement_left_original innerModel, map_leftLift]

/-- Literal comparison of the second quaternion embedding with the movement marking. -/
theorem movement_right (q : QuaternionGroup 2) :
    SecondCoordinates.movement (QuaternionSwapModel.rightEmbedding q) =
      rightLift (SecondCoordinates.rightChange q) := by
  rw [SecondCoordinates.movement_right_original innerModel, map_rightLift]

/-- The two different coordinate systems have the same embedded residual commutator. -/
theorem movement_residual_image :
    QuaternionSwapModel.QK.map SecondCoordinates.movement =
      (⁅pCore 2 firstParabolic, pResidual 2 firstParabolic⁆).map firstParabolic.subtype := by
  rw [mapped_pCore_residual_commutator innerModel, quaternionCore_eq_map innerModel]
  exact SecondCoordinates.movement_core innerModel

/-- The second core retains its actual ambient embedding as the natural-four centralizer. -/
theorem secondCore_image : (pCore 2 secondParabolic).map secondParabolic.subtype =
    Subgroup.centralizer (natural : Set Carrier) :=
  SecondCoordinates.secondCore_image innerModel

/-- The geometric and order assertions for the actual pair, without extra premises. -/
theorem pair_calculations :
    Nat.card firstParabolic = 384 ∧ Nat.card secondParabolic = 384 ∧
    Nat.card overlap = 128 ∧ Nat.card (pCore 2 firstParabolic) = 64 ∧
    Nat.card (pCore 2 secondParabolic) = 64 ∧
    firstParabolic ⊔ secondParabolic = ⊤ ∧
    secondParabolic ⊓ Subgroup.normalizer (overlap : Set Carrier) = overlap :=
  ⟨card_firstParabolic innerModel, SecondCoordinates.card_secondParabolic innerModel,
    SecondCoordinates.card_overlap innerModel, card_pCore innerModel,
    SecondCoordinates.card_secondCore innerModel,
    SecondCoordinates.parabolic_sup_eq_top innerModel,
    SecondCoordinates.second_sylow_normalizer innerModel⟩

/-- Concrete invariants rule out the printed central product and the split substitute. -/
theorem firstCore_correction :
    Nat.card (center (pCore 2 firstParabolic)) = 2 ∧
    Nat.card {x : pCore 2 firstParabolic // x ^ 2 = 1} = 20 ∧
    ¬ Nonempty (pCore 2 firstParabolic ≃* QuaternionSwapModel.QH) ∧
    ¬ Nonempty (firstParabolic ≃* QuaternionSwapModel.H0) :=
  ⟨card_intrinsicCore_center innerModel, card_square_one_intrinsicCore innerModel,
    intrinsicCore_not_equiv_split innerModel, firstParabolic_not_equiv_split innerModel⟩

/-- The faithfully embedded C₄ factor required by the printed central product is impossible. -/
theorem no_cyclic_four_central_product (C D : Subgroup outerCore)
    (e : C ≃* Multiplicative (ZMod 4))
    (hcomm : ∀ c ∈ C, ∀ d ∈ D, c * d = d * c) (hspan : C ⊔ D = ⊤) : False :=
  FirstParabolic.no_cyclic_four_central_product innerModel C D e hcomm hspan

end Sporadic.Mathieu.M12ExceptionalExtension.VerifiedPair
