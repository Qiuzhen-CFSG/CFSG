module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Fusion
public import Theory.SpecificGroups.Janko4.Model.LinearFiveRadicalBound
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.GroupTheory.PRadical

/-!
# Full ambient normalizer recognition for the native F

The actual exterior marking, two native conjugation certificates, ambient
class separation and C(F)=F discharge the generic recognition theorem.
The resulting map has kernel the literal F and identifies the quotient by
the full intrinsic two-core. The native size-bound application retains the
actual normalizer inclusion into J₄.

Source: Kleidman--Wilson (1988), Lemma 1.1.1 and Aschbacher--Smith 12.5.1.
A complement and the global two-conjugate geometry are separate assertions.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive
open Cardinality KernelCount Subgroup
open Representation Representation.SL5ExteriorSquare Representation.SL5TenDimensional
open Representation.SL5ExteriorSquare.TwoGeneratorRecognition
open NativeNormalizer
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel localX localY

abbrev fullNormalizer := Subgroup.normalizer (F : Set Model)
abbrev normalizerKernel := F.subgroupOf fullNormalizer

private theorem nativeAction0_eq :
    (BinaryConjugationSection.normalizerAction exteriorMarking.toMonoidHom
      exteriorMarking.bijective (normalizerElement 0)).toLinearMap = exteriorAction 2 A0 :=
  action_eq_of_coordinates F exteriorMarking _ _ (exterior_conjugation 0)
private theorem nativeAction1_eq :
    (BinaryConjugationSection.normalizerAction exteriorMarking.toMonoidHom
      exteriorMarking.bijective (normalizerElement 1)).toLinearMap = exteriorAction 2 A1 :=
  action_eq_of_coordinates F exteriorMarking _ _ (exterior_conjugation 1)

/-- The homomorphism induced by the actual left exterior action. -/
def normalizerProjection : fullNormalizer →* Representation.SL5TenDimensional.Group :=
  normalizerToSL F exteriorMarking preserves_decomposable

theorem normalizerProjection_surjective : Function.Surjective normalizerProjection :=
  normalizerToSL_surjective F exteriorMarking preserves_decomposable
    (normalizerElement 0) (normalizerElement 1) nativeAction0_eq nativeAction1_eq

theorem normalizerProjection_ker : normalizerProjection.ker = normalizerKernel := by
  rw [normalizerProjection, normalizerToSL_ker, centralizer_F]

def normalizerQuotient : (fullNormalizer ⧸ normalizerKernel) ≃* Representation.SL5TenDimensional.Group :=
  normalizerQuotientEquiv F exteriorMarking preserves_decomposable
    (normalizerElement 0) (normalizerElement 1) (by exact nativeAction0_eq)
    (by exact nativeAction1_eq) centralizer_F

theorem normalizerQuotient_mk (n : fullNormalizer) :
    normalizerQuotient (QuotientGroup.mk n) = normalizerProjection n :=
  normalizerQuotientEquiv_mk F exteriorMarking preserves_decomposable
    (normalizerElement 0) (normalizerElement 1) nativeAction0_eq nativeAction1_eq centralizer_F n

theorem normalizerProjection_exterior (n : fullNormalizer) (x : F) :
    (exteriorMarking (F.normalizerMonoidHom n x)).toAdd =
      exteriorAction 2 (normalizerProjection n) (exteriorMarking x).toAdd :=
  normalizerToSL_intertwines F exteriorMarking preserves_decomposable n x

/-- The same marking is linear on Additive F and equivariant for the same projection. -/
theorem normalizerProjection_linear (n : fullNormalizer) (x : F) :
    exteriorLinearMarking (Additive.ofMul (F.normalizerMonoidHom n x)) =
      exteriorAction 2 (normalizerProjection n) (exteriorLinearMarking (Additive.ofMul x)) := by
  simpa only [exteriorLinearMarking_apply] using normalizerProjection_exterior n x

theorem normalizerQuotient_representative (n : fullNormalizer) (x : F) :
    (exteriorMarking.symm (Multiplicative.ofAdd
      (exteriorAction 2 (normalizerQuotient (QuotientGroup.mk n))
        (exteriorMarking x).toAdd)) : Model) = (n : Model) * (x : Model) * (n : Model)⁻¹ :=
  normalizerQuotientEquiv_ambient F exteriorMarking preserves_decomposable
    (normalizerElement 0) (normalizerElement 1) nativeAction0_eq nativeAction1_eq centralizer_F n x

theorem normalizerProjection_generators :
    normalizerProjection (normalizerElement 0) = A0 ∧
      normalizerProjection (normalizerElement 1) = A1 := by
  simpa only [normalizerQuotientEquiv_mk, normalizerProjection] using
    normalizerQuotientEquiv_generators F exteriorMarking preserves_decomposable
      (normalizerElement 0) (normalizerElement 1) nativeAction0_eq nativeAction1_eq centralizer_F

private theorem SL5_twoCore : pCore 2 Representation.SL5TenDimensional.Group = ⊥ := by
  apply Subgroup.map_injective (f := (BinaryLinear.OuterCyclic.slEquivLinear 5).toMonoidHom)
    (BinaryLinear.OuterCyclic.slEquivLinear 5).injective
  rw [pCore_map_iso, Subgroup.map_bot]
  exact BinaryLinear.SmallParabolicLevi.linearGroup_twoCore_eq_bot

theorem normalizerKernel_isPGroup : IsPGroup 2 normalizerKernel := by
  let _ := F_elementary
  exact (IsElementaryAbelian.isPGroup 2 F).comap_of_injective
    fullNormalizer.subtype fullNormalizer.subtype_injective

theorem fullNormalizer_twoCore : pCore 2 fullNormalizer = normalizerKernel := by
  have h := normalizerProjection.comap_pCore_of_ker_isPGroup
    normalizerProjection_surjective (normalizerProjection_ker.symm ▸ normalizerKernel_isPGroup)
  rw [SL5_twoCore] at h
  exact h.symm.trans normalizerProjection_ker

/-- Quotient by the full intrinsic core, with no smaller denominator. -/
def intrinsicNormalizerQuotient :
    (fullNormalizer ⧸ pCore 2 fullNormalizer) ≃* Representation.SL5TenDimensional.Group :=
  (QuotientGroup.quotientMulEquivOfEq fullNormalizer_twoCore).trans normalizerQuotient

theorem intrinsicNormalizerQuotient_mk (n : fullNormalizer) :
    intrinsicNormalizerQuotient (QuotientGroup.mk n) = normalizerProjection n :=
  normalizerQuotient_mk n

/-- The actual native normalizer supplies the linear-five two-group bound. -/
theorem native_normalized_twoGroup_card_le_1024 (U : Subgroup Model)
    (hU : IsPGroup 2 U) (hn : fullNormalizer ≤ Subgroup.normalizer (U : Set Model)) :
    Nat.card U ≤ 1024 := by
  refine Janko4.linearFive_normalized_twoGroup_card_le_1024 fullNormalizer.subtype
    ?_ intrinsicNormalizerQuotient U hU ?_
  · rw [fullNormalizer.ker_subtype]
    exact IsPGroup.of_bot
  · simpa only [Subgroup.range_subtype] using hn


/-- A concrete generating family for the whole ambient normalizer. -/
def M_F : Subgroup Model := Subgroup.closure ((F : Set Model) ∪ Set.range element)

theorem F_le_M_F : F ≤ M_F := fun _ hx => Subgroup.subset_closure (Or.inl hx)

theorem element_mem_M_F (i : Fin 2) : element i ∈ M_F :=
  Subgroup.subset_closure (Or.inr (Set.mem_range_self i))

theorem M_F_le_fullNormalizer : M_F ≤ fullNormalizer := by
  apply (Subgroup.closure_le _).mpr
  rintro x (hx | ⟨i,rfl⟩)
  · exact F.le_normalizer hx
  · exact element_mem_normalizer i

/-- Both containments: the concrete family generates the full ambient normalizer. -/
theorem M_F_eq_fullNormalizer : M_F = fullNormalizer := by
  apply le_antisymm M_F_le_fullNormalizer
  intro x hx
  let n : fullNormalizer := ⟨x,hx⟩
  let H := M_F.subgroupOf fullNormalizer
  have him : H.map normalizerProjection = ⊤ := by
    apply eq_top_of_contains
    · exact Subgroup.mem_map.mpr ⟨normalizerElement 0, element_mem_M_F 0,
        normalizerProjection_generators.1⟩
    · exact Subgroup.mem_map.mpr ⟨normalizerElement 1, element_mem_M_F 1,
        normalizerProjection_generators.2⟩
  have hm : normalizerProjection n ∈ H.map normalizerProjection := by rw [him]; trivial
  obtain ⟨m,hm,he⟩ := Subgroup.mem_map.mp hm
  have hk : n * m⁻¹ ∈ normalizerProjection.ker := by
    change normalizerProjection (n * m⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  rw [normalizerProjection_ker] at hk
  have hkn : (n : Model) * (m : Model)⁻¹ ∈ F := hk
  have hprod := M_F.mul_mem (F_le_M_F hkn) hm
  change ((n : Model) * (m : Model)⁻¹) * (m : Model) ∈ M_F at hprod
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hprod

/-- F inside the concrete generated normalizer, rather than an abstract copy. -/
abbrev F_M : Subgroup M_F := F.subgroupOf M_F

/-- The native SL5 map on the concrete generated normalizer. -/
def pi_F : M_F →* Representation.SL5TenDimensional.Group :=
  normalizerProjection.comp (MulEquiv.subgroupCongr M_F_eq_fullNormalizer).toMonoidHom

theorem pi_F_surjective : Function.Surjective pi_F :=
  normalizerProjection_surjective.comp (MulEquiv.subgroupCongr M_F_eq_fullNormalizer).surjective

theorem pi_F_ker : pi_F.ker = F_M := by
  ext x
  change normalizerProjection ((MulEquiv.subgroupCongr M_F_eq_fullNormalizer) x) = 1 ↔ (x : Model) ∈ F
  rw [← MonoidHom.mem_ker, normalizerProjection_ker]
  rfl

instance F_M_normal : F_M.Normal := by
  rw [← pi_F_ker]
  infer_instance

theorem M_F_twoCore : pCore 2 M_F = F_M := by
  unfold F_M
  rw [M_F_eq_fullNormalizer]
  exact fullNormalizer_twoCore

def M_F_intrinsicQuotient :
    (M_F ⧸ pCore 2 M_F) ≃* Representation.SL5TenDimensional.Group :=
  (QuotientGroup.quotientMulEquivOfEq (M_F_twoCore.trans pi_F_ker.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective pi_F pi_F_surjective)

theorem M_F_intrinsicQuotient_mk (n : M_F) :
    M_F_intrinsicQuotient (QuotientGroup.mk n) = pi_F n := rfl

/-- Exterior equivariance under the very same map on the generated normalizer. -/
theorem pi_F_exterior (n : M_F) (x : F) :
    (exteriorMarking (F.normalizerMonoidHom
      ((MulEquiv.subgroupCongr M_F_eq_fullNormalizer) n) x)).toAdd =
        exteriorAction 2 (pi_F n) (exteriorMarking x).toAdd :=
  normalizerProjection_exterior ((MulEquiv.subgroupCongr M_F_eq_fullNormalizer) n) x

/-- Literal quotient representatives recover ambient conjugation with the original marking. -/
theorem M_F_intrinsicQuotient_representative (n : M_F) (x : F) :
    (exteriorMarking.symm (Multiplicative.ofAdd
      (exteriorAction 2 (M_F_intrinsicQuotient (QuotientGroup.mk n))
        (exteriorMarking x).toAdd)) : Model) = (n : Model) * (x : Model) * (n : Model)⁻¹ := by
  rw [M_F_intrinsicQuotient_mk, ← pi_F_exterior]
  change (exteriorMarking.symm (exteriorMarking (F.normalizerMonoidHom
    ((MulEquiv.subgroupCongr M_F_eq_fullNormalizer) n) x)) : Model) = _
  rw [exteriorMarking.symm_apply_apply]
  exact Subgroup.normalizerMonoidHom_apply_apply_coe F
    ((MulEquiv.subgroupCongr M_F_eq_fullNormalizer) n) x

/-- The bound is applied to the literal subtype of the generated native normalizer. -/
theorem M_F_normalized_twoGroup_card_le_1024 (U : Subgroup Model)
    (hU : IsPGroup 2 U) (hn : M_F ≤ Subgroup.normalizer (U : Set Model)) :
    Nat.card U ≤ 1024 := by
  refine Janko4.linearFive_normalized_twoGroup_card_le_1024 M_F.subtype
    ?_ M_F_intrinsicQuotient U hU ?_
  · rw [M_F.ker_subtype]
    exact IsPGroup.of_bot
  · simpa only [Subgroup.range_subtype] using hn

theorem F_ambient_twoCore : fullNormalizer.pCoreIn 2 = F := by
  rw [Subgroup.pCoreIn, fullNormalizer_twoCore]
  exact Subgroup.map_subgroupOf_eq_of_le F.le_normalizer

/-- The native P=F radical row, using the full normalizer and full two-core. -/
theorem F_isPRadical : F.IsPRadical 2 := by
  refine ⟨?_, F_ambient_twoCore⟩
  intro he
  have hc := F_card
  rw [he, Subgroup.card_bot] at hc
  norm_num at hc

private theorem SL5_card : Nat.card Representation.SL5TenDimensional.Group = 9999360 := by
  rw [Nat.card_congr Representation.SL5TenDimensional.projectiveEquiv.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
  calc
    _ = ∏ i : Fin 5, (2 ^ 5 - 2 ^ (i : ℕ)) := by
      simpa only [Nat.card_zmod,Nat.reduceSub,Nat.gcd_one_right,mul_one] using hc
    _ = 9999360 := by decide

/-- The full native normalizer genuinely extends outside max1. -/
theorem fullNormalizer_not_le_M : ¬ fullNormalizer ≤ M := by
  intro h
  have hdiv : 31 ∣ Nat.card fullNormalizer := by
    apply (show 31 ∣ Nat.card (fullNormalizer ⧸ normalizerKernel) from ?_).trans
      (Subgroup.card_quotient_dvd_card _)
    rw [Nat.card_congr normalizerQuotient.toEquiv, SL5_card]
    decide
  have hd : 31 ∣ Nat.card M := hdiv.trans (Subgroup.card_dvd_of_le h)
  rw [Cardinality.max1Subgroup_card matrixA_mul_self matrixB_pow_four] at hd
  norm_num at hd

/-- At least one of the two displayed native words is an outside generator. -/
theorem exists_outside_generator : ∃ i : Fin 2, element i ∉ M := by
  by_contra! h
  apply fullNormalizer_not_le_M
  rw [← M_F_eq_fullNormalizer]
  apply (Subgroup.closure_le _).mpr
  rintro x (hx | ⟨i,rfl⟩)
  · exact F_le_M hx
  · exact h i

end Janko4.LocalStructure.LinearFive
