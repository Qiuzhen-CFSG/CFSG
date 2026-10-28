module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent

/-!
# The intrinsic two-core of the first J₄ involution centralizer

Let C be the centralizer of the literal first generator a in the binary
matrix model. The certified local generators generate C. Their seed normal
closure N is extraspecial, has center of order two, and has central quotient
the binary twelve-space. The existing quotient-kernel and relative-centralizer
calculations identify its actual image with O₂(C). We retain that embedding
and deduce the order 2¹³, rather than identifying groups by order.

The proved containment C_C(O₂(C)) ≤ O₂(C) excludes every ordinary component:
a component either lies in or centralizes the normal solvable two-core.
The explicit centralizer equivalence transports this conclusion from matrix
units to the literal subgroup of Janko4.Model.

Source: Aschbacher–Smith, combined manuscript, printed pp.1172–1173,
16.1.5(9) and the J₄ exclusion in 16.1.7; GLS3 Table 5.3i. The plus type and
full covering-extension identification are further assertions, not consequences
of the extraspeciality and order proved here.
-/

public section

namespace Janko4.InvolutionCentralizers.First

open Subgroup Theory.GroupTheory
open OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreCentralizerData TwoCoreComparison.CoordinateGenerators

private theorem no_component_of_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : ∀ D : Subgroup H, ¬ IsComponent H D)
    (D : Subgroup G) : ¬ IsComponent G D :=
  fun hD => h _ (hD.map_equiv e)

private noncomputable def coreEquivOfEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : pCore 2 G ≃* pCore 2 H :=
  (e.subgroupMap (pCore 2 G)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))

/-- The actual embedded seed normal closure is the intrinsic two-core. -/
theorem normalClosureImage_eq_twoCore :
    localNormalClosure.map localSubgroup.subtype = involutionTwoCore :=
  Realization.normalClosureImage_eq_twoCore_of_quotient_kernel
    Realization.localTwoCore_le_quotientAction_ker TwoCoreComparison.center_card_two
    localSubgroup_eq_top localNormalClosure_centralizer_pow_two

/-- The established image equality gives an equivalence preserving inclusion. -/
noncomputable def normalClosureEquivTwoCore : localNormalClosure ≃* involutionTwoCore :=
  Realization.normalClosureEquiv normalClosureImage_eq_twoCore

/-- The equivalence preserves the element of the full matrix centralizer. -/
theorem normalClosureEquivTwoCore_coe (n : localNormalClosure) :
    (normalClosureEquivTwoCore n : involutionCentralizer) = (n : localSubgroup) := by rfl

attribute [local irreducible] normalClosureEquivTwoCore

/-- Extraspeciality of the actual two-core, with every local premise discharged. -/
theorem twoCore_extraspecial : IsExtraspecial 2 involutionTwoCore :=
  IsExtraspecial.of_mulEquiv (A := localNormalClosure) (B := involutionTwoCore)
    normalClosureEquivTwoCore Realization.normalClosure_extraspecial

/-- The center and its twelve-dimensional quotient determine the core order. -/
theorem normalClosure_card : Nat.card localNormalClosure = 2 ^ 13 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center localNormalClosure),
    Realization.normalClosure_center_card,
    Nat.card_congr Realization.normalClosureCentralCoordinates.toEquiv]
  norm_num [Nat.card_eq_fintype_card]

/-- The intrinsic two-core in the matrix centralizer has order 8192. -/
theorem twoCore_card : Nat.card involutionTwoCore = 2 ^ 13 :=
  (Nat.card_congr normalClosureEquivTwoCore.toEquiv).symm.trans normalClosure_card

/-- The full matrix centralizer has no ordinary component. -/
theorem matrixCentralizer_no_component (D : Subgroup involutionCentralizer) :
    ¬ IsComponent involutionCentralizer D :=
  not_isComponent_of_twoCore localTwoCoreCentralizerControl.1 D

/-- The full centralizer of the literal first generator in the actual carrier. -/
abbrev centralizer : Subgroup Model := Subgroup.centralizer ({a} : Set Model)

/-- Flattening subtypes identifies the two realizations of the full centralizer. -/
noncomputable def centralizerEquiv : centralizer ≃* involutionCentralizer where
  toFun x := ⟨toAmbient x, (mem_involutionCentralizer_iff _).mpr
    ⟨x.val.property, by
      have h := mem_centralizer_singleton_iff.mp x.property
      simpa only [map_mul, toAmbient_a] using congrArg toAmbient h⟩⟩
  invFun x := ⟨⟨x, involutionCentralizer_le_matrixGroup x.property⟩, by
    apply mem_centralizer_singleton_iff.mpr
    apply toAmbient_injective
    exact ((mem_involutionCentralizer_iff _).mp x.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The centralizer comparison preserves the actual ambient matrix. -/
theorem centralizerEquiv_coe (x : centralizer) :
    (centralizerEquiv x : BinaryMatrixˣ) = toAmbient (x : Model) := by rfl

attribute [local irreducible] centralizerEquiv

/-- No component exists in the literal centralizer inside Janko4.Model. -/
theorem no_component (D : Subgroup centralizer) : ¬ IsComponent centralizer D := by
  exact @no_component_of_equiv centralizer involutionCentralizer inferInstance inferInstance
    centralizerEquiv matrixCentralizer_no_component D

/-- The same exclusion for a subgroup retained in the ambient J₄ carrier. -/
theorem no_componentIn (D : Subgroup Model) : ¬ IsComponentIn D centralizer :=
  fun hD => no_component _ hD.2

/-- The centralizer comparison carries intrinsic two-cores to one another. -/
noncomputable def twoCoreEquiv : pCore 2 centralizer ≃* involutionTwoCore :=
  @coreEquivOfEquiv centralizer involutionCentralizer inferInstance inferInstance centralizerEquiv

/-- The two-core comparison preserves the underlying centralizer element. -/
theorem twoCoreEquiv_coe (q : pCore 2 centralizer) :
    (twoCoreEquiv q : involutionCentralizer) = centralizerEquiv (q : centralizer) := by rfl

attribute [local irreducible] twoCoreEquiv

/-- Extraspeciality on the intrinsic two-core of the literal subgroup of J₄. -/
theorem centralizer_twoCore_extraspecial : IsExtraspecial 2 (pCore 2 centralizer) :=
  IsExtraspecial.of_mulEquiv (A := involutionTwoCore) (B := pCore 2 centralizer)
    twoCoreEquiv.symm twoCore_extraspecial

/-- The intrinsic two-core of C_J₄(a) has order 2¹³. -/
theorem centralizer_twoCore_card : Nat.card (pCore 2 centralizer) = 2 ^ 13 :=
  (Nat.card_congr twoCoreEquiv.toEquiv).trans twoCore_card



private theorem center_card_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : Nat.card (center G) = Nat.card (center H) :=
  Nat.card_congr (Subgroup.centerCongr e).toEquiv

/-- The literal first involution as an element of the intrinsic two-core. -/
def twoCoreInvolution : involutionTwoCore :=
  ⟨centralInvolution, centralInvolution_mem_twoCore⟩

/-- The core center is exactly the marked central involution subgroup. -/
theorem twoCore_center : center involutionTwoCore = zpowers twoCoreInvolution := by
  have hc : twoCoreInvolution ∈ center involutionTwoCore := by
    apply mem_center_iff.mpr
    intro q
    exact Subtype.ext (mem_center_iff.mp centralInvolution_mem_center q)
  have ho : orderOf twoCoreInvolution = 2 := by
    rw [← orderOf_injective involutionTwoCore.subtype Subtype.val_injective]
    exact orderOf_centralInvolution
  symm
  apply eq_of_le_of_card_ge (zpowers_le.mpr hc)
  rw [TwoCoreComparison.center_card_two, Nat.card_zpowers, ho]

/-- Its centralizer in the full local group is the same marked subgroup. -/
theorem twoCore_centralizer :
    Subgroup.centralizer (involutionTwoCore : Set involutionCentralizer) =
      zpowers centralInvolution := by
  apply le_antisymm
  · intro x hx
    let q : involutionTwoCore := ⟨x, localTwoCoreCentralizerControl.1 hx⟩
    have hq : q ∈ center involutionTwoCore := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (hx y y.property)
    rw [twoCore_center] at hq
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hq
    exact mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩
  · exact (zpowers_le.mpr centralInvolution_mem_center).trans (center_le_centralizer _)

/-- The full matrix centralizer also has precisely the marked cyclic center. -/
theorem matrixCentralizer_center :
    center involutionCentralizer = zpowers centralInvolution :=
  le_antisymm ((center_le_centralizer _).trans_eq twoCore_centralizer)
    (zpowers_le.mpr centralInvolution_mem_center)

/-- The full centralizer in the literal J₄ carrier has center of order two. -/
theorem centralizer_center_card : Nat.card (center centralizer) = 2 := by
  rw [@center_card_congr centralizer involutionCentralizer inferInstance inferInstance centralizerEquiv,
    matrixCentralizer_center, Nat.card_zpowers, orderOf_centralInvolution]

end Janko4.InvolutionCentralizers.First
