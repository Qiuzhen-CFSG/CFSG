module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoFour.Marked
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness

/-!
# The exact marked J₄ centralizer extensions

Transport the proved literal centralizer structures along genuine conjugation
isomorphisms. The first row retains the intrinsic O₂, its isomorphism with the
central product of six D₈ groups, and the full matrix quotient 3.M₂₂.2.
The latter is the extension of the genuine perfect triple cover by C₂; its
outer element inverts the covering scalar. It is not MulAut of the cover.
The imported first-centralizer normal series also retains the actual
C₃, M₂₂, 3.M₂₂, C₂ and Aut(M₂₂) sections and their maps.

The second row uses an actual vector-space basis to identify the elementary
kernel with E₂¹¹. Its faithful Aut(M₂₂) action is proved to be conjugation
through the transported embedding. All quotients use surjective homomorphisms
with proved kernels; no splitting is asserted. Both full rows have no components.

Source: Aschbacher–Smith 16.1.5(9), 16.1.7, printed pp.1172–1173;
GLS3 Table 5.3i resolves the first quotient's covering-group notation.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoFour
open Subgroup Theory.GroupTheory Janko4 Janko4.InvolutionCentralizers Sporadic.Mathieu
open scoped IsMulCommutative
noncomputable section
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

abbrev BinaryElementary (n : ℕ) := Multiplicative (Fin n → ZMod 2)
abbrev FirstQuotient := OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel.actionGroup

/-- Full first row, with the intrinsic two-core, its plus type, and the actual quotient. -/
structure FirstRow (C : Type) [Group C] where
  comparison : C ≃* First.centralizer
  plusEquiv : DihedralCentralProductSix.Model ≃* pCore 2 C
  core_extraspecial : IsExtraspecial 2 (pCore 2 C)
  core_card : Nat.card (pCore 2 C) = 2 ^ 13
  extension : GroupExtension (pCore 2 C) C FirstQuotient
  inl_eq : extension.inl = (pCore 2 C).subtype

/-- The actual ambient comparison restricts to the intrinsic two-cores. -/
def firstCoreEquiv {C : Type} [Group C] (e : C ≃* First.centralizer) :
    pCore 2 C ≃* pCore 2 First.centralizer :=
  (e.subgroupMap (pCore 2 C)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))

/-- The core comparison retains the original inclusion in the centralizer. -/
theorem firstCoreEquiv_coe {C : Type} [Group C] (e : C ≃* First.centralizer)
    (u : pCore 2 C) : (firstCoreEquiv e u : First.centralizer) = e u := rfl

/-- Transport retains the intrinsic kernel, not just an abstract group of the same order. -/
def firstRowOfEquiv {C : Type} [Group C] (e : C ≃* First.centralizer) : FirstRow C where
  comparison := e
  plusEquiv := First.PlusType.literalCorePlusEquiv.trans (firstCoreEquiv e).symm
  core_extraspecial := IsExtraspecial.of_mulEquiv (firstCoreEquiv e).symm
    First.centralizer_twoCore_extraspecial
  core_card := (Nat.card_congr (firstCoreEquiv e).toEquiv).trans First.centralizer_twoCore_card
  extension := {
    inl := (pCore 2 C).subtype
    rightHom := First.centralizerExtension.rightHom.comp e.toMonoidHom
    inl_injective := Subtype.val_injective
    range_inl_eq_ker_rightHom := by
      rw [range_subtype]
      ext c
      change c ∈ pCore 2 C ↔ First.centralizerExtension.rightHom (e c) = 1
      rw [← MonoidHom.mem_ker, First.QuotientExtension.centralizerProjection_ker]
      constructor
      · intro hc
        exact (firstCoreEquiv e ⟨c, hc⟩).property
      · intro hc
        have h := ((firstCoreEquiv e).symm ⟨e c, hc⟩).property
        have he : (((firstCoreEquiv e).symm ⟨e c, hc⟩ : pCore 2 C) : C) = c := by
          apply e.injective
          exact congrArg Subtype.val ((firstCoreEquiv e).apply_symm_apply ⟨e c, hc⟩)
        rwa [he] at h
    rightHom_surjective := First.centralizerExtension.rightHom_surjective.comp e.surjective }
  inl_eq := rfl

/-- The quotient in every first row is the genuine 3.M22.2 extension. -/
def firstCoveringExtension : GroupExtension M22TripleCover FirstQuotient
    (Multiplicative (ZMod 2)) := First.QuotientExtension.coveringExtension

/-- Its outer element inverts the actual order-three covering scalar. -/
theorem firstCoveringExtension_outer_action :
    firstCoveringExtension.conjAct First.QuotientExtension.outerElement
      M22TripleCover.scalar = M22TripleCover.scalar⁻¹ := by
  apply firstCoveringExtension.inl_injective
  rw [GroupExtension.inl_conjAct_comm, map_inv]
  exact First.QuotientExtension.outerElement_conj_scalar

/-- A genuine linear isomorphism identifies the elementary kernel with E2^11. -/
def secondKernelEquiv : Second.kernel ≃* BinaryElementary 11 := by
  let := Second.kernel_elementary
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive Second.kernel) = 2 ^ 11 := by
    have hs := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Second.kernel)
    change Nat.card Second.kernel = _ at hs
    simpa only [Nat.card_zmod, Second.kernel_card, show (2 : ℕ) ^ 11 = 2048 by decide]
      using hs.symm
  have hdim : Module.finrank (ZMod 2) (Additive Second.kernel) = 11 :=
    Nat.pow_right_injective (by decide : 1 < 2) hpow
  exact (Module.finBasisOfFinrankEq (ZMod 2) (Additive Second.kernel) hdim).equivFun.toAddEquiv.toMultiplicativeRight

/-- Transport of the full second extension with its actual kernel embedding. -/
def secondExtensionOfEquiv {C : Type} [Group C]
    (e : C ≃* Second.ambientCentralizer) :
    GroupExtension (BinaryElementary 11) C (MulAut M22) where
  inl := e.symm.toMonoidHom.comp
    (Second.ambientExtension.inl.comp secondKernelEquiv.symm.toMonoidHom)
  rightHom := Second.ambientExtension.rightHom.comp e.toMonoidHom
  inl_injective := e.symm.injective.comp
    (Second.ambientExtension.inl_injective.comp secondKernelEquiv.symm.injective)
  range_inl_eq_ker_rightHom := by
    ext c
    change (∃ u, e.symm (Second.ambientExtension.inl (secondKernelEquiv.symm u)) = c) ↔
      Second.ambientExtension.rightHom (e c) = 1
    rw [← MonoidHom.mem_ker, ← Second.ambientExtension.range_inl_eq_ker_rightHom]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨secondKernelEquiv.symm u, (e.apply_symm_apply _).symm⟩
    · rintro ⟨u, hu⟩
      refine ⟨secondKernelEquiv u, ?_⟩
      rw [secondKernelEquiv.symm_apply_apply, hu, e.symm_apply_apply]
  rightHom_surjective := Second.ambientExtension.rightHom_surjective.comp e.surjective

/-- The marked first row, valid for every two-central involution. -/
theorem central_row {x : Model} (hx : orderOf x = 2) (hc : SylowCentral x) :
    Nonempty (FirstRow (MulAut.conj x).fixedSubgroup) := by
  obtain ⟨e⟩ := central_fixed_equiv hx hc
  exact ⟨firstRowOfEquiv e⟩

/-- The marked second row, valid for every non-two-central involution. -/
theorem noncentral_row {x : Model} (hx : orderOf x = 2) (hc : ¬ SylowCentral x) :
    Nonempty (GroupExtension (BinaryElementary 11) (MulAut.conj x).fixedSubgroup
      (MulAut M22)) := by
  obtain ⟨e⟩ := noncentral_fixed_equiv hx hc
  exact ⟨secondExtensionOfEquiv e⟩

/-- The first marked companion in the exact Sylow-center convention of 16.5.6(4). -/
theorem central_row_of_twoCentral {x : Model} (hx : orderOf x = 2)
    (hc : DoubleCoverCentralizer.TwoCentral x) :
    Nonempty (FirstRow (MulAut.conj x).fixedSubgroup) :=
  central_row hx (sylowCentral_iff_twoCentral.mpr hc)

/-- The second marked companion in the exact Sylow-center convention of 16.5.6(4). -/
theorem noncentral_row_of_not_twoCentral {x : Model} (hx : orderOf x = 2)
    (hc : ¬ DoubleCoverCentralizer.TwoCentral x) :
    Nonempty (GroupExtension (BinaryElementary 11) (MulAut.conj x).fixedSubgroup
      (MulAut M22)) :=
  noncentral_row hx (fun h => hc (sylowCentral_iff_twoCentral.mp h))

/-- Components are absent in both full centralizer classes. -/
theorem inner_fixed_no_component (x : Model) (hx : orderOf x = 2)
    (K : Subgroup (MulAut.conj x).fixedSubgroup) :
    ¬ IsComponent (MulAut.conj x).fixedSubgroup K := by
  classical
  by_cases hc : SylowCentral x
  · obtain ⟨e⟩ := central_fixed_equiv hx hc
    exact fun hK => First.no_component _ (hK.map_equiv e)
  · obtain ⟨e⟩ := noncentral_fixed_equiv hx hc
    exact fun hK => Second.ambient_no_component _ (hK.map_equiv e)

end
end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoFour

namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoFour
open Subgroup Theory.GroupTheory Janko4 Janko4.InvolutionCentralizers Sporadic.Mathieu
noncomputable section
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The short exact sequence identifies the full quotient by the intrinsic core. -/
def FirstRow.quotientEquiv {C : Type} [Group C] (d : FirstRow C) :
    (C ⧸ pCore 2 C) ≃* FirstQuotient := by
  have hk : d.extension.rightHom.ker = pCore 2 C := by
    rw [← d.extension.range_inl_eq_ker_rightHom, d.inl_eq, range_subtype]
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective d.extension.rightHom
      d.extension.rightHom_surjective)

/-- The quotient projection is transported from the literal core conjugation action. -/
theorem firstRowOfEquiv_rightHom {C : Type} [Group C] (e : C ≃* First.centralizer)
    (c : C) : (firstRowOfEquiv e).extension.rightHom c =
      First.centralizerExtension.rightHom (e c) := rfl

/-- The second row's quotient action on its E2^11 kernel. -/
def secondAction : MulAut M22 →* MulAut (BinaryElementary 11) :=
  (MulAut.congr secondKernelEquiv).toMonoidHom.comp Second.autM22Action

theorem secondAction_injective : Function.Injective secondAction :=
  (MulAut.congr secondKernelEquiv).injective.comp Second.autM22Action_injective

/-- This faithful action is conjugation through the actual extension embedding. -/
theorem secondExtensionOfEquiv_action {C : Type} [Group C]
    (e : C ≃* Second.ambientCentralizer) (c : C) (u : BinaryElementary 11) :
    (secondExtensionOfEquiv e).inl
      (secondAction ((secondExtensionOfEquiv e).rightHom c) u) =
        c * (secondExtensionOfEquiv e).inl u * c⁻¹ := by
  apply e.injective
  simp only [map_mul, map_inv]
  change e (e.symm (Second.ambientExtension.inl
      (secondKernelEquiv.symm
        (secondKernelEquiv (Second.autM22Action
          (Second.ambientExtension.rightHom (e c)) (secondKernelEquiv.symm u)))))) =
    e c * e (e.symm (Second.ambientExtension.inl (secondKernelEquiv.symm u))) * (e c)⁻¹
  rw [secondKernelEquiv.symm_apply_apply, e.apply_symm_apply, e.apply_symm_apply]
  exact Second.ambientExtension_action (e c) (secondKernelEquiv.symm u)

/-- The quotient is identified by the actual surjective map to Aut(M22). -/
def secondQuotientEquiv {C : Type} [Group C] (e : C ≃* Second.ambientCentralizer) :
    (C ⧸ (secondExtensionOfEquiv e).rightHom.ker) ≃* MulAut M22 :=
  QuotientGroup.quotientKerEquivOfSurjective (secondExtensionOfEquiv e).rightHom
    (secondExtensionOfEquiv e).rightHom_surjective

end
end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoFour
