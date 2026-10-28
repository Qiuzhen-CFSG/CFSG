module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.ResidualCore
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second.ResidualElementary

/-!
# Intrinsic inner halves of the native involution centralizers

The literal perfect triple-cover preimage in the first centralizer and the
inner-automorphism preimage in the second are precisely their solvable
residuals. Full movement puts the two-cores in those residuals, and the
actual quotient maps give index two. Conjugacy covers every involution.

The resulting intrinsic relation is functorial under homomorphisms and
invariant under simultaneous conjugacy. `FirstPair` applies it to a checked
reverse-character calculation. Symmetry on all commuting involutions is
not asserted.

Source: Kleidman--Wilson, The Maximal Subgroups of J4 (1988), p.487,
Corollary 1.1.4. These identifications fix the actual halves used there.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem m22_perfect : Group.IsPerfect M22 :=
  Group.IsPerfect.ofSurjective (f := M22TripleCover.centralQuotientEquiv.toMonoidHom.comp
    (QuotientGroup.mk' (center M22TripleCover)))
    (M22TripleCover.centralQuotientEquiv.surjective.comp
      (QuotientGroup.mk'_surjective _))

private theorem aut_residual :
    solvableResidual (MulAut M22) = MulAut.innerSubgroup M22 := by
  let := m22_perfect
  let : Group.IsPerfect (MulAut.innerSubgroup M22) := Group.IsPerfect.range MulAut.conj
  let : Group.IsNilpotent (MulAut.Outer M22) :=
    (IsPGroup.of_card_dvd_pow (p := 2) (n := 1)
      (by simpa only [pow_one] using
        M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two)).isNilpotent
  exact le_antisymm (solvableResidual_le_of_solvable_quotient _)
    (le_solvableResidual_of_isPerfect _)

theorem first_innerHalf_eq_residual :
    InvolutionCentralizers.First.QuotientExtension.H =
      solvableResidual InvolutionCentralizers.First.centralizer := by
  open InvolutionCentralizers.First InvolutionCentralizers.First.QuotientExtension
    OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel in
  let e : coverSubgroup ≃* M22TripleCover := subgroupOfEquivOfLe derivedGroup_le_actionGroup
  let : Group.IsPerfect coverSubgroup :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have htwo : IsPGroup 2 (actionGroup ⧸ coverSubgroup) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_congr coverQuotientEquiv.toEquiv]; simp)
  let : Group.IsNilpotent (actionGroup ⧸ coverSubgroup) := htwo.isNilpotent
  have hres : solvableResidual actionGroup = coverSubgroup :=
    le_antisymm (solvableResidual_le_of_solvable_quotient _)
      (le_solvableResidual_of_isPerfect _)
  change coverSubgroup.comap centralizerExtension.rightHom = _
  rw [← hres, ← map_solvableResidual_eq centralizerExtension.rightHom
    centralizerExtension.rightHom_surjective, comap_map_eq,
    centralizerProjection_ker, sup_eq_left.mpr twoCore_le_residual]

theorem second_innerHalf_eq_residual :
    (MulAut.innerSubgroup M22).comap
      InvolutionCentralizers.Second.ambientExtension.rightHom =
        solvableResidual InvolutionCentralizers.Second.ambientCentralizer := by
  open InvolutionCentralizers.Second in
  have hlocal : kernel ≤ solvableResidual localCentralizer := by
    rw [← CoreMovement.kernel_fully_moved]
    exact commutator_le_right _ _
  have hker : ambientExtension.rightHom.ker ≤ solvableResidual ambientCentralizer := by
    change ambientKernel ≤ _
    rw [ambientKernel_eq_map, ← map_solvableResidual_eq ambientEquivLocal.symm.toMonoidHom
      ambientEquivLocal.symm.surjective]
    exact map_mono hlocal
  rw [← aut_residual, ← map_solvableResidual_eq ambientExtension.rightHom
    ambientExtension.rightHom_surjective, comap_map_eq, sup_eq_left.mpr hker]

private theorem outer_m22_card : Nat.card (MulAut.Outer M22) = 2 := by
  have hi : Nat.card (MulAut.innerSubgroup M22) = 443520 := by
    let e : M22 ≃* MulAut.innerSubgroup M22 :=
      MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot m22_center_eq_bot)
    exact (Nat.card_congr e.symm.toEquiv).trans m22_order
  have ha : Nat.card (MulAut M22) = 887040 :=
    (Nat.card_congr MathieuCode.m22PairStabilizerEquivAut.symm.toEquiv).trans
      MathieuCode.m22PairStabilizer_card
  have h := (MulAut.innerSubgroup M22).card_mul_index
  rw [hi, ha, index_eq_card] at h
  change 443520 * Nat.card (MulAut.Outer M22) = 887040 at h
  omega

theorem first_residual_index :
    (solvableResidual InvolutionCentralizers.First.centralizer).index = 2 := by
  rw [← first_innerHalf_eq_residual, index_eq_card,
    Nat.card_congr InvolutionCentralizers.First.QuotientExtension.centralizerQuotientEquivC2.toEquiv]
  simp

theorem second_residual_index :
    (solvableResidual InvolutionCentralizers.Second.ambientCentralizer).index = 2 := by
  rw [← second_innerHalf_eq_residual, index_comap_of_surjective _
    InvolutionCentralizers.Second.ambientExtension.rightHom_surjective, index_eq_card]
  exact outer_m22_card

theorem involution_residual_index (z : Model) (hz : orderOf z = 2) :
    (solvableResidual (centralizer ({z} : Set Model))).index = 2 := by
  rcases InvolutionCentralizers.centralizer_equiv_first_or_second z hz with h | h
  all_goals obtain ⟨e⟩ := h
  all_goals
    have he : solvableResidual (centralizer ({z} : Set Model)) =
        (solvableResidual _).comap e.toMonoidHom := by
      rw [← map_solvableResidual_eq e.toMonoidHom e.surjective,
        comap_map_eq_self_of_injective e.injective]
    rw [he, index_comap_of_surjective _ e.surjective]
  · exact first_residual_index
  · exact second_residual_index

/-- Membership in the embedded solvable residual of the full centralizer.
For involutions this is membership in the actual inner half. -/
@[expose] def InnerRelated (x y : Model) : Prop :=
  y ∈ (solvableResidual (centralizer ({x} : Set Model))).map
    (centralizer ({x} : Set Model)).subtype

theorem innerRelated_map (e : Model →* Model) {x y : Model}
    (h : InnerRelated x y) : InnerRelated (e x) (e y) := by
  let f : centralizer ({x} : Set Model) →* centralizer ({e x} : Set Model) :=
    { toFun := fun z => ⟨e z, mem_centralizer_singleton_iff.mpr (by
        simpa only [map_mul] using congrArg e
          (mem_centralizer_singleton_iff.mp z.property))⟩
      map_one' := Subtype.ext (map_one e)
      map_mul' := fun u v => Subtype.ext (map_mul e (u : Model) (v : Model)) }
  obtain ⟨z, hz, rfl⟩ := h
  exact ⟨f z, map_solvableResidual_le f (mem_map_of_mem f hz), rfl⟩

theorem innerRelated_equiv (e : Model ≃* Model) (x y : Model) :
    InnerRelated (e x) (e y) ↔ InnerRelated x y := by
  constructor
  · intro h
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using innerRelated_map e.symm.toMonoidHom h
  · exact innerRelated_map e.toMonoidHom

end Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
