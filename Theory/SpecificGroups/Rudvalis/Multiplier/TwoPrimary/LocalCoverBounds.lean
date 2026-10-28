module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.ModelMap
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.CentralKernel
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.CentralIdentities
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.Reduction
public import Theory.GroupTheory.PerfectCentralCoverSquareObstruction

/-!
# The local Rudvalis two-primary cover bound

Every perfect central cover of the literal max4 is a quotient of the derived
subgroup of the seven-relator free central extension. Faithfulness of the
presentation identifies its kernel with the derived central kernel. Four
specific central identities then reduce that kernel to two involutions.

The first is the square of a lift of `max4First`. If that element has an
involutory lift in the cover, the exponent-two kernel makes all lift squares
equal, killing that first generator and leaving a kernel of order at most two.

The checked presentation and central identities discharge both inputs in
`max4CoverBounds`. Its ambient application retains only the independent
`FirstInvolutionLift` premise; final multiplier assembly belongs to its consumer.
Source: Aschbacher--Smith I.1.3(1), printed p.407.
-/

namespace Rudvalis.Multiplier.TwoPrimary
open PerfectCentralCovering SylowOvergroups LocalPresentation LocalPresentation.CentralKernel

variable {D : Type} [Group D] (c : Cover D max4)

private noncomputable def coverGenerator (i : Bool) : D :=
  Classical.choose (c.surjective (modelGenerator i))

private theorem coverGenerator_fac (i : Bool) :
    c.toMonoidHom (coverGenerator c i) = modelGenerator i :=
  Classical.choose_spec (c.surjective (modelGenerator i))

private noncomputable def coverFreeEvaluation : Free →* D := FreeGroup.lift (coverGenerator c)

private theorem coverFreeEvaluation_fac :
    c.toMonoidHom.comp (coverFreeEvaluation c) = modelEvaluation := by
  apply FreeGroup.ext_hom
  intro i
  simpa only [MonoidHom.comp_apply, coverFreeEvaluation, FreeGroup.lift_apply_of,
    modelEvaluation] using coverGenerator_fac c i

private theorem coverFreeEvaluation_relator_central (i : Fin 7) :
    coverFreeEvaluation c (relator i) ∈ Subgroup.center D := by
  apply c.ker_le_center
  change c.toMonoidHom (coverFreeEvaluation c (relator i)) = 1
  rw [← MonoidHom.comp_apply, coverFreeEvaluation_fac, modelEvaluation_relator]

private noncomputable def coverCentralEvaluation : Central →* D :=
  descend (coverFreeEvaluation c) (coverFreeEvaluation_relator_central c)

private theorem coverCentralEvaluation_fac :
    c.toMonoidHom.comp (coverCentralEvaluation c) = modelMap.comp centralProjection := by
  apply MonoidHom.ext
  intro x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective centralRelations x
  change c.toMonoidHom (coverFreeEvaluation c x) = modelMap (toPresented x)
  rw [modelMap_toPresented]
  exact DFunLike.congr_fun (coverFreeEvaluation_fac c) x

private theorem coverCentralEvaluation_surjective :
    Function.Surjective (coverCentralEvaluation c) := by
  let : Group.IsPerfect D := c.isPerfect
  exact surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    c.toMonoidHom (coverCentralEvaluation c)
    (by rw [coverCentralEvaluation_fac]; exact modelMap_surjective.comp centralProjection_surjective)
    c.ker_le_center

private theorem cover_kernel_preimage (hi : Function.Injective modelMap)
    (z : D) (hz : z ∈ c.toMonoidHom.ker) :
    ∃ x : Central, x ∈ commutator Central ∧ centralProjection x = 1 ∧
      coverCentralEvaluation c x = z := by
  let : Group.IsPerfect D := c.isPerfect
  have hD : (commutator Central).map (coverCentralEvaluation c) = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (coverCentralEvaluation_surjective c)]
    exact Group.IsPerfect.commutator_eq_top
  have hzD : z ∈ (commutator Central).map (coverCentralEvaluation c) := by rw [hD]; trivial
  obtain ⟨x, hxD, hxz⟩ := hzD
  refine ⟨x, hxD, ?_, hxz⟩
  apply hi
  rw [map_one]
  have hfac := DFunLike.congr_fun (coverCentralEvaluation_fac c) x
  change c.toMonoidHom (coverCentralEvaluation c x) = modelMap (centralProjection x) at hfac
  rw [← hfac, hxz]
  exact hz

/-- A faithful presentation and the four central word identities imply the
required local bound on the literal marked max4. -/
public theorem max4CoverBounds_of_presentation
    (hi : Function.Injective modelMap) (hc : CollectionIdentities) : Max4CoverBounds := by
  intro D _ _ c _
  let f := coverCentralEvaluation c
  let a : D := f (markedSquare : Central)
  let b : D := f (secondCycle : Central)
  have ha : a ^ 2 = 1 := by
    change f (markedSquare : Central) ^ 2 = 1
    rw [← map_pow, show (markedSquare : Central) ^ 2 = 1 from
      congrArg Subtype.val (markedSquare_sq hc), map_one]
  have hb : b ^ 2 = 1 := by
    change f (secondCycle : Central) ^ 2 = 1
    rw [← map_pow, show (secondCycle : Central) ^ 2 = 1 from
      congrArg Subtype.val hc.second_sq, map_one]
  have hab : Commute a b :=
    (show Commute (markedSquare : Central) (secondCycle : Central) from
      (Subgroup.mem_center_iff.mp markedSquare.property _).symm).map f
  have hall (z : D) (hz : z ∈ c.toMonoidHom.ker) : z = 1 ∨ z = a ∨ z = b ∨ z = a * b := by
    obtain ⟨x, hxD, hx, rfl⟩ := cover_kernel_preimage c hi z hz
    rcases derived_kernel_four_cases hc hxD hx with h | h | h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr (Or.inl (congrArg f h))
    · exact Or.inr (Or.inr (Or.inl (congrArg f h)))
    · exact Or.inr (Or.inr (Or.inr (by simpa only [map_mul] using congrArg f h)))
  have hexponent (z : D) (hz : z ∈ c.toMonoidHom.ker) : z ^ 2 = 1 := by
    rcases hall z hz with rfl | rfl | rfl | rfl
    · exact one_pow 2
    · exact ha
    · exact hb
    · rw [hab.mul_pow, ha, hb, one_mul]
  refine ⟨hexponent, ?_⟩
  rintro ⟨x, hx, hx2⟩
  have hmarked : c.toMonoidHom (f markedLift) = max4First := by
    change c.toMonoidHom (coverCentralEvaluation c markedLift) = _
    rw [← MonoidHom.comp_apply, coverCentralEvaluation_fac, MonoidHom.comp_apply,
      markedLift_projection, modelMap_first]
  have ha1 : a = 1 := by
    calc
      a = (f markedLift) ^ 2 := by rw [← map_pow, markedLift_sq]
      _ = x ^ 2 := square_eq_of_map_eq_of_kernel_exponent_two c.toMonoidHom
        c.ker_le_center hexponent (hmarked.trans hx.symm)
      _ = 1 := hx2
  have hbker : b ∈ c.toMonoidHom.ker := by
    change c.toMonoidHom (coverCentralEvaluation c (secondCycle : Central)) = 1
    rw [← MonoidHom.comp_apply, coverCentralEvaluation_fac, MonoidHom.comp_apply,
      secondCycle_projection, map_one]
  let bk : c.toMonoidHom.ker := ⟨b, hbker⟩
  let g : Bool → c.toMonoidHom.ker := fun i => if i then bk else 1
  have hg : Function.Surjective g := by
    intro z
    have hz : (z : D) = 1 ∨ (z : D) = b := by
      simpa only [ha1, one_mul, or_self, or_self_left] using hall z z.property
    rcases hz with hz | hz
    · exact ⟨false, Subtype.ext hz.symm⟩
    · exact ⟨true, Subtype.ext hz.symm⟩
  simpa using Nat.card_le_card_of_surjective g hg

/-- Actual application to the ambient reduction, retaining the independent
involution-lifting calculation and the two presentation obligations explicitly. -/
public theorem kernel_card_le_two_of_presentation
    (hi : Function.Injective modelMap) (hc : CollectionIdentities)
    (hlift : FirstInvolutionLift)
    {E : Type} [Group E] [Finite E] (c : Cover E Model)
    (hp : IsPGroup 2 c.toMonoidHom.ker) : Nat.card c.toMonoidHom.ker ≤ 2 :=
  kernel_card_le_two_of_local_bounds (max4CoverBounds_of_presentation hi hc) hlift c hp

/-- Perfect central covers of the actual max4 with two-group kernel have
kernel of exponent two. An involutory lift of the literal `max4First` further
bounds the kernel order by two. The presentation and collection calculations
discharge every premise of this local bound. -/
public theorem max4CoverBounds : Max4CoverBounds :=
  max4CoverBounds_of_presentation modelMap_injective collectionIdentities

/-- The local calculation discharges the max4 premise of the ambient Rudvalis
reduction. Only the independent marked involution-lifting input remains. -/
public theorem kernel_card_le_two_of_firstInvolutionLift
    (hlift : FirstInvolutionLift)
    {E : Type} [Group E] [Finite E] (c : Cover E Model)
    (hp : IsPGroup 2 c.toMonoidHom.ker) : Nat.card c.toMonoidHom.ker ≤ 2 :=
  kernel_card_le_two_of_local_bounds max4CoverBounds hlift c hp

end Rudvalis.Multiplier.TwoPrimary
