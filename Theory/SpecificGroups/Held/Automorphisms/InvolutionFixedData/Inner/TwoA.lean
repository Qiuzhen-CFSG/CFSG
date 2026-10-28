module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Reduction
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.Model
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.FiniteStructure
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.ProjectiveComparison
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# The actual Held 2A perfect central cover

A central kernel of order four in the derived subgroup's actual permutation
action, with faithful image isomorphic to matrix PSL₃(4), is the entire
center: PSL₃(4) is centerless. The first isomorphism theorem then constructs
the central-quotient isomorphism. Perfectness and simplicity of PSL₃(4)
give quasisimplicity. The kernel and image orders give 80640, and centralizer
order 161280 gives relative index two.

The final theorem discharges every input using the checked finite structure
and projective comparison. Its witness is the literal derived subgroup from
`TwoA.Model`, normal in the fixed subgroup of conjugation by `Held.a`.
No splitting of the cover is assumed. The existing ATLAS port proves the
needed matrix simplicity and perfectness, with its original attribution.

Source: GLS3 Table 5.3p and the perfect-cover convention on printed pp.260–261.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace Held.InvolutionFixedData.TwoA

private theorem psl_center_eq_bot :
    center Matrix.PSL3Four.PSL = ⊥ := by
  let : Group.IsPerfect Matrix.PSL3Four.SL := Atlas.sl_perfect 3 (by decide)
  exact Group.IsPerfect.center_quotient_center_eq_bot Matrix.PSL3Four.SL

/-- Compose the actual orbit action with a comparison of its image with PSL₃(4). -/
noncomputable def projection (e : orbitImage ≃* Matrix.PSL3Four.PSL) :
    derived →* Matrix.PSL3Four.PSL := e.toMonoidHom.comp orbitAction.rangeRestrict

theorem projection_surjective (e : orbitImage ≃* Matrix.PSL3Four.PSL) :
    Function.Surjective (projection e) :=
  e.surjective.comp orbitAction.rangeRestrict_surjective

theorem projection_ker (e : orbitImage ≃* Matrix.PSL3Four.PSL) :
    (projection e).ker = orbitKernel := by
  ext x
  change e (orbitAction.rangeRestrict x) = 1 ↔ orbitAction x = 1
  rw [← e.map_one, e.injective.eq_iff]
  exact Subtype.ext_iff

/-- A central orbit kernel is the full center once its image is identified with PSL₃(4). -/
theorem orbitKernel_eq_center
    (e : orbitImage ≃* Matrix.PSL3Four.PSL)
    (hcentral : orbitKernel ≤ center derived) : orbitKernel = center derived := by
  apply le_antisymm hcentral
  intro x hx
  rw [← projection_ker e]
  change projection e x = 1
  have hz : projection e x ∈ center Matrix.PSL3Four.PSL := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := projection_surjective e y
    simpa only [← map_mul] using congrArg (projection e) (Subgroup.mem_center_iff.mp hx z)
  simpa only [psl_center_eq_bot, Subgroup.mem_bot] using hz

/-- The first isomorphism theorem gives the required isomorphism of the actual central quotient. -/
noncomputable def quotientCenterEquiv
    (e : orbitImage ≃* Matrix.PSL3Four.PSL)
    (hcentral : orbitKernel ≤ center derived) :
    (derived ⧸ center derived) ≃* Matrix.PSL3Four.PSL :=
  (QuotientGroup.quotientMulEquivOfEq (orbitKernel_eq_center e hcentral).symm).trans
    ((QuotientGroup.quotientKerEquivRange orbitAction).trans e)

/-- The central-kernel order and projective image determine the candidate order. -/
theorem derived_card (e : orbitImage ≃* Matrix.PSL3Four.PSL)
    (hk : Nat.card orbitKernel = 4) : Nat.card derived = 80640 := by
  have hc := orbitKernel.card_mul_index
  rw [Subgroup.index_ker, Nat.card_congr e.toEquiv, Matrix.PSL3Four.card_PSL, hk] at hc
  exact hc.symm

/-- Conditional assembly from the finite subgroup calculation and projective image comparison.
The concrete perfectness, centralizer order, kernel data and image equivalence remain
producer obligations; this theorem does not assert the unconditional 2A row. -/
theorem hasPSL3FourNormalOfIndexTwo_of_orbit
    [Group.IsPerfect derived]
    (hc : Nat.card centralizer = 161280)
    (hk : Nat.card orbitKernel = 4)
    (hcentral : orbitKernel ≤ center derived)
    (e : orbitImage ≃* Matrix.PSL3Four.PSL) :
    HasPSL3FourNormalOfIndexTwo (MulAut.conj a).fixedSubgroup := by
  let : IsSimpleGroup Matrix.PSL3Four.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  have hq : IsQuasisimple derived :=
    { simple := (quotientCenterEquiv e hcentral).isSimpleGroup }
  have hi : derived.index = 2 := by
    have h := derived.card_mul_index
    rw [derived_card e hk, hc] at h
    omega
  have hz : Nat.card (center derived) = 4 := by
    rw [← orbitKernel_eq_center e hcentral]
    exact hk
  exact ⟨derived, inferInstance, hq, hi, hz, ⟨quotientCenterEquiv e hcentral⟩⟩

/-- The literal Held 2A fixed subgroup contains its derived subgroup as a normal
quasisimple subgroup of index two, with center of order four and central quotient
isomorphic to matrix PSL₃(4). All finite and model-comparison inputs are proved. -/
theorem hasPSL3FourNormalOfIndexTwo :
    HasPSL3FourNormalOfIndexTwo (MulAut.conj a).fixedSubgroup := by
  obtain ⟨e⟩ := ProjectiveComparison.nonempty_equiv
    FiniteStructure.centralizer_card FiniteStructure.orbitKernel_card
  exact hasPSL3FourNormalOfIndexTwo_of_orbit FiniteStructure.centralizer_card
    FiniteStructure.orbitKernel_card FiniteStructure.orbitKernel_central e

end Held.InvolutionFixedData.TwoA
