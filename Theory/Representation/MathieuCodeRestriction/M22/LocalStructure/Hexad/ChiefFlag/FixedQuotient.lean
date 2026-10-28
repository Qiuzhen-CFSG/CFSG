module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Spaces
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.FixedQuotient.Calculation
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.FixedQuotient.NativeActor

/-!
# The fixed-quotient branch of the outer M22 hexad code flag

Starting from the independently constructed chief/action data, the actual
six-point core gives the invariant-subspace alternatives. A nonidentity kernel
involution lifts to native M22; its checked centralizer supplies an order-three
actor preserving the source hexad. The dual conjugation marking bounds its
five-space displacement by two. The earlier scalar lower bound six on the
native ten-dimensional code then gives full displacement above V6 and excludes
V6 from the fixed quotient. V is excluded by the independent commutator
construction, leaving precisely the image of V5 in V/V1.

The only additional module scalar is the explicitly quantified native-M22
order-three displacement lower bound. Its construction and the construction
of the action data belong to the source-theorem assembly owner.

Source: Aschbacher--Smith, H.16.4(5), printed p.403, combined manuscript of
1 March 2004; earlier involution and odd displacement inputs are H.14 and H.13.
-/

public section
noncomputable section
namespace MathieuCode.Hexad.ChiefFlag
open Representation Representation.BinaryOffender
open FixedQuotientData

/-- H.16.4(5), conditional precisely on the independent action data and the
earlier scalar inputs. V5 is the actual coinvariant kernel throughout. -/
theorem fixedCodeQuotient_eq_commutatorImage
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (D : FixedQuotientData.Actions E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad)
    (hβ : ∀ u : Sporadic.Mathieu.M22, orderOf u = 3 →
      6 ≤ fixedCodim m22CodeRepresentation (Subgroup.zpowers u)) :
    fixedCodeQuotient = commutatorImage := by
  let : Nontrivial Kernel :=
    (Subgroup.nontrivial_iff_ne_bot Kernel).mpr (h.kernel_ne_bot h24.fixed_finrank)
  obtain ⟨z, hz⟩ := exists_ne (1 : Kernel)
  have hzsq : z ^ 2 = 1 := by
    apply D.kernelMarking.symm.injective
    rw [map_pow, map_one, pow_two]
    change Multiplicative.toAdd (D.kernelMarking.symm z) +
      Multiplicative.toAdd (D.kernelMarking.symm z) = 0
    simpa only [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul, one_smul] using
      (add_smul (1 : ZMod 2) 1 (Multiplicative.toAdd (D.kernelMarking.symm z))).symm
  have hz2 : orderOf z = 2 := orderOf_eq_prime hzsq hz
  obtain ⟨y, u, hy, hu, huy, hyz⟩ := FixedQuotientNative.commuting_cubic h z hz2
  have hf : fixedSpace codeAction (Subgroup.zpowers y) =
      fixedSpace m22CodeRepresentation (Subgroup.zpowers u) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff, mem_fixedSpace_zpowers_iff]
    change m22OuterCodeRepresentation y.val v = v ↔ m22CodeRepresentation u v = v
    rw [← huy, m22OuterCodeRepresentation_restrict]
  have hm : 6 ≤ fixedCodim codeAction (Subgroup.zpowers y) := by
    unfold fixedCodim
    rw [hf]
    exact hβ u hu
  have hs := fixedLift_ne_six_of_cubic D h h24 y hy z hz hyz hm
  have he : fixedLift = V5 := by
    rcases subrepresentation_alternatives D h h24 fixedLift (five_le_fixedLift D) with
      he | he | he
    · exact he
    · exact (hs he).elim
    · exact (fixedLift_ne_top h h24 he).elim
  have he' := congrArg (fun W : Subrepresentation codeAction =>
    W.toSubmodule.map V1.toSubmodule.mkQ) he
  change (fixedCodeQuotient.comap V1.toSubmodule.mkQ).map V1.toSubmodule.mkQ =
    V5.toSubmodule.map V1.toSubmodule.mkQ at he'
  rw [Submodule.map_comap_eq_of_surjective V1.toSubmodule.mkQ_surjective,
    codeCommutatorSubrepresentation_space] at he'
  exact he'

end MathieuCode.Hexad.ChiefFlag
