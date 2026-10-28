module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.Basic
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.CentralExtensions.Characters

/-!
# Four central extensions on the genuine outer M₁₂ endpoint

The two certified binary characters vanish on the central involution `z`.
Their four binary combinations yield involutory central automorphisms of the
literal first endpoint. They fix the first overlap generator and independently
multiply the second and third by the marked central involution. Thus
`central_extensions` discharges exactly the endpoint-extension premise of
`all_extend_of_coverage`; the separate generator-image coverage remains with
that theorem's assembly owner.

Source context: Aschbacher--Smith F.1.11--12, pp.262--263, E.2.16, p.228, and
14.2.21, p.988, `refs/quasithin.pdf`. The actual degree-24 ATLAS carrier and its
corrected nonsplit first core are retained throughout. This proves the specified
finite endpoint calculation, not the full source rigidity theorem by itself.
-/
@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions
open Theory.GroupTheory.CentralInvolutionTwist

/-- The central mark in the genuine first endpoint. -/
def endpointMarked : firstParabolic := VerifiedPair.amalgam.left marked

theorem endpointMarked_coe : (endpointMarked : Carrier) = z := marked_coe

theorem endpointMarked_square : endpointMarked * endpointMarked = 1 := by
  apply Subtype.ext
  change (endpointMarked : Carrier) * (endpointMarked : Carrier) = 1
  rw [endpointMarked_coe, ← pow_two, FirstParabolic.z_square]

theorem endpointMarked_central : endpointMarked ∈ Subgroup.center firstParabolic := by
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply Subtype.ext
  change (x : Carrier) * (endpointMarked : Carrier) = (endpointMarked : Carrier) * x
  rw [endpointMarked_coe]
  exact Subgroup.mem_centralizer_singleton_iff.mp x.property

/-- Independently activate the second- and third-generator characters. -/
noncomputable def centralCharacter (p q : Bool) : firstParabolic →* C2 :=
  (if p then Endpoint.character 0 else 1) * (if q then Endpoint.character 1 else 1)

theorem centralCharacter_marked (p q : Bool) : centralCharacter p q endpointMarked = 1 := by
  cases p <;> cases q <;>
    simp [centralCharacter, endpointMarked, Endpoint.character_marked]

theorem centralCharacter_generator (p q : Bool) (j : Fin 3) :
    centralCharacter p q (VerifiedPair.amalgam.left (Overlap.generator j)) =
      if (j = 1 ∧ p = true) ∨ (j = 2 ∧ q = true) then Multiplicative.ofAdd 1 else 1 := by
  cases p <;> cases q <;> fin_cases j <;>
    simp [centralCharacter, Endpoint.character_overlap_generator]

/-- Central displacement by the selected parity character. -/
noncomputable def centralExtension (p q : Bool) : MulAut firstParabolic :=
  ofCharacter endpointMarked endpointMarked_square endpointMarked_central
    (centralCharacter p q) (centralCharacter_marked p q)

theorem centralExtension_generator (p q : Bool) (j : Fin 3) :
    centralExtension p q (VerifiedPair.amalgam.left (Overlap.generator j)) =
      VerifiedPair.amalgam.left (centralImage p q j) := by
  rw [centralExtension, ofCharacter_apply, centralCharacter_generator]
  unfold centralImage
  rw [map_mul]
  split_ifs <;> simp [endpointMarked, ZMod.val_one_eq_one_mod]

/-- All four central changes of the shared triple extend to actual automorphisms
of the nonsplit first endpoint. This is precisely the `hext` input of
`all_extend_of_coverage`; generator-image coverage is a separate calculation. -/
theorem central_extensions : ∀ p q : Bool, ∃ a : MulAut firstParabolic, ∀ j,
    a (VerifiedPair.amalgam.left (Overlap.generator j)) =
      VerifiedPair.amalgam.left (centralImage p q j) :=
  fun p q => ⟨centralExtension p q, centralExtension_generator p q⟩

end Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions
