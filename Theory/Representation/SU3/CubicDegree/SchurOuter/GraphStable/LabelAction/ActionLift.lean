module

public import Theory.Representation.SU3.CubicDegree.SchurOuter.GraphStable.LabelAction.MatrixLift
public import Theory.Representation.SU3.BinaryDegree.Perfectness
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.Representation.BinaryOffender.CentralKernelImage
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.PerfectCentralCoverExistence
import all Theory.Representation.BinaryOffender.CentralKernelImage

/-!
# The literal action image of an outer involution

A central-kernel representation of SU₃ has perfect image, with genuine central
quotient PSU₃. The quotient detects inner automorphisms. Lift its outer
involution by the matrix normal form, then use uniqueness of maps from a
perfect group to a central extension to remove the possible central error.
The resulting equation holds in the original linear action image.
The internal import supplies the computation of the existing quotient
equivalence on a representative; no existing public boundary is changed.

Source: GM04, Proposition 4.11, internal pp.31--32.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open BenderSuzuki.MatrixGroups Matrix Subgroup
open Representation Representation.BinaryOffender
namespace Representation.SU3.CubicDegree.SchurOuter.GraphStable.LabelAction
variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
  [Module (ZMod 2) V] (J : HermitianForm 3 F)

/-- Lift the conjugation of a literal normalizer involution to the original SU₃,
retaining both the exact action-image equation and the semilinear matrix formula. -/
theorem outer_normalizer_matrix_lift
    {s : ℕ} (hs : 2 ≤ s) (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (σ : Representation (ZMod 2) J.specialSubgroup V)
    (hk : σ.ker ≤ center J.specialSubgroup)
    (t : linearNormalizer σ) (ht : t ^ 2 = 1)
    (ho : (actionImage σ).normalizerMonoidHom t ∉ MulAut.innerSubgroup (actionImage σ)) :
    ∃ (β : MulAut J.specialSubgroup) (D : GL (Fin 3) F),
      (∀ g, actionHom σ (β g) =
        (actionImage σ).normalizerMonoidHom t (actionHom σ g)) ∧
      (∀ g, (β g).val = D * GeneralLinearGroup.map J.conj.toRingHom g.val * D⁻¹) := by
  let : Group.IsPerfect J.specialSubgroup :=
    Representation.SU3.BinaryDegree.isPerfect_specialSubgroup J hs hcard hconj
  let : Group.IsPerfect (actionImage σ) :=
    Group.IsPerfect.ofSurjective σ.asGroupHom.rangeRestrict_surjective
  have hz := J.specialToProjective_ker_eq_center
    (HermitianForm.EvenProjectiveComparison.center_eq_bot J (by omega) hcard hconj)
  let f : J.specialSubgroup ⧸ center J.specialSubgroup ≃*
      ProjectiveSpecialUnitaryMatrixGroup J :=
    (QuotientGroup.quotientMulEquivOfEq hz.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective
        J.specialToProjective_surjective)
  let e : actionImage σ ⧸ center (actionImage σ) ≃*
      ProjectiveSpecialUnitaryMatrixGroup J :=
    (simpleQuotientEquivImage σ hk).symm.trans f
  have he (g : J.specialSubgroup) :
      e (QuotientGroup.mk' (center (actionImage σ)) (actionHom σ g)) =
        J.specialToProjective g := by
    change f ((simpleQuotientEquivImage σ hk).symm _) = _
    rw [← show simpleQuotientEquivImage σ hk
        (QuotientGroup.mk' (center J.specialSubgroup) g) =
          QuotientGroup.mk' (center (actionImage σ)) (actionHom σ g) from rfl,
      MulEquiv.symm_apply_apply]
    rfl
  let α := (actionImage σ).normalizerMonoidHom t
  let a := MulAut.centralQuotientAction e α
  have ha : a ^ 2 = 1 := by
    change (MulAut.centralQuotientAction e ((actionImage σ).normalizerMonoidHom t)) ^ 2 = 1
    rw [← map_pow, ← map_pow, ht, map_one, map_one]
  have hoa : ¬ ∃ x, a = MulAut.conj x := by
    intro hi
    obtain ⟨x, hx⟩ := (MulAut.centralQuotientAction_inner_iff e α).mp hi
    exact ho ⟨x, hx.symm⟩
  obtain ⟨β, D, hp, hm⟩ := outer_involution_matrix_lift J hs hcard hconj a ha hoa
  refine ⟨β, D, ?_, hm⟩
  have hmaps : (actionHom σ).comp β.toMonoidHom = α.toMonoidHom.comp (actionHom σ) := by
    apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
      (QuotientGroup.mk' (center (actionImage σ)))
      (by rw [QuotientGroup.ker_mk'])
    ext g
    apply e.injective
    change e (QuotientGroup.mk' (center (actionImage σ)) (actionHom σ (β g))) =
      e (QuotientGroup.mk' (center (actionImage σ)) (α (actionHom σ g)))
    rw [he, hp, ← MulAut.centralQuotientAction_apply, he]
  exact fun g => DFunLike.congr_fun hmaps g

end Representation.SU3.CubicDegree.SchurOuter.GraphStable.LabelAction
