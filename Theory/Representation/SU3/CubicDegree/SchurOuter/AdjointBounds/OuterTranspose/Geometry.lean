module

public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose.Geometry.AdjointTransport
public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose.Geometry.ProjectiveNormalForm
public import Theory.Representation.SU3.BinaryDegree.Perfectness
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.Representation.BinaryOffender.CentralKernelImage
public import Theory.GroupAction.PerfectCentralQuotient
import all Theory.Representation.BinaryOffender.CentralKernelImage

/-!
# The adjoint graph operator on a central-kernel action image

The perfect action image has the genuine PSU₃ central quotient. Its induced
automorphism retains square one and non-innerness. A projective matrix
coordinate equation therefore yields an adjoint graph operator for all
related SU₃ representatives, even when the original action has central kernel.

The natural-matrix coordinate existence theorem is supplied by outer-involution
normal form, unitary descent, and Hermitian basis transport. Thus the final
geometric intertwiner has no coordinate or representation-model premise.
The internal import is used only to compute the existing central-quotient equivalence on a literal
representative, as in `GraphStable.LabelAction.ActionLift`; it changes no
public boundary of that module.

Source: GM04, Proposition 4.11, internal pp.31--32.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open BenderSuzuki.MatrixGroups Subgroup
open Representation Representation.BinaryOffender

namespace Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose
open Geometry
variable {F K V : Type*} [Field F] [Finite F] [Field K]
  [AddCommGroup V] [Module (ZMod 2) V] (J : HermitianForm 3 F)

/-- Reduction of the requested geometric intertwiner to a natural-matrix
normal form on PSU₃. The remaining premise contains no binary representation,
Schur model, or adjoint operator. -/
theorem adjointGraphIntertwiner_of_projectiveCoordinates
    {s : ℕ} (hs : 2 ≤ s) (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (hnorm : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      a ^ 2 = 1 → (¬ ∃ x, a = MulAut.conj x) → HasProjectiveTransposeCoordinates J a)
    (σ : Representation (ZMod 2) J.specialSubgroup V)
    (hk : σ.ker ≤ center J.specialSubgroup)
    (ι : F →+* K) (t : linearNormalizer σ) (ht : t ^ 2 = 1)
    (ho : (actionImage σ).normalizerMonoidHom t ∉ MulAut.innerSubgroup (actionImage σ)) :
    AdjointGraphIntertwiner J ι (actionHom σ) ((actionImage σ).normalizerMonoidHom t) := by
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
  apply adjointGraphIntertwiner_of_matrixCoordinates
  apply matrixCoordinates_of_projectiveCoordinates J (actionHom σ) α a (hnorm a ha hoa)
  intro g h hgh
  rw [← he h, hgh, ← MulAut.centralQuotientAction_apply, he]

/-- Every literal outer involution on a central-kernel binary action of SU₃
has a transpose-conjugate intertwiner on the actual trace-zero adjoint space.
The covariance holds for every related pair of special-unitary representatives.
No irreducibility or choice of an adjoint model for the original action is needed. -/
theorem adjointGraphIntertwiner_of_outer_involution
    {s : ℕ} (hs : 2 ≤ s) (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (σ : Representation (ZMod 2) J.specialSubgroup V)
    (hk : σ.ker ≤ center J.specialSubgroup)
    (ι : F →+* K) (t : linearNormalizer σ) (ht : t ^ 2 = 1)
    (ho : (actionImage σ).normalizerMonoidHom t ∉ MulAut.innerSubgroup (actionImage σ)) :
    AdjointGraphIntertwiner J ι (actionHom σ) ((actionImage σ).normalizerMonoidHom t) :=
  adjointGraphIntertwiner_of_projectiveCoordinates J hs hcard hconj
    (hasProjectiveTransposeCoordinates_of_outer_involution J hs hcard hconj) σ hk ι t ht ho

end Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose
