module

public import Theory.AlgebraicGroup.Morphism.Connected
public import Theory.AlgebraicGroup.Morphism.ClosedImage
public import Theory.AlgebraicGroup.Radical.Defs

universe u

/-!
Preimages of connected solvable closed subgroups under a point-surjective
algebraic-group morphism have a useful quotient certificate even when the
ambient kernel is nonsolvable.  The identity component of the preimage maps
onto the target subgroup, so its quotient by the restricted kernel is
solvable.  A separate containment theorem records the exact additional input
needed to place that identity component in a source radical: solvability of
the identity component itself.  This separation is intentional, since target
solvability alone does not imply solvability of a preimage with nonsolvable
kernel (for example, a projection from a semisimple product to one factor).
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The quotient of the identity component of a preimage by its restricted
kernel is solvable.  No solvability assumption on the ambient kernel is used.

The proof uses the surjectivity of the identity-component preimage image and
the standard quotient-by-kernel equivalence; this is the quotient transfer
interface needed before any source-radical containment argument. -/
public theorem Morphism.preimage_identityComponent_quotient_isSolvable
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (hf : Function.Surjective f.onPoints)
    (S : ClosedSubgroup H)
    (hSconn : _root_.IsConnected (S : Set (Variety.Point H)))
    (hSsolv : Group.IsSolvable (Variety.Point S.carrierVariety)) :
    let P := f.closedSubgroupPreimage S
    let I := P.identityComponentAmbient
    Group.IsSolvable
      (Variety.Point I.carrierVariety ⧸ (f.comp I.inclusion).onPoints.ker) := by
  let P := f.closedSubgroupPreimage S
  let I := P.identityComponentAmbient
  let q := f.comp I.inclusion
  have hImage : q.imageClosedSubgroup = S :=
    f.closedSubgroupPreimage_identityComponent_image_eq hf S hSconn
  let hmap : ∀ x : Variety.Point I.carrierVariety,
      q.onPoints x ∈ S.toSubgroup := by
    intro x
    have hx : q.onPoints x ∈ q.imageClosedSubgroup.toSubgroup := ⟨x, rfl⟩
    rw [hImage] at hx
    exact hx
  let qS : AlgebraicGroup.Morphism I.carrierVariety S.carrierVariety :=
    q.codRestrictClosedSubgroup S hmap
  have hqSsurj : Function.Surjective qS.onPoints := by
    intro y
    have hy : S.inclusion.onPoints y ∈ q.imageClosedSubgroup.toSubgroup := by
      rw [hImage]
      exact (S.pointEquiv y).property
    rcases hy with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply S.inclusion_injective
    rw [q.codRestrictClosedSubgroup_inclusion_apply]
    exact hx
  let : Group.IsSolvable (S.toSubgroup) := by
    exact Group.isSolvable_of_surjective
      (f := (Equiv.mulEquiv S.pointEquiv).toMonoidHom)
      S.pointEquiv.surjective
  have hqker : qS.kernel = q.onPoints.ker :=
    q.codRestrictClosedSubgroup_kernel_eq S hmap
  let eS : (Variety.Point I.carrierVariety ⧸ qS.kernel) ≃*
      S.toSubgroup :=
    (QuotientGroup.quotientKerEquivOfSurjective qS.onPoints hqSsurj).trans
      (Equiv.mulEquiv S.pointEquiv)
  let eK : (Variety.Point I.carrierVariety ⧸ q.onPoints.ker) ≃*
      (Variety.Point I.carrierVariety ⧸ qS.kernel) :=
    QuotientGroup.quotientMulEquivOfEq hqker.symm
  let e : (Variety.Point I.carrierVariety ⧸ q.onPoints.ker) ≃*
      S.toSubgroup :=
    eK.trans eS
  exact Group.isSolvable_of_isSolvable_injective
    (f := e.toMonoidHom) e.injective

/-- If the identity component of a target-radical preimage is known to be
solvable, then it lies in any source radical.  The proof uses only normality
of the target subgroup, connectedness of the identity component, and the
defining maximality of the source radical; in particular it does not assume
that the ambient morphism kernel is solvable. -/
public theorem IsRadicalSubgroup.preimage_identityComponent_le_of_isSolvable
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    {R : ClosedSubgroup G} (hR : IsRadicalSubgroup R)
    {S : ClosedSubgroup H} (hSnormal : S.toSubgroup.Normal)
    (hIsolvable :
      Group.IsSolvable
        (Variety.Point
          (f.closedSubgroupPreimage S).identityComponentAmbient.carrierVariety)) :
    (f.closedSubgroupPreimage S).identityComponentAmbient ≤ R := by
  let P := f.closedSubgroupPreimage S
  let I := P.identityComponentAmbient
  have hInormal : I.toSubgroup.Normal :=
    P.identityComponentAmbient_normal_of_normal
      (f.closedSubgroupPreimage_normal hSnormal)
  have hIconnected : _root_.IsConnected (I : Set (Variety.Point G)) :=
    P.identityComponentAmbient_isConnected
  exact hR.maximal I hInormal hIconnected hIsolvable

end Theory.AlgebraicGroup
