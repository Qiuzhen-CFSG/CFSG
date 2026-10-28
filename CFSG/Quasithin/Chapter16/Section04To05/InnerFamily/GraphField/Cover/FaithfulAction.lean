module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Cover.Kernel
public import Theory.SpecificGroups.GL2.ThreeQuaternionUniqueness.Faithful

/-!
# The quaternion contradiction through the actual action image

The exact residual-action kernel constructs an isomorphism from M/E to
its image in GL₂(3). Under this faithful representation Q/E is an actual
quaternion subgroup, hence the unique such subgroup of GL₂(3). Pullback
makes Q normal in M, contradicting the two marked transvections and the
transitive Y-action in Cover.Actions.

This is a stronger terminal argument than the surjective-quotient version
in the source: quaternion uniqueness already applies to a subgroup of
GL₂(3). It avoids the separate SL₂(3)-image and determinant calculations;
no faithful kernel, action dichotomy, or quotient identification is taken
as a source premise in the final Cover theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1191.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.GraphField
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {r z : G} {L : Subgroup G}

/-- The actual quotient by E embeds in GL₂(3) through conjugation on D.
Quaternion uniqueness forces Q to be normal in the actual cover overgroup. -/
theorem cover_normal_of_faithful_residual_action
    (d : NormalizerData L r z) (hQ : d.Q ≤ coverOvergroup T r z)
    (hD : IsElementaryAbelian 3 (residual L r)) (h9 : Nat.card (residual L r) = 9)
    (hDN : coverOvergroup T r z ≤ normalizer (residual L r : Set G))
    (hK : (coverResidualAction T r z (residual L r) hDN).ker =
      (fourGroup r z).subgroupOf (coverOvergroup T r z)) :
    (d.Q.subgroupOf (coverOvergroup T r z)).Normal := by
  let M := coverOvergroup T r z
  let E := fourGroup r z
  let A := d.Q.subgroupOf M
  let F := E.subgroupOf M
  let f := coverMatrixAction T r z (residual L r) hD h9 hDN
  have hfK : f.ker = F := coverMatrixAction_kernel_eq T r z (residual L r) hD h9 hDN hK
  let e : (M ⧸ F) ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hfK.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  let ρ := f.range.subtype.comp e.toMonoidHom
  have hρ : Function.Injective ρ := f.range.subtype_injective.comp e.injective
  let _ : (E.subgroupOf d.Q).Normal :=
    normal_subgroupOf_of_le_normalizer d.normalizes_four
  let b : A ≃* d.Q := subgroupOfEquivOfLe hQ
  have hb : (F.subgroupOf A).map b.toMonoidHom = E.subgroupOf d.Q := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      change (x : G) ∈ E
      have hyE : ((y : A) : G) ∈ E := hy
      have heval := congrArg (fun q : d.Q => (q : G)) he
      exact heval ▸ hyE
    · intro hx
      refine ⟨b.symm x, ?_, b.apply_symm_apply x⟩
      exact hx
  let a := QuotientGroup.congr (F.subgroupOf A) (E.subgroupOf d.Q) b hb
  obtain ⟨eQ⟩ := d.quaternion
  exact Matrix.GeneralLinearGroup.normal_of_three_faithful_quotient F A
    (fun _ hx => d.four_le hx) ρ hρ ⟨a.trans eQ⟩

end CFSG.Quasithin.Chapter16.Intersections.GraphField
