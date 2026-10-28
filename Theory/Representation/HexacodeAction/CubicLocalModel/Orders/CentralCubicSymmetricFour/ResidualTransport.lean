module

public import Theory.Representation.HexacodeAction.CubicLocalModel.Orders.Intrinsic
public import Theory.GroupTheory.PCoreSurjective

/-!
# Intrinsic commutator residuals through two-group kernels

Surjections preserve finite two-residuals and commutators, hence preserve
the intrinsic commutator residual attached to a Sylow two-subgroup. If the
kernel is a two-group, the restricted map on that residual again has a
two-group kernel. Pulling back the target two-core identifies the source
two-core and gives an isomorphism of the two-core quotients.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1, printed p.877. All cores here are intrinsic to the residual;
normality in the original ambient group is unnecessary.
-/

public section

noncomputable section
open Subgroup
namespace Representation.Hexacode.CubicLocalModel.Orders
variable {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]

omit [Finite Y] in
/-- Surjections preserve the intrinsic commutator residual. -/
theorem intrinsicCommutatorResidual_map_of_surjective
    (f : X →* Y) (hf : Function.Surjective f) (P : Sylow 2 X) :
    (intrinsicCommutatorResidual P).map f =
      intrinsicCommutatorResidual (P.mapSurjective hf) := by
  unfold intrinsicCommutatorResidual
  rw [map_embedded_pResidual, map_commutator,
    map_pResidual_of_surjective 2 f hf, Sylow.coe_mapSurjective]

/-- Killing a normal two-subgroup preserves the order of the intrinsic
commutator residual modulo its intrinsic two-core. -/
theorem intrinsicCommutatorResidual_quotient_card_of_two_kernel
    (f : X →* Y) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (P : Sylow 2 X) :
    Nat.card (intrinsicCommutatorResidual P ⧸ pCore 2 (intrinsicCommutatorResidual P)) =
      Nat.card (intrinsicCommutatorResidual (P.mapSurjective hf) ⧸
        pCore 2 (intrinsicCommutatorResidual (P.mapSurjective hf))) := by
  let R := intrinsicCommutatorResidual P
  let S := R.map f
  let g : R →* S := f.subgroupMap R
  have hg : Function.Surjective g := f.subgroupMap_surjective R
  have hgk : IsPGroup 2 g.ker := by
    rw [Subgroup.ker_subgroupMap]
    exact hk.comap_subtype
  let q := (QuotientGroup.mk' (pCore 2 S)).comp g
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hg
  have hqk : q.ker = pCore 2 R := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact g.comap_pCore_of_ker_isPGroup hg hgk
  let e : (R ⧸ pCore 2 R) ≃* (S ⧸ pCore 2 S) :=
    (QuotientGroup.quotientMulEquivOfEq hqk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have hS : S = intrinsicCommutatorResidual (P.mapSurjective hf) :=
    intrinsicCommutatorResidual_map_of_surjective f hf P
  exact (Nat.card_congr e.toEquiv).trans (by rw [hS])

end Representation.Hexacode.CubicLocalModel.Orders
