module

public import Theory.AlgebraicGroup.Semisimple.SolvableNormal
public import Theory.AlgebraicGroup.Variety.MorphicAction

/-!
# The kernel of a realized Borel-orbit action

An algebraic-group morphism realizing an action with exact Borel stabilizer
has kernel contained in that Borel. For a semisimple source the actual kernel
is therefore finite and central. The input is the literal action comparison;
no faithfulness or separability is assumed. This is the kernel step in
Borel §13.13 after the projective-line action is realized by PGL₂.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

namespace Bor1.RankOneGeometry
open Variety.Geometric
variable {K : Variety k} [AlgebraicGroup K] {X : Variety.Geometric k}

theorem action_morphism_kernel_finite_central
    (hG : IsSemisimpleAlgebraicGroup G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (A : MorphicAction G X) (x : Point X)
    (hstab : ∀ g : Variety.Point G,A.toMulAction.smul g x=x ↔ g∈B.toSubgroup)
    (D : MorphicAction K X) (φ : AlgebraicGroup.Morphism G K)
    (hφ : ∀ g p,D.toMulAction.smul (φ.onPoints g) p=A.toMulAction.smul g p) :
    Finite (Variety.Point φ.kernelClosedSubgroup.carrierVariety) ∧
      φ.kernelClosedSubgroup.toSubgroup ≤ Subgroup.center (Variety.Point G) := by
  apply semisimple_normal_le_borel_finite_central hG B hB φ.kernelClosedSubgroup
    (show φ.kernel.Normal from inferInstance)
  intro g hg
  apply (hstab g).mp
  rw [←hφ,show φ.onPoints g=1 from hg]
  exact D.toMulAction.one_smul x
end Bor1.RankOneGeometry
end Theory.AlgebraicGroup
