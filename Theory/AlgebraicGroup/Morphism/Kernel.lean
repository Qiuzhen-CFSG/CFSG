module

public import Theory.AlgebraicGroup.Morphism.Basic
public import Theory.AlgebraicGroup.Variety.Zariski

universe u

/-! Closed kernels of algebraic-group morphisms. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

public lemma Morphism.kernel_isZariskiClosed {G H : Variety k}
    [AlgebraicGroup G] [AlgebraicGroup H] (f : AlgebraicGroup.Morphism G H) :
    IsZariskiClosed G (f.kernel : Set (Variety.Point G)) := by
  have hclosed := f.toVariety.isZariskiClosed_preimage
    (isZariskiClosed_singleton H (1 : Variety.Point H))
  have hset :
      (f.kernel : Set (Variety.Point G)) =
        f.toVariety.toFun ⁻¹' ({1} : Set (Variety.Point H)) := by
    ext x
    change (f.onPoints x = 1) ↔ (f.toVariety.toFun x = 1)
    rfl
  rw [hset]
  exact hclosed

end Theory.AlgebraicGroup
