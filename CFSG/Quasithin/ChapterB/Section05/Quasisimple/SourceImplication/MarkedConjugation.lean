module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry
/-!
# Conjugation through a marked action equivalence

The subgroup marking is compatible with the whole actor marking. Hence
conjugation by an actor element transports to conjugation in its marked
normal component. This is the group part of B.5's marked action convention.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {D V E W : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [Group E] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) E W}
  {H L : Subgroup D} {M : Subgroup E} [M.Normal]
theorem MarkedActionEquiv.marked_conjugation (e : MarkedActionEquiv ρ H L σ M)
    (h : H) (l : L) :
    ((e.subgroupEquiv.symm (MulAut.conjNormal (e.action.groupEquiv h)
        (e.subgroupEquiv l)) : L) : D) = (h : D) * (l : D) * (h : D)⁻¹ := by
  let a := e.subgroupEquiv.symm (MulAut.conjNormal (e.action.groupEquiv h) (e.subgroupEquiv l))
  have he : (⟨a,e.contained a.property⟩ : H) =
      h * (⟨l,e.contained l.property⟩ : H) * h⁻¹ := by
    apply e.action.groupEquiv.injective
    rw [e.compatible, map_mul, map_mul, map_inv,e.compatible]
    rw [show e.subgroupEquiv a = MulAut.conjNormal (e.action.groupEquiv h)
      (e.subgroupEquiv l) from e.subgroupEquiv.apply_symm_apply _]
    rfl
  exact congrArg Subtype.val he
end CFSG.Quasithin.ChapterB.QuasisimpleSource

