module

public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.FirstParabolic.Intrinsic
public import Theory.GroupTheory.QuaternionSwapModel.Parabolic

/-!
# The split parabolic cannot model the first outer parabolic

An isomorphism of the whole parabolics would identify their intrinsic
two-cores. The split model's two-core is its copy of QuaternionSwapModel.QH,
which has twenty-eight square-one elements, while the actual first core
has twenty. Thus even an unmarked isomorphism of the parabolics is impossible.
The existing split model and its conditional interfaces are preserved.

This is a structural obstruction, independent of GAP SmallGroup labels.
The replacement core and action are the concrete outerCore and wreathAction
exported by Intrinsic; both are identified with the actual first parabolic.

Source: Aschbacher--Smith, F.1.12(I)(13), printed p.263, and the proof of
14.2.21, printed p.988, refs/quasithin.pdf.
-/

public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic

/-- No isomorphism, even without generator markings, identifies these parabolics. -/
theorem firstParabolic_not_equiv_split (m : InnerModel) :
    ¬ Nonempty (firstParabolic ≃* QuaternionSwapModel.H0) := by
  rintro ⟨e⟩
  let coreEquiv : pCore 2 firstParabolic ≃* pCore 2 QuaternionSwapModel.H0 :=
    (e.subgroupMap (pCore 2 firstParabolic)).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  let splitEquiv : pCore 2 QuaternionSwapModel.H0 ≃* QuaternionSwapModel.QH :=
    (MulEquiv.subgroupCongr QuaternionSwapModel.pcore_eq_i_range).trans
      (MonoidHom.ofInjective QuaternionSwapModel.i_inj).symm
  exact intrinsicCore_not_equiv_split m ⟨coreEquiv.trans splitEquiv⟩

end Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic
