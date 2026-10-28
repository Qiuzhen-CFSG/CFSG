module
public import Theory.SpecificGroups.Suzuki.RankOneRoots
public import Theory.SpecificGroups.Suzuki.RootSquareFibers

/-!
# Every Suzuki involution is a square

Sylow conjugacy puts an involution in the root center, and the explicit
Tits-norm square formula covers every central root element. Transporting
the square root back preserves the original involution. This is the
native square obstruction used in the G.4.1 rank-one normalizer inspection.
-/

public noncomputable section
open Subgroup
namespace BenderSuzuki.MatrixGroups

/-- Every actual Suzuki involution has an actual square root in the same group. -/
theorem suzuki_involution_is_square (m:ℕ) (hm:0<m)
    (t:SuzukiMatrixGroup m) (ht:orderOf t=2) : ∃x:SuzukiMatrixGroup m,x^2=t := by
  obtain ⟨g,b,_,he,_,_⟩ := suzuki_involution_root_geometry m hm t ht
  have hz : MulAut.conj g t∈SuzukiRootSubgroup m :=
    (mem_suzukiRootSubgroup_iff m _).mpr ⟨0,b,he⟩
  let z:SuzukiRootSubgroup m := ⟨MulAut.conj g t,hz⟩
  have hzs : z^2=1 := by
    apply Subtype.ext
    change (MulAut.conj g t)^2=1
    rw [←map_pow]
    simpa only [ht,map_one] using congrArg (MulAut.conj g) (pow_orderOf_eq_one t)
  have hzc : z∈center (SuzukiRootSubgroup m) :=
    (suzukiRootSubgroup_square_iff_center m hm z).mp hzs
  obtain ⟨x,hx⟩ := suzukiRootSubgroup_square_surjective m hm ⟨z,hzc⟩
  refine ⟨(MulAut.conj g).symm x,?_⟩
  apply (MulAut.conj g).injective
  rw [map_pow,MulEquiv.apply_symm_apply]
  exact congrArg Subtype.val hx
end BenderSuzuki.MatrixGroups
