module

public import GorensteinWalter.SL2UniversalCover
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv

/-!
# The exceptional universal double cover of PSL₂(4)

Transport the proved universal cover SL₂(5) → PSL₂(5) through the actual
isomorphisms PSL₂(5) ≃ A₅ ≃ PSL₂(F), where F has four elements. The result
is a finite quasisimple universal cover whose kernel is C₂. The ordinary
SL₂(F) projection is not used as the exceptional covering group.

This supplies the order-four endpoint in the exhaustive multiplier list of
Aschbacher–Smith I.1.3, printed p.407. The model comparisons use the existing
icosahedral construction and faithful five-point projective action.
-/

public section
noncomputable section

open Theory.GroupTheory
open scoped MatrixGroups
namespace GorensteinWalter.PSL2Cover
universe u w
variable (F : Type u) [Field F] [Finite F] [Fact (3 < Nat.card F)]

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (3 < Nat.card (ZMod 5)) := ⟨by norm_num⟩

noncomputable def fourComparison (hF : Nat.card F = 4) : PSL(2, ZMod 5) ≃* PSL(2, F) :=
  Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five.some.trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some.symm

/-- An explicit double cover at q = 4, with covering group SL₂(5). -/
@[expose] noncomputable def fourCover (hF : Nat.card F = 4) : Covering SL(2, ZMod 5) PSL(2, F) :=
  (Covering.ofMulEquiv (fourComparison F hF)).comp (cover (ZMod 5))

theorem fourCover_isUniversal (hF : Nat.card F = 4) :
    Covering.IsUniversal.{u, 0, w} (fourCover F hF) :=
  (isUniversal_of_card_prime (ZMod 5) (by norm_num)).comp_ofMulEquiv (fourComparison F hF)

noncomputable def fourKernelEquivTwo (hF : Nat.card F = 4) :
    (fourCover F hF).toMonoidHom.ker ≃* Multiplicative (ZMod 2) := by
  have he : (fourCover F hF).toMonoidHom.ker = (cover (ZMod 5)).toMonoidHom.ker :=
    MonoidHom.ker_comp_of_injective _ _ (fourComparison F hF).injective
  exact (MulEquiv.subgroupCongr he).trans (kernelEquivTwo (ZMod 5) (by norm_num))

end GorensteinWalter.PSL2Cover
