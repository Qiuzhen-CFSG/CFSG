module

public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Solvable

/-!
# The original residual inside the component central quotient

Restrict the actual component quotient to the fixed residual. Its kernel is
central in that residual, hence solvable. The image of the residual two-core
is nontrivial: otherwise its nontrivial commutator module would centralize
the residual. That image is a two-group normalized by the residual image.

Thus the concrete two-local exclusions apply to this representation, rather
than to an unrelated simple section of the component. Central covers and
the original module are retained throughout.
Source: Aschbacher--Smith 4.4.11--12, printed pp.621--622.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory

variable {G Q : Type*} [Group G] [Group Q]

/-- The literal representation of a residual in a marked component quotient. -/
@[expose] def residualQuotientMap {F K : Subgroup G} (hFK : F ≤ K)
    (e : (K ⧸ center K) ≃* Q) : F →* Q :=
  e.toMonoidHom.comp ((QuotientGroup.mk' (center K)).comp (inclusion hFK))

/-- Restricting a central quotient to the original residual has solvable kernel. -/
theorem residualQuotientMap_kernel_solvable {F K : Subgroup G} (hFK : F ≤ K)
    (e : (K ⧸ center K) ≃* Q) : Group.IsSolvable (residualQuotientMap hFK e).ker := by
  let r := residualQuotientMap hFK e
  have hc : r.ker ≤ center F := by
    intro x hx
    have hh : e (QuotientGroup.mk' (center K) (inclusion hFK x)) = 1 := hx
    have hx' : inclusion hFK x ∈ center K := (QuotientGroup.eq_one_iff _).mp
      (e.injective (hh.trans e.map_one.symm))
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact congrArg K.subtype (mem_center_iff.mp hx' (inclusion hFK y))
  let : CommGroup (center F) := IsMulCommutative.instCommGroup
  exact Group.isSolvable_of_isSolvable_injective (inclusion_injective hc)

/-- The actual image of O₂(F) is a nonidentity two-group normalized by F's image. -/
theorem residualQuotientMap_two_local
    {F K W : Subgroup G} (hFK : F ≤ K) (hWF : W ≤ F.pCoreIn 2)
    (hne : W ≠ ⊥) (hcomm : W = ⁅W,F⁆) (e : (K ⧸ center K) ≃* Q) :
    let r := residualQuotientMap hFK e
    IsPGroup 2 ((pCore 2 F).map r) ∧ (pCore 2 F).map r ≠ ⊥ ∧
      r.range ≤ normalizer ((pCore 2 F).map r : Set Q) := by
  let r := residualQuotientMap hFK e
  refine ⟨pCore_isPGroup.map r,?_,?_⟩
  · intro hb
    have hk : pCore 2 F ≤ r.ker := (Subgroup.map_eq_bot_iff _).mp hb
    have hc : F.pCoreIn 2 ≤ centralizer (F : Set G) := by
      rintro _ ⟨x,hx,rfl⟩ y hy
      have hh : e (QuotientGroup.mk' (center K) (inclusion hFK x)) = 1 := hk hx
      have hz : inclusion hFK x ∈ center K := (QuotientGroup.eq_one_iff _).mp
        (e.injective (hh.trans e.map_one.symm))
      exact congrArg K.subtype (mem_center_iff.mp hz (inclusion hFK ⟨y,hy⟩))
    exact hne (hcomm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr (hWF.trans hc)))
  · simpa only [normalizer_eq_top, MonoidHom.range_eq_map] using
      (pCore 2 F).le_normalizer_map r

end Theory.GroupTheory
