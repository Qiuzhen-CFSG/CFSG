module

public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The image of a normal subgroup modulo the ambient p-core

For a normal subgroup `N` of `H`, its p-core is the restriction of `O_p(H)`.
Indeed its characteristic p-core is normal in `H`, and the reverse inclusion
is a normal p-subgroup of `N`. The first isomorphism theorem therefore
identifies `N/O_p(N)` with the image of `N` in `H/O_p(H)`.

This is the star-quotient identification used in Aschbacher–Smith,
Lemma 15.3.7, printed p.1122. No hypothesis on the action kernel is needed.
-/

namespace Subgroup
variable {H : Type*} [Group H] (p : ℕ) (N : Subgroup H) [N.Normal]

/-- Restriction of the ambient p-core to a normal subgroup. -/
public theorem pCore_eq_comap_of_normal :
    pCore p N = (pCore p H).comap N.subtype := by
  apply le_antisymm
  · rw [← map_le_iff_le_comap]
    exact le_sSup ⟨inferInstance, pCore_isPGroup.map N.subtype⟩
  · exact le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩

/-- The kernel of the map to the ambient core quotient is the intrinsic core. -/
public theorem ker_coreQuotient_restrict :
    ((QuotientGroup.mk' (pCore p H)).comp N.subtype).ker = pCore p N := by
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', pCore_eq_comap_of_normal]

/-- A normal subgroup's intrinsic core quotient is its actual ambient image. -/
public noncomputable def coreQuotientEquivImage :
    N ⧸ pCore p N ≃* N.map (QuotientGroup.mk' (pCore p H)) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_coreQuotient_restrict p N).symm).trans
    ((QuotientGroup.quotientKerEquivRange
      ((QuotientGroup.mk' (pCore p H)).comp N.subtype)).trans
      (MulEquiv.subgroupCongr (by
        rw [MonoidHom.range_comp, range_subtype])))

/-- The isomorphism is induced by the ambient quotient map. -/
@[simp] public theorem coreQuotientEquivImage_apply_mk (n : N) :
    ((coreQuotientEquivImage p N) (QuotientGroup.mk' (pCore p N) n) : H ⧸ pCore p H) =
      QuotientGroup.mk' (pCore p H) (n : H) := by
  rfl

end Subgroup
