module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.BinaryFour
public import Theory.GroupTheory.GeneralizedFitting.CubicResidual
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The literal cubic residual actor in the local class

When C_H(V)=O₂(H), a cubic residual in H/C_H(V) is its generalized
Fitting subgroup. Its full inverse image is O²(H)O₂(H), and the kernel
centralizes V. Thus the moved module is exactly [V,O²(H)]. The final
source application constructs the actual binary natural marking.

Source: Aschbacher--Smith C.1.17 and the selected-factor application in
C.1.26, printed pp.126 and132.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Group H] [Finite H]

private theorem localStar_twoCore_eq_bot (e : B →* H)
    (hk : localKernel e = pCore 2 H) : pCore 2 (LocalStar e) = ⊥ := by
  let a := QuotientGroup.quotientMulEquivOfEq hk
  have he := pCore_map_iso 2 a
  rw [pCore_quotient_pCore_eq_bot] at he
  exact bot_unique (((Subgroup.map_eq_bot_iff _).mp he).trans_eq
    ((MonoidHom.ker_eq_bot_iff _).mpr a.injective))

/-- Computing the literal local actor from its original two-core kernel. -/
theorem actorLift_eq_residual_sup_kernel (e : B →* H)
    (hk : localKernel e = pCore 2 H)
    (hr : Nat.card (pResidual 2 (LocalStar e)) = 3) :
    actorLift e = pResidual 2 H ⊔ localKernel e := by
  have hc := localStar_twoCore_eq_bot e hk
  unfold actorLift
  rw [generalizedFitting_eq_residual_of_cubic hc hr,comap_pResidual_quotient]

/-- The kernel acts trivially, so the source moved module is exactly the
commutator with the original two-residual. -/
theorem moved_eq_residual_commutator (e : B →* H)
    (hk : localKernel e = pCore 2 H)
    (hr : Nat.card (pResidual 2 (LocalStar e)) = 3) :
    moved e = ⁅localV e,pResidual 2 H⁆ := by
  apply Eq.symm
  exact commutator_eq_of_centralizing_sup
    ((sup_comm _ _).trans (actorLift_eq_residual_sup_kernel e hk hr).symm)
    le_rfl le_normalizer_of_normal

/-- The actual residual computation supplies the C.1.17 actor and moved
module, with no extra action or coordinates premise. -/
theorem inLocalClass_of_cubic_residual (e : B →* H)
    [IsElementaryAbelian 2 (localV e)]
    (he : Function.Injective e)
    (hs : ∃ T : Sylow 2 H, e.range = (T : Subgroup H) ∧
      ChapterB.IsMinimalParabolicOver T ⊤)
    (hfit : generalizedFitting H = pCore 2 H)
    (hk : localKernel e = pCore 2 H)
    (hr : Nat.card (pResidual 2 (LocalStar e)) = 3)
    (hw : Nat.card (⁅localV e,pResidual 2 H⁆ : Subgroup H) = 4) : InLocalClass e := by
  apply inLocalClass_of_cubic_four e he hs hfit
  · rw [generalizedFitting_eq_residual_of_cubic (localStar_twoCore_eq_bot e hk) hr]
    exact hr
  · rw [moved_eq_residual_commutator e hk hr]
    exact hw
end CFSG.Quasithin.ChapterC.GlaubermanNiles
