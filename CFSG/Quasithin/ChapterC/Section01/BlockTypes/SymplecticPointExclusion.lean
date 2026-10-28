module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.SpecificGroups.SymplecticFour.NaturalScalarCubic
public import Theory.GroupTheory.PCoreImage

/-!
# Excluding the point residual on a moved symplectic submodule

In the natural symplectic representation, the point radical fixes exactly
its distinguished point, and the point residual fixes that point elementwise.
Thus a nonzero commutator-generated subgroup of a block layer cannot be fixed
by the original local two-core if its image is the point residual. The proof
passes through the actual central quotient and lifts the local core through
a map with two-group kernel; it assumes no splitting of the block layer.

Source: Aschbacher–Smith C.4.1(2), printed pp.151–153, and the natural
module description in F.1.12, pp.262–264.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC
variable {X : Type*} [Group X] [Finite X] {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A moved subgroup fixed by the local core excludes the point marking. -/
theorem BlockModuleModel.symplectic_not_point_of_moved_core_fixed
    (hF : Nat.card F = 4)
    {rho : Sp F →* MulAut (Multiplicative (Vector F))}
    (m : BlockModuleModel X rho)
    (hrho : ∀ g v, (rho g v).toAdd = g.val.mulVec v.toAdd)
    (A W : Subgroup X) (hWU : W ≤ blockU X) (hne : W ≠ ⊥)
    (hcomm : ⁅W,A⁆ = W)
    (hfix : W ≤ centralizer (A.pCoreIn 2 : Set X)) :
    A.map (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) ≠
      pointLocal := by
  intro hA
  let p := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  let q := m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (blockFixed X))
  have hp : p.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,QuotientGroup.ker_mk']
  have hk : q.ker = blockFixed X := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.moduleIso.injective,QuotientGroup.ker_mk']
  have hcore : (A.pCoreIn 2).map p = pointRadicalAmbient := by
    rw [map_pCoreIn_of_ker_isPGroup p (hp ▸ pCore_isPGroup), hA]
    change (pCore 2 (pointLocal (F := F))).map pointLocal.subtype = _
    rw [pointLocal_core_eq (n := 2) hF (by decide)]
  have hq (a : X) (u : blockU X) :
      (q (blockConjugate X a u)).toAdd = (p a).val.mulVec (q u).toAdd := by
    change (m.moduleIso (QuotientGroup.mk' _ (blockConjugate X a u))).toAdd = _
    rw [m.intertwining,hrho]
    rfl
  have hpoint (w : blockU X) (hw : w.val ∈ W) : (q w).toAdd ∈ point F := by
    apply NaturalScalarCubic.point_radical_fixed
    intro r hr
    rw [←hcore] at hr
    obtain ⟨a,ha,rfl⟩ := hr
    rw [smul_eq_mulVec,←hq]
    congr 2
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hfix hw a ha)
  have hfixed (a : X) (ha : a ∈ A) (w : blockU X) (hw : w.val ∈ W) :
      q (blockConjugate X a w) = q w := by
    apply Multiplicative.toAdd.injective
    rw [hq,←smul_eq_mulVec]
    have hpA : p a ∈ pointLocal (F := F) := hA ▸ mem_map_of_mem p ha
    obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp (hpoint w hw)
    rw [←ht]
    change toLinear (p a) (t • e 0) = t • e 0
    rw [map_smul]
    exact congrArg (t • ·) ((mem_pointLocal_iff_fixed (p a)).mp hpA)
  have hc : ⁅A,W⁆ ≤ center X := by
    apply commutator_le.mpr
    intro a ha w hw
    let u : blockU X := ⟨w,hWU hw⟩
    have hz : blockConjugate X a u * u⁻¹ ∈ q.ker := by
      rw [MonoidHom.mem_ker,map_mul,map_inv,hfixed a ha u hw,mul_inv_cancel]
    rw [hk] at hz
    exact hz
  rw [commutator_comm,hcomm] at hc
  have hz : ⁅W,A⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (by
    intro w hw a _
    exact mem_center_iff.mp (hc hw) a)
  exact hne (hcomm.symm.trans hz)
end CFSG.Quasithin.ChapterC
