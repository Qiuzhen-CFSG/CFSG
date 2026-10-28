module
public import Theory.SpecificGroups.Suzuki.SmallSylowIntersections
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.GroupTheory.PGroup.OmegaAmbient

/-!
# Odd residual generation by two small Suzuki omega subgroups

The binary Suzuki group is the faithful group C₅:C₄. Distinct involutions
have a product generating its subgroup of order five; the residual lies in
that subgroup because the complementary quotient is a two-group. The TI
property supplies distinct involutions from distinct Sylow two-subgroups.

The consumer is the small Suzuki row of DGS85 (8.7), printed pp.139--140:
fixing both full omega subgroups forces a middle-center element to be fixed
by the odd residual, hence trivial when the local group is centerless.
-/

public noncomputable section
open Subgroup
namespace FiveFour
private theorem involution_pair_generates_c (x y : Group)
    (hx : x^2=1) (hx1 : x≠1) (hy : y^2=1) (hy1 : y≠1) (hxy : x≠y) :
    c ∈ zpowers (x*y) := by
  have cert : ∀ x y : Group, x^2=1 → x≠1 → y^2=1 → y≠1 → x≠y →
      ∃ n : Fin 5, (x*y)^n.val=c := by decide +kernel
  obtain ⟨n,hn⟩ := cert x y hx hx1 hy hy1 hxy
  rw [←hn]
  exact pow_mem (mem_zpowers _) _

private theorem twoResidual_le_c : pResidual 2 Group ≤ zpowers c := by
  have hres : pResidual 2 Group ≤ (SemidirectProduct.rightHom : Group →* Cyclic 4).ker :=
    pResidual_le_ker_of_isPGroup 2 _ (IsPGroup.of_card (n:=2) (by
      change Nat.card (ZMod 4)=2^2
      simp))
  intro g hg
  have he : g.right=1 := hres hg
  rw [←normal_form g,he]
  simp only [toAdd_one,ZMod.val_zero,pow_zero,mul_one]
  exact pow_mem (mem_zpowers _) _

/-- Distinct nontrivial involutions generate the odd residual of the faithful
five-by-four group. -/
theorem twoResidual_le_involution_pair (x y : Group)
    (hx : x^2=1) (hx1 : x≠1) (hy : y^2=1) (hy1 : y≠1) (hxy : x≠y) :
    pResidual 2 Group ≤ zpowers x ⊔ zpowers y := by
  apply twoResidual_le_c.trans
  apply zpowers_le.mpr
  exact (zpowers_le.mpr ((zpowers x ⊔ zpowers y).mul_mem
    ((show zpowers x ≤ zpowers x ⊔ zpowers y from le_sup_left) (mem_zpowers x))
    ((show zpowers y ≤ zpowers x ⊔ zpowers y from le_sup_right) (mem_zpowers y))))
      (involution_pair_generates_c x y hx hx1 hy hy1 hxy)
end FiveFour

namespace BenderSuzuki.MatrixGroups
/-- The omega subgroups of distinct Sz(2) Sylows generate a subgroup
containing the full odd residual. -/
theorem suzukiZero_twoResidual_le_distinct_omega_sup
    (P Q : Sylow 2 (SuzukiMatrixGroup 0)) (hPQ : P≠Q) :
    pResidual 2 (SuzukiMatrixGroup 0) ≤
      omegaOneAmbient (P : Subgroup (SuzukiMatrixGroup 0)) ⊔
      omegaOneAmbient (Q : Subgroup (SuzukiMatrixGroup 0)) := by
  have hc (R : Sylow 2 (SuzukiMatrixGroup 0)) : Nat.card R=4 := by
    rw [R.card_eq_multiplicity,
      (Nat.card_congr FiveFour.suzukiZeroEquiv.toEquiv).symm.trans FiveFour.card]
    decide +kernel
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 (by rw [hc P]; decide)
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 (by rw [hc Q]; decide)
  have hx2 : (x : SuzukiMatrixGroup 0)^2=1 := by
    have hh:=pow_orderOf_eq_one x
    rw [hx] at hh
    exact congrArg Subtype.val hh
  have hy2 : (y : SuzukiMatrixGroup 0)^2=1 := by
    have hh:=pow_orderOf_eq_one y
    rw [hy] at hh
    exact congrArg Subtype.val hh
  have hx1 : (x : SuzukiMatrixGroup 0)≠1 := by
    intro he
    have hh : x=1 := Subtype.ext he
    simp only [hh,orderOf_one] at hx
    omega
  have hy1 : (y : SuzukiMatrixGroup 0)≠1 := by
    intro he
    have hh : y=1 := Subtype.ext he
    simp only [hh,orderOf_one] at hy
    omega
  have hxy : (x : SuzukiMatrixGroup 0)≠y := by
    intro he
    apply hPQ
    apply smallSuzuki_sylow_eq_of_inf_ne_bot
    intro hb
    exact hx1 (mem_bot.mp (hb ▸ show (x : SuzukiMatrixGroup 0)∈
      (P : Subgroup (SuzukiMatrixGroup 0)) ⊓ Q from ⟨x.property,he ▸ y.property⟩))
  let e := FiveFour.suzukiZeroEquiv
  have hpair := FiveFour.twoResidual_le_involution_pair (e.symm x) (e.symm y)
    (by rw [←map_pow,hx2,map_one]) (e.symm.map_ne_one_iff.mpr hx1)
    (by rw [←map_pow,hy2,map_one]) (e.symm.map_ne_one_iff.mpr hy1)
    (fun he => hxy (e.symm.injective he))
  have hm := Subgroup.map_mono (f := e.toMonoidHom) hpair
  rw [Subgroup.map_pResidual,Subgroup.map_sup,
    MonoidHom.map_zpowers,MonoidHom.map_zpowers] at hm
  simp only [MulEquiv.coe_toMonoidHom,e.apply_symm_apply] at hm
  apply hm.trans
  apply sup_le_sup
  · exact zpowers_le.mpr ((omegaOneAmbient_le_iff _ _).mp le_rfl _ x.property hx2)
  · exact zpowers_le.mpr ((omegaOneAmbient_le_iff _ _).mp le_rfl _ y.property hy2)
end BenderSuzuki.MatrixGroups
