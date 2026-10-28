module
public import Theory.GroupTheory.Recognition.Brauer.FixedFactors
public import Theory.GroupTheory.OddOrderSquare
public import Theory.GroupTheory.Recognition.Brauer.InvertedSubgroups
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.Complement

/-!
# The distinguished incidence in Brauer's involution geometry

Under Brauer's first three postulates, the base point containing `j` is
incident with the conjugate base line containing `j1`: the two actual
involution subsets are disjoint. This is the algebraic heart of Brauer,
*On finite Desarguesian planes I*, (2D), article p. 120, equation (2.6).
The general commuting-incidence theorem transports this result by conjugation.

Suppose a common element gives `j*a*b = j1*z`, where `a` and `b` are the
fixed factors in `M`, and `z` belongs to the conjugate of `Mstar` by `y`.
Conjugation by `j1` fixes `a` and inverts `b` and `z`. Comparing the original
and conjugated equations gives `z² = b²`. Both elements have odd order,
so the cross-subgroup square-root theorem identifies them. The remaining
equation puts `j*j1` in `M ∩ C(j)`, contradicting the distinct involutions.
-/

namespace Theory.GroupTheory
private theorem comparison {G : Type*} [Group G] (j1 t a b z : G)
    (ht : j1 * t * j1⁻¹ = t) (ha : j1 * a * j1⁻¹ = a)
    (hb : j1 * b * j1⁻¹ = b⁻¹) (hz : j1 * z * j1⁻¹ = z⁻¹)
    (heq : t = z * b⁻¹ * a⁻¹) : z ^ 2 = b ^ 2 := by
  let φ : MulAut G := MulAut.conj j1
  have ht' : φ t = t := ht
  have ha' : φ a = a := ha
  have hb' : φ b = b⁻¹ := hb
  have hz' : φ z = z⁻¹ := hz
  have heq' := congrArg φ heq
  simp only [map_mul, map_inv, ht', ha', hb', hz', inv_inv] at heq'
  have heq'' : z * b⁻¹ = z⁻¹ * b := mul_right_cancel (heq.symm.trans heq')
  calc
    z ^ 2 = z * (z * b⁻¹) * b := by simp [pow_two, mul_assoc]
    _ = z * (z⁻¹ * b) * b := by rw [heq'']
    _ = b ^ 2 := by simp [pow_two]


open scoped Pointwise
namespace BrauerPlaneSeed
/-- Brauer I (2D) for the distinguished pair `j,j1`. -/
public theorem disjoint_basePoint_conj_baseLine
    {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G) :
    Disjoint S.basePoint ((ConjAct.toConjAct S.y⁻¹) • S.baseLine) := by
  have hcomp := S.fixed_factors.1
  obtain ⟨⟨hMo, _, hMi⟩, ⟨hSo, _, hSi⟩⟩ := S.inverted_subgroups
  have hjj : S.j * S.j = 1 := by simpa only [S.j_order, pow_two] using pow_orderOf_eq_one S.j
  have hjInv : S.j⁻¹ = S.j := inv_eq_iff_mul_eq_one.mpr hjj
  have hj1j1 : S.j1 * S.j1 = 1 := by simpa only [S.j1_order, pow_two] using pow_orderOf_eq_one S.j1
  have hj1Inv : S.j1⁻¹ = S.j1 := inv_eq_iff_mul_eq_one.mpr hj1j1
  have hjcomm := S.j_commute_j1.eq
  apply Set.disjoint_left.mpr
  intro x hx hl
  obtain ⟨m, hm, hmx⟩ := Set.mem_smul_set.mp hx
  obtain ⟨w, hw, hwx⟩ := Set.mem_smul_set.mp hl
  obtain ⟨n, hn, hnw⟩ := Set.mem_smul_set.mp hw
  change S.j * m = x at hmx
  change S.j * n = w at hnw
  change S.y⁻¹ * w * (S.y⁻¹)⁻¹ = x at hwx
  obtain ⟨⟨a', b'⟩, hab', _⟩ := hcomp.existsUnique ⟨m, hm⟩
  let a : G := (a' : S.M)
  let b : G := (b' : S.M)
  let z : G := S.y⁻¹ * n * S.y
  have ha : a ∈ S.M1 := a'.property
  have hb : b ∈ S.M2 := b'.property
  have hab : a * b = m := congrArg Subtype.val hab'
  have hz : S.j1 * z * S.j1⁻¹ = z⁻¹ := by
    rw [← S.y_conj_j]
    change (S.y⁻¹ * S.j * S.y) * (S.y⁻¹ * n * S.y) *
      (S.y⁻¹ * S.j * S.y)⁻¹ = (S.y⁻¹ * n * S.y)⁻¹
    calc
      _ = S.y⁻¹ * (S.j * n * S.j⁻¹) * S.y := by group
      _ = S.y⁻¹ * n⁻¹ * S.y := by rw [show S.j * n * S.j⁻¹ = n⁻¹ from by simpa only [hjInv] using hSi ⟨n, hn⟩]
      _ = _ := by group
  have haFix : S.j1 * a * S.j1⁻¹ = a := by
    exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp ha.2).symm
  have hbInv : S.j1 * b * S.j1⁻¹ = b⁻¹ := by
    have hbFix : S.j2 * b * S.j2⁻¹ = b :=
      mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp hb.2).symm
    have hj1 : S.j1 = S.j * S.j2 := by
      change S.j1 = S.j * (S.j * S.j1)
      rw [← mul_assoc, hjj, one_mul]
    calc
      _ = S.j * (S.j2 * b * S.j2⁻¹) * S.j⁻¹ := by rw [hj1]; group
      _ = S.j * b * S.j⁻¹ := by rw [hbFix]
      _ = b⁻¹ := by simpa only [hjInv] using hMi ⟨b, hb.1⟩
  have htFix : S.j1 * S.j2 * S.j1⁻¹ = S.j2 := by
    change S.j1 * (S.j * S.j1) * S.j1⁻¹ = S.j * S.j1
    simp only [mul_assoc, mul_inv_cancel, mul_one]
    exact hjcomm.symm
  have hprod : S.j * (a * b) = S.j1 * z := by
    rw [hab, hmx, ← hwx, ← hnw, inv_inv, ← S.y_conj_j]
    dsimp only [z]
    group
  have htprod : S.j2 * a * b = z := by
    have heq := congrArg (S.j1 * ·) hprod
    have hl : S.j1 * (S.j * (a * b)) = S.j2 * a * b := by
      change S.j1 * (S.j * (a * b)) = (S.j * S.j1) * a * b
      rw [← mul_assoc S.j1 S.j, ← hjcomm]
      group
    rw [hl, ← mul_assoc S.j1 S.j1, hj1j1, one_mul] at heq
    exact heq
  have heq : S.j2 = z * b⁻¹ * a⁻¹ := by
    rw [← htprod]
    group
  have hsq := comparison S.j1 S.j2 a b z htFix haFix hbInv hz heq
  have hnodd : Odd (orderOf n) := hSo.of_dvd_nat (S.Mstar.orderOf_dvd_natCard hn)
  have hzodd : Odd (orderOf z) := by
    have heq := (MulAut.conj S.y⁻¹).orderOf_eq n
    change orderOf (S.y⁻¹ * n * (S.y⁻¹)⁻¹) = orderOf n at heq
    have hzorder : orderOf z = orderOf n := by simpa only [z, inv_inv] using heq
    rwa [hzorder]
  have hbodd : Odd (orderOf b) := hMo.of_dvd_nat (S.M.orderOf_dvd_natCard hb.1)
  have hzb : z = b := eq_of_sq_eq_sq_of_odd_orderOf hzodd hbodd hsq
  have hta : S.j2 = a⁻¹ := by simpa only [hzb, mul_inv_cancel, one_mul] using heq
  have htM : S.j2 ∈ S.M := hta ▸ S.M.inv_mem ha.1
  have htC : S.j2 ∈ Subgroup.centralizer ({S.j} : Set G) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (Commute.refl S.j).mul_left S.j_commute_j1.symm |>.eq
  have htOne : S.j2 = 1 := by
    have ht : S.j2 ∈ S.M ⊓ Subgroup.centralizer ({S.j} : Set G) := ⟨htM, htC⟩
    simpa only [S.disjoint_M_centralizer.eq_bot, Subgroup.mem_bot] using ht
  apply S.j_ne_j1
  have ht := inv_eq_iff_mul_eq_one.mpr htOne
  simpa only [hjInv] using ht
end BrauerPlaneSeed
end Theory.GroupTheory
