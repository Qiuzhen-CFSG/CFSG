module
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Tactic

/-!
# Involution fibers through odd kernels

Two involutions with the same image have product in the odd kernel. If that
product has order 2k+1, its kth power conjugates the first involution to the
second. Thus each nonempty involution fiber is one kernel orbit, with
stabilizer the centralizer in the kernel. Conjugation also identifies fibers
over conjugate quotient elements.

The dihedral calculation follows the proof in
`Theory.GroupTheory.InvolutionPairCentralInvolution`, retaining membership of
the conjugator in the kernel. This supplies the lift multiplicity used in
Alperin–Brauer–Gorenstein, III.7 equation (8), article pp.103–104.
-/

namespace Subgroup

/-- Involutions with the same image through an odd kernel are conjugate by
an element of that kernel. -/
public theorem involutions_same_image_conj_ker
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hker : Nat.Coprime 2 (Nat.card f.ker))
    {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : f a = f b) :
    ∃ g : f.ker, (g : G) * a * (g : G)⁻¹ = b := by
  have haa : a * a = 1 := by simpa only [pow_two, ha] using pow_orderOf_eq_one a
  have hbb : b * b = 1 := by simpa only [pow_two, hb] using pow_orderOf_eq_one b
  have hai : a⁻¹ = a := inv_eq_iff_mul_eq_one.mpr haa
  have hbi : b⁻¹ = b := inv_eq_iff_mul_eq_one.mpr hbb
  have hr : a * b ∈ f.ker := by
    change f (a * b) = 1
    rw [map_mul, hab, ← map_mul, hbb, map_one]
  let r : f.ker := ⟨a * b, hr⟩
  have hodd : Odd (orderOf r) := Nat.coprime_two_left.mp
    (hker.of_dvd_right (_root_.orderOf_dvd_natCard r))
  obtain ⟨k, hk⟩ := hodd
  have hnum : k * 2 + 1 = orderOf (a * b) := by
    have hrorder : orderOf (a * b) = orderOf r := Subgroup.orderOf_coe r
    omega
  have haRot : MulAut.conj a (a * b) = (a * b)⁻¹ := by
    change a * (a * b) * a⁻¹ = (a * b)⁻¹
    rw [mul_inv_rev, hai, hbi, ← mul_assoc a a b, haa, one_mul]
  let g := (a * b) ^ k
  have haPow : MulAut.conj a g = g⁻¹ := by
    change MulAut.conj a ((a * b) ^ k) = ((a * b) ^ k)⁻¹
    rw [map_pow, haRot, inv_pow]
  have hsquare : g ^ 2 = (a * b)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    change ((a * b) ^ k) ^ 2 * (a * b) = 1
    rw [← pow_mul, ← pow_succ, hnum, pow_orderOf_eq_one]
  have hmove : a * g⁻¹ = g * a := by
    have hh : MulAut.conj a g⁻¹ = g := by rw [map_inv, haPow, inv_inv]
    exact mul_inv_eq_iff_eq_mul.mp hh
  refine ⟨⟨g, f.ker.pow_mem hr k⟩, ?_⟩
  change g * a * g⁻¹ = b
  calc
    g * a * g⁻¹ = g * (a * g⁻¹) := by group
    _ = g * (g * a) := by rw [hmove]
    _ = g ^ 2 * a := by simp only [pow_two, mul_assoc]
    _ = (a * b)⁻¹ * a := by rw [hsquare]
    _ = b := by rw [mul_inv_rev, hai, hbi, mul_assoc, haa, mul_one]

/-- A nonempty involution fiber has size the centralizer index in the kernel. -/
public theorem card_involution_fiber_eq_centralizer_index
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hker : Nat.Coprime 2 (Nat.card f.ker))
    (a : G) (ha : orderOf a = 2) :
    Nat.card {u : {u : G // orderOf u = 2} // f u = f a} =
      ((centralizer ({a} : Set G)).subgroupOf f.ker).index := by
  let : MulAction f.ker G := MulAction.compHom G
    (ConjAct.toConjAct.toMonoidHom.comp f.ker.subtype)
  have hstab : MulAction.stabilizer f.ker a =
      (centralizer ({a} : Set G)).subgroupOf f.ker := by
    ext g
    change (g : G) * a * (g : G)⁻¹ = a ↔ _
    rw [mul_inv_eq_iff_eq_mul]
    exact mem_centralizer_singleton_iff.symm
  have horbit (b : G) : b ∈ MulAction.orbit f.ker a ↔ orderOf b = 2 ∧ f b = f a := by
    constructor
    · rintro ⟨g, rfl⟩
      constructor
      · exact ((MulAut.conj (g : G)).orderOf_eq a).trans ha
      · change f ((g : G) * a * (g : G)⁻¹) = f a
        rw [map_mul, map_mul, map_inv, g.property]
        simp
    · rintro ⟨hb, hba⟩
      obtain ⟨g, hg⟩ := involutions_same_image_conj_ker f hker ha hb hba.symm
      exact ⟨g, hg⟩
  rw [← hstab, MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
  apply Nat.card_congr
  exact (Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
    (Equiv.subtypeEquiv (Equiv.refl G) (fun b => (horbit b).symm))

/-- A surjective homomorphism has equally many involution lifts over conjugate
codomain elements. -/
public theorem card_involution_fiber_eq_of_isConj
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    {y z : H} (hyz : IsConj y z) :
    Nat.card {u : {u : G // orderOf u = 2} // f u = y} =
      Nat.card {u : {u : G // orderOf u = 2} // f u = z} := by
  obtain ⟨h, hh⟩ := isConj_iff.mp hyz
  obtain ⟨g, rfl⟩ := hf h
  let e := MulAut.conj g
  have hm (a : G) : f (e a) = MulAut.conj (f g) (f a) := by
    change f (g * a * g⁻¹) = f g * f a * (f g)⁻¹
    simp only [map_mul, map_inv]
  apply Nat.card_congr
  refine (Equiv.subtypeSubtypeEquivSubtypeInter (fun u : G => orderOf u = 2)
    (fun u => f u = y)).trans (Equiv.trans ?_
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun u : G => orderOf u = 2)
        (fun u => f u = z)).symm)
  exact Equiv.subtypeEquiv e.toEquiv (fun a => by
    change (orderOf a = 2 ∧ f a = y) ↔ (orderOf (e a) = 2 ∧ f (e a) = z)
    rw [e.orderOf_eq, hm, ← hh]
    exact and_congr_right (fun _ => (MulAut.conj (f g)).injective.eq_iff.symm))

end Subgroup
