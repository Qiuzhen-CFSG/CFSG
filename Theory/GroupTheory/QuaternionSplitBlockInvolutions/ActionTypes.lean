module

public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Geometry.Basic
public import Theory.GroupTheory.QuaternionOuterInvolutionReduction

/-!
# The square-quotient involution types for a quaternion central product

The a₂ and c₂ conditions are conditions on the literal quotient by the center:
its fixed plane has order four, and the square map is respectively trivial or
nontrivial on that plane. Rank-nullity identifies the fixed and displacement
planes. The exported equivalences identify the square test with Suzuki's
perpendicularity test for the actual polar form, not an abstract class label.

An involution interchanging the embedded quaternion factors is of type a₂.
A fixed quotient vector lifts to a fixed group element, so the fixed plane is
the image of the elementary diagonal of order eight.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Definition
E.2.6 (printed p.218) and proof of Lemma 14.4.4 (printed p.1007).
-/

open scoped Pointwise IsMulCommutative commutatorElement
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

@[expose] public def fixedSquareQuotient (_d : QuaternionCentralProductData Q) (α : MulAut Q) : Subgroup (Q ⧸ center Q) :=
  (quotientAut (center Q) α).toMonoidHom.eqLocus (MonoidHom.id _)

@[expose] public def IsA2Action (α : MulAut Q) : Prop :=
  (quotientAut (center Q) α) ^ 2 = 1 ∧
  Nat.card (d.fixedSquareQuotient α) = 4 ∧
  ∀ v ∈ d.fixedSquareQuotient α, d.square v = 1

@[expose] public def IsC2Action (α : MulAut Q) : Prop :=
  (quotientAut (center Q) α) ^ 2 = 1 ∧
  Nat.card (d.fixedSquareQuotient α) = 4 ∧
  ∃ v ∈ d.fixedSquareQuotient α, d.square v ≠ 1

/-- The actual displacement homomorphism of the central quotient. -/
@[expose] public def quotientDisplacement (α : MulAut Q) : (Q ⧸ center Q) →* (Q ⧸ center Q) := by
  let := d.quotient_elementary
  exact {
    toFun := fun v => v⁻¹ * quotientAut (center Q) α v
    map_one' := by simp
    map_mul' := fun v w => by simp only [mul_inv_rev, map_mul]; ac_rfl }

/-- In dimension four, fixed order four identifies the fixed and moved planes. -/
public theorem displacement_range_eq_fixed (α : MulAut Q)
    (hα : (quotientAut (center Q) α) ^ 2 = 1)
    (hc : Nat.card (d.fixedSquareQuotient α) = 4) :
    (d.quotientDisplacement α).range = d.fixedSquareQuotient α := by
  let := d.quotient_elementary
  let β := quotientAut (center Q) α
  have hker : (d.quotientDisplacement α).ker = d.fixedSquareQuotient α := by
    ext v
    change v⁻¹ * β v = 1 ↔ β v = v
    rw [inv_mul_eq_one, eq_comm]
  have hi (v : Q ⧸ center Q) : v⁻¹ = v := by
    apply inv_eq_iff_mul_eq_one.mpr
    exact (pow_two v).symm.trans
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (Q ⧸ center Q)) v)
  have hle : (d.quotientDisplacement α).range ≤ d.fixedSquareQuotient α := by
    rintro _ ⟨v, rfl⟩
    change β (v⁻¹ * β v) = v⁻¹ * β v
    have hβ : β (β v) = v := by
      simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using DFunLike.congr_fun hα v
    rw [map_mul, map_inv, hβ, hi, hi, mul_comm]
  have hcount := (d.quotientDisplacement α).ker.card_mul_index
  rw [index_ker, hker, hc, d.quotient_card] at hcount
  apply eq_of_le_of_card_ge hle
  omega

/-- The square criterion on displacement is exactly Suzuki's perpendicularity
criterion for the actual polar form (Definition E.2.6). -/
public theorem square_displacement_eq_one_iff (α : MulAut Q) (v : Q ⧸ center Q) :
    d.square (d.quotientDisplacement α v) = 1 ↔
    d.quadraticForm.polarBilin (Additive.ofMul v)
      (Additive.ofMul (quotientAut (center Q) α v)) = 0 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center Q) v
  let π := QuotientGroup.mk' (center Q)
  have hδ : d.quotientDisplacement α (π x) = π (x⁻¹ * α x) := by
    change (π x)⁻¹ * quotientAut (center Q) α (π x) = _
    rw [quotientAut_apply_mk, map_mul, map_inv]
  have hs : (α x) ^ 2 = x ^ 2 := by
    rw [← map_pow]
    exact d.fixes_center α ⟨x ^ 2, d.square_mem_center x⟩
  have hsq : (x⁻¹ * α x) ^ 2 = ⁅x, α x⁆ := by
    calc
      (x⁻¹ * α x) ^ 2 = (x ^ 2)⁻¹ * ⁅x, α x⁆ * (α x) ^ 2 := by
        simp only [pow_two, commutatorElement_def]
        group
      _ = (x ^ 2)⁻¹ * ⁅x, α x⁆ * x ^ 2 := by rw [hs]
      _ = ⁅x, α x⁆ := by
        rw [← mem_center_iff.mp ((center Q).inv_mem (d.square_mem_center x))
          ⁅x, α x⁆, inv_mul_cancel_right]
  have hv : d.square (d.quotientDisplacement α (π x)) =
      ⟨⁅x, α x⁆, d.commutator_mem_center x (α x)⟩ := by
    apply Subtype.ext
    rw [hδ, d.square_mk]
    exact hsq
  rw [quotientAut_apply_mk, d.polarBilin_mk, d.centerCoordinate_eq_zero_iff]
  exact iff_of_eq (congrArg (fun z : center Q => z = 1) hv)

/-- The a₂ definition agrees with the literal source perpendicularity test;
the fixed order-four condition also supplies displacement order four. -/
public theorem isA2Action_iff_source (α : MulAut Q) :
    d.IsA2Action α ↔ (quotientAut (center Q) α) ^ 2 = 1 ∧
      Nat.card (d.fixedSquareQuotient α) = 4 ∧
      ∀ v : Q ⧸ center Q, d.quadraticForm.polarBilin (Additive.ofMul v)
        (Additive.ofMul (quotientAut (center Q) α v)) = 0 := by
  constructor
  · rintro ⟨hα, hc, hs⟩
    refine ⟨hα, hc, fun v => (d.square_displacement_eq_one_iff α v).mp ?_⟩
    apply hs
    rw [← d.displacement_range_eq_fixed α hα hc]
    exact ⟨v, rfl⟩
  · rintro ⟨hα, hc, hs⟩
    refine ⟨hα, hc, ?_⟩
    intro v hv
    rw [← d.displacement_range_eq_fixed α hα hc] at hv
    obtain ⟨w, rfl⟩ := hv
    exact (d.square_displacement_eq_one_iff α w).mpr (hs w)

/-- The c₂ definition likewise records a nonperpendicular vector, rather than
an unattached conjugacy-class label. -/
public theorem isC2Action_iff_source (α : MulAut Q) :
    d.IsC2Action α ↔ (quotientAut (center Q) α) ^ 2 = 1 ∧
      Nat.card (d.fixedSquareQuotient α) = 4 ∧
      ∃ v : Q ⧸ center Q, d.quadraticForm.polarBilin (Additive.ofMul v)
        (Additive.ofMul (quotientAut (center Q) α v)) ≠ 0 := by
  constructor
  · rintro ⟨hα, hc, v, hv, hs⟩
    rw [← d.displacement_range_eq_fixed α hα hc] at hv
    obtain ⟨w, rfl⟩ := hv
    exact ⟨hα, hc, w, fun h => hs ((d.square_displacement_eq_one_iff α w).mpr h)⟩
  · rintro ⟨hα, hc, w, hs⟩
    refine ⟨hα, hc, d.quotientDisplacement α w, ?_, ?_⟩
    · rw [← d.displacement_range_eq_fixed α hα hc]
      exact ⟨w, rfl⟩
    · exact fun h => hs ((d.square_displacement_eq_one_iff α w).mp h)

include d in
private theorem fixed_of_quotient_fixed_of_swap (α : MulAut Q) (hα : α ^ 2 = 1)
    (hswap : d.left.map α.toMonoidHom = d.right) (x : Q)
    (hx : quotientAut (center Q) α (QuotientGroup.mk' (center Q) x) =
      QuotientGroup.mk' (center Q) x) : α x = x := by
  let B := d.left
  let C := d.right
  have he2 (x : Q) : α (α x) = x := by
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using DFunLike.congr_fun hα x
  have hab (b : Q) (hb : b ∈ B) : α b ∈ C := hswap.le (mem_map_of_mem α.toMonoidHom hb)
  have hac (c : Q) (hc : c ∈ C) : α c ∈ B := by
    have hc' : c ∈ d.left.map α.toMonoidHom := hswap.ge hc
    obtain ⟨b, hb, he⟩ := hc'
    change α b = c at he
    rw [← he, he2]
    exact hb
  have hn : C ≤ normalizer (B : Set Q) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    exact fun c hc b hb => d.commute b hb c hc
  have hp : x ∈ (B : Set Q) * (C : Set Q) := by
    rw [← coe_mul_of_right_le_normalizer_left B C hn, show B ⊔ C = ⊤ from d.span]
    trivial
  obtain ⟨b, hb, c, hc, rfl⟩ := hp
  rw [quotientAut_apply_mk] at hx
  have hz : (b*c)⁻¹ * α (b*c) ∈ center Q := QuotientGroup.eq.mp hx.symm
  have hdiff : (b*c)⁻¹ * α (b*c) = (b⁻¹ * α c) * (c⁻¹ * α b) := by
    rw [map_mul, mul_inv_rev, ← d.commute (α c) (hac c hc) (α b) (hab b hb)]
    calc
      c⁻¹ * b⁻¹ * (α c * α b) = c⁻¹ * (b⁻¹ * α c) * α b := by group
      _ = (b⁻¹ * α c) * c⁻¹ * α b := by
        rw [← d.commute (b⁻¹ * α c) (B.mul_mem (B.inv_mem hb) (hac c hc))
          c⁻¹ (C.inv_mem hc)]
      _ = _ := by group
  rw [hdiff, d.center_eq] at hz
  have hcZ : c⁻¹ * α b ∈ center Q := by
    rw [d.center_eq]
    exact ⟨(B.mul_mem_cancel_left (B.mul_mem (B.inv_mem hb) (hac c hc))).mp hz.1,
      C.mul_mem (C.inv_mem hc) (hab b hb)⟩
  have hcfix : α (c⁻¹ * α b) = c⁻¹ * α b := d.fixes_center α ⟨_, hcZ⟩
  have hec : c = α b * (c⁻¹ * α b)⁻¹ := by group
  rw [hec, map_mul, map_mul, he2, map_inv, hcfix]
  rw [← mul_assoc, ← d.commute b hb (α b) (hab b hb), mul_assoc]

/-- Factor interchange is the a₂ action on the literal square quotient. -/
public theorem isA2Action_of_swap (α : MulAut Q) (hα : α ^ 2 = 1)
    (hswap : d.left.map α.toMonoidHom = d.right) : d.IsA2Action α := by
  let θ : d.left ≃* d.right := (α.subgroupMap d.left).trans (MulEquiv.subgroupCongr hswap)
  let F := α.toMonoidHom.eqLocus (MonoidHom.id Q)
  have hF : F = quaternionDiagonal d.left d.right θ d.commute :=
    quaternion_diagonal_eq_fixed_of_involution_swap d.left d.right θ d.intersection_card
      d.commute d.span α hα (fun _ => rfl)
  have he := quaternion_diagonal_elementary_eight d.left d.right d.left_model.some θ
    d.intersection_card d.commute
  have hFc : Nat.card F = 8 := by rw [hF]; exact he.2.1
  have hFe : IsElementaryAbelian 2 F :=
    Eq.mp (congrArg (fun S : Subgroup Q => IsElementaryAbelian 2 S) hF.symm) he.1
  have hZF : center Q ≤ F := fun x hx => d.fixes_center α ⟨x, hx⟩
  let π := QuotientGroup.mk' (center Q)
  have him : F.map π = d.fixedSquareQuotient α := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change quotientAut (center Q) α (π x) = π x
      rw [quotientAut_apply_mk, show α x = x from hx]
    · intro hv
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center Q) v
      exact ⟨x, d.fixed_of_quotient_fixed_of_swap α hα hswap x hv, rfl⟩
  refine ⟨by rw [← map_pow, hα, map_one], ?_, ?_⟩
  · have hi := F.index_map_eq (QuotientGroup.mk'_surjective (center Q))
      (by rw [QuotientGroup.ker_mk']; exact hZF)
    have hcF := F.card_mul_index
    rw [hFc, d.card] at hcF
    have hindexF : F.index = 4 := by omega
    have hc := (F.map π).card_mul_index
    rw [hi, hindexF, d.quotient_card] at hc
    rw [← him]
    omega
  · intro v hv
    rw [← him] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    let := hFe
    apply Subtype.ext
    change (d.square (QuotientGroup.mk' (center Q) x) : Q) = 1
    rw [d.square_mk]
    exact elemPow_eq_one_of_isElementaryAbelian x hx
end Subgroup.QuaternionCentralProductData
