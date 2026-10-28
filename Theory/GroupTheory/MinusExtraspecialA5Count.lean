module
public import Theory.GroupTheory.MinusExtraspecialA5Count.Model
public import Theory.GroupTheory.MinusExtraspecialA5Fusion
import all Theory.GroupTheory.MinusExtraspecialA5Fusion

/-!
# Involution counts in a minus-extraspecial A₅ extension

Let Q be a self-centralizing normal subgroup isomorphic to Q₈ ∘ D₈ and
H/Q be isomorphic to A₅. Given one outside involution, quotient fusion
supplies an involution in each of the fifteen involution cosets. Multiplying
by a core element identifies the involutions in each coset with the eight
cocycles of its conjugation action. Thus there are 120 outside involutions.

For a fixed outside involution v, the square of qv is q times its conjugate
by v. The exponent-four core reduces membership of its central involution
in the rotation subgroup to the two model equations. The checked count is
eight. All quotient maps and cyclic subgroups here are the literal ones.

The internal `import all` deliberately reuses the action and kernel proofs
from the preceding fusion module; private action coordinates do not escape
into either public theorem. No ambient recognition or order is used.
Source: Aschbacher, *Sporadic Groups* (1994), 47.1, printed p.259.
-/

open Subgroup
namespace MinusExtraspecial
open FixedFourCalculation.Outside
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
private theorem cocycle_card (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model)
    (hc : centralizer (Q : Set H) ≤ Q)
    (eA : (H ⧸ Q) ≃* alternatingGroup (Fin 5))
    (v : H) (hv : v ^ 2 = 1) (hvQ : v ∉ Q) :
    Nat.card {q : Q // q * MulAut.conjNormal v q = 1} = 8 := by
  let a := modelAction Q e v
  have ha : a ^ 2 = 1 := by rw [← map_pow, hv, map_one]
  have heven : Equiv.Perm.sign (fivePointAction a) = 1 := pointAction_even Q e hc eA v
  have hne : fivePointAction a ≠ 1 := by
    intro heq
    apply hvQ
    rw [← pointAction_kernel Q e hc]
    exact heq
  have heq : {q : Q // q * MulAut.conjNormal v q = 1} ≃
      {d : Model // d * a d = 1} := Equiv.subtypeEquiv e.toEquiv (fun q => by
    change q * MulAut.conjNormal v q = 1 ↔ e q * e (MulAut.conjNormal v (e.symm (e q))) = 1
    rw [e.symm_apply_apply, ← map_mul, e.map_eq_one_iff])
  exact (Nat.card_congr heq).trans (Count.model_counts a ha heven hne).1

omit [Finite H] in
private theorem coset_involutions_card (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model)
    (hc : centralizer (Q : Set H) ≤ Q)
    (eA : (H ⧸ Q) ≃* alternatingGroup (Fin 5))
    (v : H) (hv : v ^ 2 = 1) (hvQ : v ∉ Q) :
    Nat.card {u : H // u ^ 2 = 1 ∧ QuotientGroup.mk' Q u = QuotientGroup.mk' Q v} = 8 := by
  let a := MulAut.conjNormal v (H := Q)
  have hvInv : v⁻¹ = v := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hv)
  let ec : {q : Q // q * a q = 1} ≃
      {u : H // u ^ 2 = 1 ∧ QuotientGroup.mk' Q u = QuotientGroup.mk' Q v} := {
    toFun := fun q => ⟨(q.val : H) * v, by
      have hh := congrArg Subtype.val q.property
      change (q.val : H) * (v * (q.val : H) * v⁻¹) = 1 at hh
      constructor
      · simpa only [pow_two, hvInv, mul_assoc] using hh
      · have hqπ : QuotientGroup.mk' Q (q.val : H) = 1 :=
          (QuotientGroup.eq_one_iff (N := Q) (q.val : H)).mpr q.val.property
        rw [map_mul, hqπ, one_mul]⟩
    invFun := fun u => by
      have hq : u.val * v⁻¹ ∈ Q := by
        simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp u.property.2
      refine ⟨⟨u.val * v⁻¹, hq⟩, ?_⟩
      apply Subtype.ext
      change (u.val * v⁻¹) * (v * (u.val * v⁻¹) * v⁻¹) = 1
      calc
        _ = u.val ^ 2 * (v ^ 2)⁻¹ := by simp only [pow_two]; group
        _ = 1 := by rw [u.property.1, hv]; simp
    left_inv := fun q => Subtype.ext (Subtype.ext (by simp))
    right_inv := fun u => Subtype.ext (by simp) }
  exact (Nat.card_congr ec).symm.trans (cocycle_card Q e hc eA v hv hvQ)

omit [Finite H] in
private theorem quotient_involutions_card (Q : Subgroup H) [Q.Normal]
    (eA : (H ⧸ Q) ≃* alternatingGroup (Fin 5)) :
    Nat.card {a : H ⧸ Q // orderOf a = 2} = 15 := by
  let ec : {a : H ⧸ Q // orderOf a = 2} ≃
      {a : alternatingGroup (Fin 5) // a ^ 2 = 1 ∧ a ≠ 1} :=
    Equiv.subtypeEquiv eA.toEquiv (fun a => by
      rw [← orderOf_eq_prime_iff]
      change orderOf a = 2 ↔ orderOf (eA a) = 2
      rw [eA.orderOf_eq])
  rw [Nat.card_congr ec, Nat.card_eq_fintype_card]
  decide +kernel

/-- An existing outside involution supplies representatives for all fifteen
involution cosets of the A₅ quotient; each has eight involution lifts. -/
public theorem outside_involutions_card (Q : Subgroup H) [Q.Normal]
    (e : Q ≃* Model) (hc : centralizer (Q : Set H) ≤ Q)
    (eA : (H ⧸ Q) ≃* alternatingGroup (Fin 5))
    (v : H) (hv : orderOf v = 2) (hvQ : v ∉ Q) :
    Nat.card {u : H // orderOf u = 2 ∧ u ∉ Q} = 120 := by
  classical
  let π := QuotientGroup.mk' Q
  have hv2 : v ^ 2 = 1 := hv ▸ pow_orderOf_eq_one v
  have hvbar : orderOf (π v) = 2 := orderOf_eq_prime
    (by rw [← map_pow, hv2, map_one])
    (fun hh => hvQ ((QuotientGroup.eq_one_iff v).mp hh))
  have hrep (a : H ⧸ Q) (ha : orderOf a = 2) :
      ∃ w : H, w ^ 2 = 1 ∧ w ∉ Q ∧ π w = a := by
    have hconj := alternatingGroup.five_involutions_isConj (eA (π v)) (eA a)
      ((eA.orderOf_eq _).trans hvbar) ((eA.orderOf_eq _).trans ha)
    have hconj' : IsConj (π v) a := by
      simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
        eA.symm.toMonoidHom.map_isConj hconj
    obtain ⟨gbar, hgbar⟩ := isConj_iff.mp hconj'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q gbar
    let w := MulAut.conj g v
    have hw : π w = a := by simpa only [w, MulAut.conj_apply, map_mul, map_inv] using hgbar
    refine ⟨w, ?_, ?_, hw⟩
    · change (MulAut.conj g v) ^ 2 = 1
      rw [← map_pow, hv2, map_one]
    · intro hwQ
      have he := (QuotientGroup.eq_one_iff w).mpr hwQ
      change π w = 1 at he
      rw [hw] at he
      rw [he, orderOf_one] at ha
      omega
  let I := {a : H ⧸ Q // orderOf a = 2}
  let F := fun a : I => {u : H // u ^ 2 = 1 ∧ π u = a.val}
  let ec : {u : H // orderOf u = 2 ∧ u ∉ Q} ≃ Σ a : I, F a := {
    toFun := fun u =>
      have hu2 : u.val ^ 2 = 1 := (orderOf_eq_prime_iff.mp u.property.1).1
      ⟨⟨π u.val, orderOf_eq_prime (by rw [← map_pow, hu2, map_one])
        (fun hh => u.property.2 ((QuotientGroup.eq_one_iff u.val).mp hh))⟩,
        ⟨u.val, hu2, rfl⟩⟩
    invFun := fun p => by
      have hn : p.1.val ≠ 1 := by intro he; have hh := p.1.property; rw [he, orderOf_one] at hh; omega
      have huQ : p.2.val ∉ Q := by
        intro hQ
        exact hn (p.2.property.2.symm.trans ((QuotientGroup.eq_one_iff _).mpr hQ))
      exact ⟨p.2.val, orderOf_eq_prime p.2.property.1
        (fun he => huQ (he.symm ▸ Q.one_mem)), huQ⟩
    left_inv := fun u => rfl
    right_inv := fun p => by
      rcases p with ⟨⟨a, ha⟩, ⟨u, hu, he⟩⟩
      dsimp only at he
      subst a
      rfl }
  let : Fintype I := Fintype.ofFinite I
  have hF (a : I) : Nat.card (F a) = 8 := by
    obtain ⟨w, hw, hwQ, hwπ⟩ := hrep a.val a.property
    change Nat.card {u : H // u ^ 2 = 1 ∧ π u = a.val} = 8
    rw [← hwπ]
    exact coset_involutions_card Q e hc eA w hw hwQ
  rw [Nat.card_congr ec, Nat.card_sigma]
  simp only [hF, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, quotient_involutions_card Q eA]
  norm_num

/-- The rotation subgroup meets the core in the powers of the rotation square.
The exponent-four model reduces membership of an involution to two equations. -/
private theorem rotation_mem_iff (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model)
    (v : H) (hv : v ^ 2 = 1) (hvQ : v ∉ Q) (z q : Q) (hz : orderOf z = 2) :
    (z : H) ∈ zpowers ((q : H) * v) ↔
      q * MulAut.conjNormal v q = z ∨ (q * MulAut.conjNormal v q) ^ 2 = z := by
  classical
  let g := (q : H) * v
  let w := q * MulAut.conjNormal v q
  let π := QuotientGroup.mk' Q
  have hvInv : v⁻¹ = v := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hv)
  have hg2 : g ^ 2 = (w : H) := by
    change ((q : H) * v) ^ 2 = (q : H) * (v * (q : H) * v⁻¹)
    simp only [pow_two, hvInv, mul_assoc]
  have hw4 : w ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact (show ∀ d : Model, d ^ 4 = 1 by decide +kernel) (e w)
  have hg8 : g ^ 8 = 1 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, hg2, ← Subgroup.coe_pow, hw4, Subgroup.coe_one]
  have hzH : orderOf (z : H) = 2 := (orderOf_coe z).trans hz
  have hz2 : (z : H) ^ 2 = 1 := hzH ▸ pow_orderOf_eq_one (z : H)
  have hzNe : (z : H) ≠ 1 := by intro he; rw [he, orderOf_one] at hzH; omega
  have hπg : π g = π v := by
    change π ((q : H) * v) = π v
    have hqπ : π (q : H) = 1 :=
      (QuotientGroup.eq_one_iff (N := Q) (q : H)).mpr q.property
    rw [map_mul, hqπ, one_mul]
  have hπv : orderOf (π v) = 2 := orderOf_eq_prime
    (by rw [← map_pow, hv, map_one])
    (fun he => hvQ ((QuotientGroup.eq_one_iff _).mp he))
  constructor
  · intro hmem
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hmem)
    have hlt : n < 8 := lt_of_lt_of_le (Finset.mem_range.mp hn)
      (Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one hg8))
    change g ^ n = (z : H) at he
    have hπ : (π v) ^ n = 1 := by
      rw [← hπg, ← map_pow, he]
      exact (QuotientGroup.eq_one_iff _).mpr z.property
    have hd : 2 ∣ n := hπv ▸ orderOf_dvd_of_pow_eq_one hπ
    obtain ⟨k, rfl⟩ := hd
    have hk : k < 4 := by omega
    rw [pow_mul, hg2] at he
    interval_cases k
    · simp only [pow_zero] at he
      exact (hzNe he.symm).elim
    · exact Or.inl (Subtype.ext (by simpa only [pow_one] using he))
    · exact Or.inr (Subtype.ext he)
    · have h6 : (w : H) ^ 6 = 1 := by
        rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, he, hz2]
      have h4 : (w : H) ^ 4 = 1 := congrArg Subtype.val hw4
      have h2 : (w : H) ^ 2 = 1 := by
        simpa only [show (6 : ℕ) = 4 + 2 from rfl, pow_add, h4, one_mul] using h6
      have h3 : (w : H) ^ 3 = (w : H) := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, h2, pow_one, one_mul]
      exact Or.inl (Subtype.ext (h3.symm.trans he))
  · rintro (he | he)
    · have hh : g ^ 2 = (z : H) := hg2.trans (congrArg Subtype.val he)
      exact hh ▸ npow_mem_zpowers g 2
    · have hh : g ^ 4 = (z : H) := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hg2]
        exact congrArg Subtype.val he
      exact hh ▸ npow_mem_zpowers g 4

/-- Each outside involution has exactly eight compatible involutions in the
minus-extraspecial core, using literal cyclic-subgroup membership. -/
public theorem compatible_core_card (Q : Subgroup H) [Q.Normal]
    (e : Q ≃* Model) (hc : centralizer (Q : Set H) ≤ Q)
    (eA : (H ⧸ Q) ≃* alternatingGroup (Fin 5))
    (v : H) (hv : orderOf v = 2) (hvQ : v ∉ Q)
    (z : Q) (hz : orderOf z = 2) (hez : e z = quaternion MinusExtraspecial.z) :
    Nat.card {q : Q // orderOf q = 2 ∧ (z : H) ∈ zpowers ((q : H) * v)} = 8 := by
  let a := modelAction Q e v
  have hv2 : v ^ 2 = 1 := hv ▸ pow_orderOf_eq_one v
  have ha : a ^ 2 = 1 := by rw [← map_pow, hv2, map_one]
  have heven : Equiv.Perm.sign (fivePointAction a) = 1 := pointAction_even Q e hc eA v
  have hne : fivePointAction a ≠ 1 := by
    intro heq
    apply hvQ
    rw [← pointAction_kernel Q e hc]
    exact heq
  let ec : {q : Q // orderOf q = 2 ∧ (z : H) ∈ zpowers ((q : H) * v)} ≃
      {d : Model // orderOf d = 2 ∧
        (d * a d = quaternion MinusExtraspecial.z ∨
          (d * a d) ^ 2 = quaternion MinusExtraspecial.z)} :=
    Equiv.subtypeEquiv e.toEquiv (fun q => by
      have heq : e q * a (e q) = e (q * MulAut.conjNormal v q) := by
        change e q * e (MulAut.conjNormal v (e.symm (e q))) = _
        rw [e.symm_apply_apply, map_mul]
      change (_ ∧ _) ↔ (orderOf (e q) = 2 ∧
        (e q * a (e q) = quaternion MinusExtraspecial.z ∨
          (e q * a (e q)) ^ 2 = quaternion MinusExtraspecial.z))
      rw [e.orderOf_eq, rotation_mem_iff Q e v hv2 hvQ z q hz,
        heq, ← hez, ← map_pow, e.injective.eq_iff, e.injective.eq_iff])
  exact (Nat.card_congr ec).trans (Count.model_counts a ha heven hne).2
end MinusExtraspecial
