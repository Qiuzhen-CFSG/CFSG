module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic

/-!
# The actual quotient fibers in the terminal two-A₃ argument

For the centralizer quotient on printed p.550 of Aschbacher–Smith, the
six involutions outside the image of K have equally large intersections
with the ambient conjugacy class. Lifting quotient conjugators gives the
fiber bijections. The counts six and five are checked on C₂ × D₈ and D₈.

The printed set Δ = z₂ᴳ ∩ (R − K) also contains z₂ in the cyclic kernel B.
Consequently the literal set has cardinality 1 + 6m, rather than the
printed 6m. Its kernel fiber is a singleton. This correction preserves the
contradiction with the five involutions of the second dihedral factor.
The source centralizer recognition, factor geometry and quotient fusion
are premises of the consumer; this file does not assert those results.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2.DoubleA3
open Subgroup

private theorem dihedral_involution_count :
    Nat.card {d : DihedralGroup 4 // d ^ 2 = 1 ∧ d ≠ 1} = 5 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem product_outside_involution_count :
    Nat.card {d : Multiplicative (ZMod 2) × DihedralGroup 4 //
      d ^ 2 = 1 ∧ d.1 ≠ 1} = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem cyclic_four_unique_involution :
    ∀ a b : Multiplicative (ZMod 4),
      a ^ 2 = 1 → a ≠ 1 → b ^ 2 = 1 → b ≠ 1 → a = b := by
  decide +kernel

variable {G : Type*} [Group G]

/-- The literal ambient fusion set in the last paragraph of §2.4. -/
def fusionOutside (H : Subgroup G) (z : G) (R K : Subgroup H) : Set H :=
  {a | IsConj z (a : G) ∧ a ∈ R ∧ a ∉ K}

/-- An individual fiber of the literal quotient, restricted to the ambient
conjugacy class. It need not be one conjugacy class inside H. -/
def classFiber (H : Subgroup G) (B : Subgroup H) [B.Normal] (z : G)
    (q : H ⧸ B) : Set H :=
  {a | IsConj z (a : G) ∧ QuotientGroup.mk' B a = q}

private theorem conjugate_square {z a : G} (hz : z ^ 2 = 1)
    (ha : IsConj z a) : a ^ 2 = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp ha
  change (MulAut.conj g z) ^ 2 = 1
  rw [← map_pow, hz, map_one]

private theorem conjugate_ne_one {z a : G} (hz : z ≠ 1)
    (ha : IsConj z a) : a ≠ 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp ha
  exact fun h => hz ((MulAut.conj g).map_eq_one_iff.mp h)

private theorem fiber_card_eq (H : Subgroup G) (B : Subgroup H) [B.Normal]
    (z : G) {q q' : H ⧸ B} (hqq' : IsConj q q') :
    Nat.card (classFiber H B z q) = Nat.card (classFiber H B z q') := by
  obtain ⟨gbar, hgbar⟩ := isConj_iff.mp hqq'
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective B gbar
  let e := MulAut.conj g
  let π := QuotientGroup.mk' B
  apply Nat.card_congr (Equiv.subtypeEquiv e.toEquiv _)
  intro a
  change (IsConj z (a : G) ∧ π a = q) ↔
    (IsConj z ((e a : H) : G) ∧ π (e a) = q')
  have ha : IsConj (a : G) ((e a : H) : G) :=
    isConj_iff.mpr ⟨(g : G), rfl⟩
  have hc : IsConj z (a : G) ↔ IsConj z ((e a : H) : G) :=
    ⟨fun h => h.trans ha, fun h => h.trans ha.symm⟩
  rw [hc]
  apply and_congr_right
  intro _
  change π a = q ↔ π (g * a * g⁻¹) = q'
  rw [map_mul, map_mul, map_inv, ← hgbar]
  exact (MulAut.conj (π g)).injective.eq_iff.symm

private theorem quotient_outside_count (H : Subgroup G)
    (B R K : Subgroup H) [B.Normal]
    (e : R.map (QuotientGroup.mk' B) ≃*
      Multiplicative (ZMod 2) × DihedralGroup 4)
    (hmark : ∀ q : R.map (QuotientGroup.mk' B),
      (q : H ⧸ B) ∈ K.map (QuotientGroup.mk' B) ↔ (e q).1 = 1) :
    Nat.card {q : H ⧸ B // q ∈ R.map (QuotientGroup.mk' B) ∧
      q ^ 2 = 1 ∧ q ∉ K.map (QuotientGroup.mk' B)} = 6 := by
  let J := {q : R.map (QuotientGroup.mk' B) //
    q ^ 2 = 1 ∧ (q : H ⧸ B) ∉ K.map (QuotientGroup.mk' B)}
  have e₁ : J ≃ {q : H ⧸ B // q ∈ R.map (QuotientGroup.mk' B) ∧
      q ^ 2 = 1 ∧ q ∉ K.map (QuotientGroup.mk' B)} := {
    toFun := fun q => ⟨q.1, q.1.property,
      congrArg Subtype.val q.2.1, q.2.2⟩
    invFun := fun q => ⟨⟨q.1, q.2.1⟩, Subtype.ext q.2.2.1, q.2.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have e₂ : J ≃ {d : Multiplicative (ZMod 2) × DihedralGroup 4 //
      d ^ 2 = 1 ∧ d.1 ≠ 1} :=
    Equiv.subtypeEquiv e.toEquiv (fun q => by
      change (q ^ 2 = 1 ∧ (q : H ⧸ B) ∉ K.map (QuotientGroup.mk' B)) ↔
        ((e q) ^ 2 = 1 ∧ (e q).1 ≠ 1)
      rw [← map_pow, e.map_eq_one_iff, hmark])
  exact (Nat.card_congr e₁).symm.trans
    ((Nat.card_congr e₂).trans product_outside_involution_count)

/-- Six equal fibers in the actual quotient. This counts precisely the
class elements whose quotient image lies outside the image of K; the
identity fiber is deliberately retained separately in `terminal_count`. -/
theorem outside_quotient_fiber_count [Finite G] (H : Subgroup G)
    (B R K : Subgroup H) [B.Normal] (z : G) (hz : z ^ 2 = 1)
    (hBR : B ≤ R) (u : H)
    (e : R.map (QuotientGroup.mk' B) ≃*
      Multiplicative (ZMod 2) × DihedralGroup 4)
    (hmark : ∀ q : R.map (QuotientGroup.mk' B),
      (q : H ⧸ B) ∈ K.map (QuotientGroup.mk' B) ↔ (e q).1 = 1)
    (hfuse : ∀ q : H ⧸ B, q ∈ R.map (QuotientGroup.mk' B) → q ^ 2 = 1 →
      q ∉ K.map (QuotientGroup.mk' B) → IsConj (QuotientGroup.mk' B u) q) :
    Nat.card {a : H // IsConj z (a : G) ∧ a ∈ R ∧
      QuotientGroup.mk' B a ∉ K.map (QuotientGroup.mk' B)} =
      6 * Nat.card (classFiber H B z (QuotientGroup.mk' B u)) := by
  classical
  let π := QuotientGroup.mk' B
  let J := {q : H ⧸ B // q ∈ R.map π ∧ q ^ 2 = 1 ∧ q ∉ K.map π}
  let F := fun q : J => classFiber H B z q.val
  have hsaturated {a : H} (ha : π a ∈ R.map π) : a ∈ R := by
    have he : (R.map π).comap π = R :=
      comap_map_eq_self (by simpa only [π, QuotientGroup.ker_mk'] using hBR)
    exact he ▸ ha
  let ec : {a : H // IsConj z (a : G) ∧ a ∈ R ∧ π a ∉ K.map π} ≃
      Σ q : J, F q := {
    toFun := fun a => ⟨⟨π a.1, mem_map_of_mem π a.2.2.1, by
      have ha : a.1 ^ 2 = 1 := Subtype.ext (conjugate_square hz a.2.1)
      rw [← map_pow, ha, map_one], a.2.2.2⟩, ⟨a.1, a.2.1, rfl⟩⟩
    invFun := fun p => ⟨p.2.1, p.2.2.1,
      hsaturated (p.2.2.2.symm ▸ p.1.2.1), p.2.2.2.symm ▸ p.1.2.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun p => by
      rcases p with ⟨⟨q, hq⟩, ⟨a, ha, he⟩⟩
      dsimp only at he
      subst q
      rfl }
  let : Fintype J := Fintype.ofFinite J
  have hF (q : J) : Nat.card (F q) = Nat.card (classFiber H B z (π u)) :=
    (fiber_card_eq H B z (hfuse q q.2.1 q.2.2.1 q.2.2.2)).symm
  rw [Nat.card_congr ec, Nat.card_sigma]
  simp only [hF, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card,
    show Nat.card J = 6 from quotient_outside_count H B R K e hmark]

/-- The identity quotient fiber consists of the source involution alone.
The cyclic order-four marking proves uniqueness, instead of assuming it. -/
theorem identity_fiber_singleton (H : Subgroup G)
    (B : Subgroup H) [B.Normal] (z : H) (hz : z ^ 2 = 1) (hz1 : z ≠ 1)
    (hzB : z ∈ B) (eB : B ≃* Multiplicative (ZMod 4)) :
    classFiber H B (z : G) 1 = {z} := by
  ext a
  constructor
  · intro ha
    have haB : a ∈ B := (QuotientGroup.eq_one_iff a).mp ha.2
    have hzG : (z : G) ^ 2 = 1 := congrArg Subtype.val hz
    have hzG1 : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
    have ha2 : a ^ 2 = 1 := Subtype.ext (conjugate_square hzG ha.1)
    have ha1 : a ≠ 1 := fun h =>
      conjugate_ne_one hzG1 ha.1 (congrArg Subtype.val h)
    have he : eB ⟨a, haB⟩ = eB ⟨z, hzB⟩ := cyclic_four_unique_involution _ _
      (by rw [← map_pow]; exact eB.map_eq_one_iff.mpr (Subtype.ext ha2))
      (fun h => ha1 (congrArg Subtype.val (eB.map_eq_one_iff.mp h)))
      (by rw [← map_pow]; exact eB.map_eq_one_iff.mpr (Subtype.ext hz))
      (fun h => hz1 (congrArg Subtype.val (eB.map_eq_one_iff.mp h)))
    exact congrArg Subtype.val (eB.injective he)
  · intro ha
    have he : a = z := ha
    subst a
    exact ⟨IsConj.refl _, (QuotientGroup.eq_one_iff z).mpr hzB⟩

/-- A dihedral factor has five members of the ambient involution class,
provided the model's involutions all belong to that class. -/
theorem dihedral_fusion_card (H : Subgroup G) (D : Subgroup H) (z : G)
    (hz : z ^ 2 = 1) (hz1 : z ≠ 1) (eD : D ≃* DihedralGroup 4)
    (hfuse : ∀ a : D, a ^ 2 = 1 → a ≠ 1 → IsConj z ((a : H) : G)) :
    Nat.card {a : H // IsConj z (a : G) ∧ a ∈ D} = 5 := by
  let e₁ : {a : H // IsConj z (a : G) ∧ a ∈ D} ≃
      {a : D // a ^ 2 = 1 ∧ a ≠ 1} := {
    toFun := fun a => ⟨⟨a, a.2.2⟩,
      Subtype.ext (Subtype.ext (conjugate_square hz a.2.1)),
      fun h => conjugate_ne_one hz1 a.2.1
        (congrArg (fun d : D => ((d : H) : G)) h)⟩
    invFun := fun a => ⟨a.1, hfuse a.1 a.2.1 a.2.2, a.1.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let e₂ : {a : D // a ^ 2 = 1 ∧ a ≠ 1} ≃
      {a : DihedralGroup 4 // a ^ 2 = 1 ∧ a ≠ 1} :=
    Equiv.subtypeEquiv eD.toEquiv (fun a => by
      change (a ^ 2 = 1 ∧ a ≠ 1) ↔ ((eD a) ^ 2 = 1 ∧ eD a ≠ 1)
      simp only [ne_eq, ← map_pow, eD.map_eq_one_iff])
  exact (Nat.card_congr (e₁.trans e₂)).trans dihedral_involution_count

/-- The literal terminal set is a singleton kernel fiber together with
six equally large nonidentity quotient fibers. `hseparate` states the
remaining geometric fact, not a count or a cardinality equation. -/
theorem terminal_count [Finite G] (H : Subgroup G)
    (B R K : Subgroup H) [B.Normal] (z : H) (hz : z ^ 2 = 1)
    (hz1 : z ≠ 1) (hzB : z ∈ B) (hzK : z ∉ K)
    (hBR : B ≤ R) (eB : B ≃* Multiplicative (ZMod 4)) (u : H)
    (e : R.map (QuotientGroup.mk' B) ≃*
      Multiplicative (ZMod 2) × DihedralGroup 4)
    (hmark : ∀ q : R.map (QuotientGroup.mk' B),
      (q : H ⧸ B) ∈ K.map (QuotientGroup.mk' B) ↔ (e q).1 = 1)
    (hfuse : ∀ q : H ⧸ B, q ∈ R.map (QuotientGroup.mk' B) → q ^ 2 = 1 →
      q ∉ K.map (QuotientGroup.mk' B) → IsConj (QuotientGroup.mk' B u) q)
    (hseparate : ∀ a : H, IsConj (z : G) (a : G) → a ∈ R → a ∉ K →
      a ∉ B → QuotientGroup.mk' B a ∉ K.map (QuotientGroup.mk' B)) :
    Nat.card (fusionOutside H (z : G) R K) =
      1 + 6 * Nat.card (classFiber H B (z : G) (QuotientGroup.mk' B u)) := by
  classical
  let π := QuotientGroup.mk' B
  let Outside := {a : H // IsConj (z : G) (a : G) ∧ a ∈ R ∧ π a ∉ K.map π}
  have hidentity := identity_fiber_singleton H B z hz hz1 hzB eB
  have hkernel (a : H) (ha : IsConj (z : G) (a : G)) (haB : a ∈ B) : a = z := by
    have h : a ∈ classFiber H B (z : G) 1 :=
      ⟨ha, (QuotientGroup.eq_one_iff a).mpr haB⟩
    rwa [hidentity] at h
  let ec : fusionOutside H (z : G) R K ≃ Unit ⊕ Outside := {
    toFun := fun a => if ha : a.1 ∈ B then .inl ()
      else .inr ⟨a.1, a.2.1, a.2.2.1, hseparate a.1 a.2.1 a.2.2.1 a.2.2.2 ha⟩
    invFun := fun p => match p with
      | .inl _ => ⟨z, IsConj.refl _, hBR hzB, hzK⟩
      | .inr a => ⟨a.1, a.2.1, a.2.2.1,
          fun ha => a.2.2.2 (mem_map_of_mem π ha)⟩
    left_inv := fun a => by
      dsimp only
      split_ifs with ha
      · apply Subtype.ext
        exact (hkernel a.1 a.2.1 ha).symm
      · rfl
    right_inv := fun p => by
      rcases p with _ | a
      · simp only [hzB, ↓reduceDIte]
      · have haB : a.1 ∉ B := by
          intro ha
          apply a.2.2.2
          have he : π a.1 = 1 := (QuotientGroup.eq_one_iff a.1).mpr ha
          rw [he]
          exact (K.map π).one_mem
        simp only [haB, ↓reduceDIte]
        rfl }
  rw [Nat.card_congr ec, Nat.card_sum, Nat.card_eq_fintype_card (α := Unit)]
  change 1 + Nat.card Outside = _
  rw [show Nat.card Outside = 6 * Nat.card (classFiber H B (z : G) (π u)) from
    outside_quotient_fiber_count H B R K (z : G) (congrArg Subtype.val hz)
      hBR u e hmark hfuse]

end CFSG.Quasithin.Chapter2.DoubleA3
