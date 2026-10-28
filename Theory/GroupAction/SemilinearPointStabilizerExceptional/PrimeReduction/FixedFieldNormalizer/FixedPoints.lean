module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.Normalizers
public import Mathlib.FieldTheory.Fixed

/-!
# Fixed fields of coefficient subgroups

The fixed scalars act transitively on the nonzero common fixed points.
If the ambient normalizer acts nontrivially on a coefficient subgroup, the
zero-stabilizer comparison forces its centralizer to fix zero. Conjugating
a fixed scalar by a normalizer element moving zero then shows that every
nonzero common fixed point equals one. Artin's fixed-field degree theorem
therefore gives the actual field order as two to the subgroup order.

For an order-p subgroup, divisibility of the coefficient order by the field
degree yields n = p and |Γ| = p. For Γ itself, orbit–stabilizer gives the
literal normalizer order 2|Γ| and its centralizer is Γ.

Source: GLS, Volume 4, Chapter 1, Lemma 3.9, after Q = R,
`refs/KGroup/GLS4/Chapter1.tex`, lines 444–451. Noncentral normalizer action
is an explicit input here; the cyclic Sylow and transfer argument supplies it.
-/

public section

open MulAction
open scoped IsMulCommutative
namespace MulAction.SemilinearPointStabilizer.Coordinates
variable {X F : Type*} [Group X] [Field F] [MulAction X F] [FaithfulSMul X F]
variable (c : Coordinates X F)
include c

/-- Coefficient subgroups preserve the field operations under their original action. -/
@[expose, implicit_reducible] def coefficientSemiringAction {P : Subgroup X} (hP : P ≤ twoPoint (X := X) (F := F)) :
    MulSemiringAction P F where
  smul u x := (u : X) • x
  one_smul x := one_smul X x
  mul_smul u v x := mul_smul (u : X) (v : X) x
  smul_zero u := by
    change (u : X) • (0 : F) = 0
    simpa only [fieldAut_apply] using (c.fieldAut ⟨u, hP u.property⟩).map_zero
  smul_add u x y := by
    change (u : X) • (x + y) = (u : X) • x + (u : X) • y
    simpa only [fieldAut_apply] using (c.fieldAut ⟨u, hP u.property⟩).map_add x y
  smul_one u := by
    change (u : X) • (1 : F) = 1
    simpa only [fieldAut_apply] using (c.fieldAut ⟨u, hP u.property⟩).map_one
  smul_mul u x y := by
    change (u : X) • (x * y) = (u : X) • x * (u : X) • y
    simpa only [fieldAut_apply] using (c.fieldAut ⟨u, hP u.property⟩).map_mul x y

omit c [Field F] [FaithfulSMul X F] in
private theorem normalizer_smul_fixed {P : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (P : Set X)) {x : F}
    (hx : ∀ u ∈ P, u • x = x) : ∀ u ∈ P, u • (g • x) = g • x := by
  intro u hu
  have hv : g⁻¹ * u * g ∈ P := by
    simpa using (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (P : Set X)).inv_mem hg) u).mp hu
  have h := congrArg (fun y : F => g • y) (hx _ hv)
  simpa only [mul_smul, smul_inv_smul] using h

/-- A scalar centralizes P precisely when its multiplier is fixed by P. -/
theorem scalar_mem_centralizer_iff_fixed {P : Subgroup X}
    (hP : P ≤ twoPoint (X := X) (F := F)) (a : Fˣ) :
    c.scalar a ∈ Subgroup.centralizer (P : Set X) ↔ ∀ u ∈ P, u • (a : F) = a := by
  constructor
  · intro ha u hu
    have h := congrArg (fun g : X => g • (1 : F)) (ha u hu)
    simpa only [mul_smul, c.scalar_smul, mul_one,
      mem_stabilizer_iff.mp (hP hu).2] using h
  · intro ha u hu
    apply eq_of_smul_eq_smul (α := F)
    intro x
    have hm := (c.fieldAut ⟨u, hP hu⟩).map_mul (a : F) x
    simp only [c.fieldAut_apply] at hm
    simpa only [mul_smul, c.scalar_smul, ha u hu] using hm

/-- The fixed scalars are transitive on the nonzero common fixed points. -/
theorem exists_centralizing_scalar_smul_eq {P : Subgroup X}
    (hP : P ≤ twoPoint (X := X) (F := F)) {x y : F}
    (hx : ∀ u ∈ P, u • x = x) (hy : ∀ u ∈ P, u • y = y)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    ∃ a : Fˣ, c.scalar a ∈ Subgroup.centralizer (P : Set X) ∧ c.scalar a • x = y := by
  let a : Fˣ := Units.mk0 (y / x) (div_ne_zero hy0 hx0)
  refine ⟨a, (c.scalar_mem_centralizer_iff_fixed hP a).mpr ?_, ?_⟩
  · intro u hu
    change u • (y / x) = y / x
    have hd := map_div₀ (c.fieldAut ⟨u, hP hu⟩) y x
    simpa only [c.fieldAut_apply, hx u hu, hy u hu] using hd
  · exact (c.scalar_smul a x).trans (div_mul_cancel₀ y hx0)

/-- Noncentral normalizer action forces the centralizer to fix zero. -/
theorem centralizer_le_stabilizer_of_normalizer_not_le [Finite F]
    {P : Subgroup X} (hP : P ≤ twoPoint (X := X) (F := F))
    (hNC : ¬ Subgroup.normalizer (P : Set X) ≤ Subgroup.centralizer (P : Set X)) :
    Subgroup.centralizer (P : Set X) ≤ stabilizer X (0 : F) := by
  classical
  obtain ⟨g, hgN, hgC⟩ := Set.not_subset.mp hNC
  have hzero : ∀ u ∈ P, u • (0 : F) = 0 := fun u hu =>
    mem_stabilizer_iff.mp (hP hu).1
  have hg0 : g • (0 : F) ≠ 0 := by
    intro h
    exact hgC (c.stabilizer_inf_normalizer_le_centralizer hP ⟨h, hgN⟩)
  intro b hb
  change b • (0 : F) = 0
  by_contra hb0
  obtain ⟨a, haC, hab⟩ := c.exists_centralizing_scalar_smul_eq hP
    (normalizer_smul_fixed (Subgroup.centralizer_le_normalizer _ hb) hzero)
    (normalizer_smul_fixed hgN hzero) hb0 hg0
  let d := c.scalar a * b
  have hdC : d ∈ Subgroup.centralizer (P : Set X) :=
    (Subgroup.centralizer _).mul_mem haC hb
  have hd0 : d • (0 : F) = g • (0 : F) := by simpa only [d, mul_smul] using hab
  have hdiff0 : (d⁻¹ * g) • (0 : F) = 0 := by
    rw [mul_smul, ← hd0, inv_smul_smul]
  have hdiffN : d⁻¹ * g ∈ Subgroup.normalizer (P : Set X) :=
    (Subgroup.normalizer _).mul_mem
      ((Subgroup.normalizer _).inv_mem (Subgroup.centralizer_le_normalizer _ hdC)) hgN
  have hdiffC := c.stabilizer_inf_normalizer_le_centralizer hP ⟨hdiff0, hdiffN⟩
  apply hgC
  change g ∈ Subgroup.centralizer (P : Set X)
  simpa only [mul_inv_cancel_left] using (Subgroup.centralizer _).mul_mem hdC hdiffC

/-- The source orbit discrepancy leaves exactly zero and one fixed by P. -/
theorem fixed_eq_zero_or_one_of_normalizer_not_le [Finite F]
    {P : Subgroup X} (hP : P ≤ twoPoint (X := X) (F := F))
    (hNC : ¬ Subgroup.normalizer (P : Set X) ≤ Subgroup.centralizer (P : Set X))
    {x : F} (hx : ∀ u ∈ P, u • x = x) : x = 0 ∨ x = 1 := by
  classical
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  right
  obtain ⟨g, hgN, hgC⟩ := Set.not_subset.mp hNC
  have hC0 := c.centralizer_le_stabilizer_of_normalizer_not_le hP hNC
  have hg0 : g • (0 : F) ≠ 0 := by
    intro h
    exact hgC (c.stabilizer_inf_normalizer_le_centralizer hP ⟨h, hgN⟩)
  let a : Fˣ := Units.mk0 x hx0
  have haC := (c.scalar_mem_centralizer_iff_fixed hP a).mpr hx
  have hconj : g⁻¹ * c.scalar a * g ∈ Subgroup.centralizer (P : Set X) := by
    let C := (Subgroup.centralizer (P : Set X)).subgroupOf (Subgroup.normalizer (P : Set X))
    have hc : (⟨c.scalar a, Subgroup.centralizer_le_normalizer _ haC⟩ :
      Subgroup.normalizer (P : Set X)) ∈ C := haC
    have hh := (inferInstance : C.Normal).conj_mem _ hc ⟨g⁻¹, (Subgroup.normalizer _).inv_mem hgN⟩
    change g⁻¹ * c.scalar a * (g⁻¹)⁻¹ ∈ Subgroup.centralizer (P : Set X) at hh
    simpa only [inv_inv] using hh
  have hz := congrArg (fun y : F => g • y) (mem_stabilizer_iff.mp (hC0 hconj))
  have hfix : c.scalar a • (g • (0 : F)) = g • (0 : F) := by
    simpa only [mul_smul, smul_inv_smul] using hz
  have ha1 : a = 1 := by
    by_contra h
    exact hg0 ((c.scalar_fixed_iff a h _).mp hfix)
  exact congrArg Units.val ha1

/-- The degree over the actual fixed field gives the field cardinality. -/
theorem card_field_eq_two_pow_card_of_normalizer_not_le [Finite X] [Finite F]
    {P : Subgroup X} (hP : P ≤ twoPoint (X := X) (F := F))
    (hNC : ¬ Subgroup.normalizer (P : Set X) ≤ Subgroup.centralizer (P : Set X)) :
    Nat.card F = 2 ^ Nat.card P := by
  let := c.coefficientSemiringAction hP
  let : Fintype P := Fintype.ofFinite P
  let E := FixedPoints.subfield P F
  have hE : Nat.card E = 2 := by
    apply (Nat.card_eq_two_iff' (0 : E)).mpr
    refine ⟨1, one_ne_zero, ?_⟩
    intro x hx
    apply Subtype.ext
    have hxfix : ∀ u ∈ P, u • (x : F) = x := fun u hu => x.property ⟨u, hu⟩
    rcases c.fixed_eq_zero_or_one_of_normalizer_not_le hP hNC hxfix with hz | ho
    · exact False.elim (hx (Subtype.ext hz))
    · exact ho
  have hdeg : Module.finrank E F = Nat.card P := by
    exact (FixedPoints.finrank_eq_card P F).trans (Fintype.card_eq_nat_card)
  rw [Module.natCard_eq_pow_finrank (K := E), hE, hdeg]

/-- Application to an order-p coefficient subgroup: the field degree and
whole two-point stabilizer both have order p. -/
theorem degree_and_card_twoPoint_of_prime_normalizer_not_le [Finite X] [Finite F]
    {n p : ℕ} (hF : Nat.card F = 2 ^ n) {P : Subgroup X}
    (hP : P ≤ twoPoint (X := X) (F := F)) (hcard : Nat.card P = p)
    (hNC : ¬ Subgroup.normalizer (P : Set X) ≤ Subgroup.centralizer (P : Set X)) :
    n = p ∧ Nat.card (twoPoint (X := X) (F := F)) = p := by
  have hn : n = p := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    change 2 ^ n = 2 ^ p
    rw [← hF, c.card_field_eq_two_pow_card_of_normalizer_not_le hP hNC, hcard]
  refine ⟨hn, Nat.dvd_antisymm ?_ ?_⟩
  · simpa only [hn] using c.card_twoPoint_dvd Nat.prime_two hF
  · exact hcard ▸ Subgroup.card_dvd_of_le hP


/-- The zero stabilizer in the normalizer is exactly Γ once its fixed field
has two elements. -/
theorem stabilizer_inf_twoPoint_normalizer_eq [Finite F]
    (hNC : ¬ Subgroup.normalizer (twoPoint (X := X) (F := F) : Set X) ≤
      Subgroup.centralizer (twoPoint (X := X) (F := F) : Set X)) :
    stabilizer X (0 : F) ⊓ Subgroup.normalizer (twoPoint (X := X) (F := F) : Set X) =
      twoPoint (X := X) (F := F) := by
  apply le_antisymm
  · intro g hg
    refine ⟨hg.1, ?_⟩
    have hf := normalizer_smul_fixed hg.2
      (fun u (hu : u ∈ twoPoint (X := X) (F := F)) => mem_stabilizer_iff.mp hu.2)
    rcases c.fixed_eq_zero_or_one_of_normalizer_not_le le_rfl hNC hf with hz | ho
    · have h0 := mem_stabilizer_iff.mp hg.1
      exact False.elim (one_ne_zero ((MulAction.injective g) (hz.trans h0.symm)))
    · exact ho
  · exact le_inf inf_le_left Subgroup.le_normalizer

/-- The full coefficient centralizer is Γ in the two-fixed-point case. -/
theorem twoPoint_centralizer_eq [Finite F]
    (hNC : ¬ Subgroup.normalizer (twoPoint (X := X) (F := F) : Set X) ≤
      Subgroup.centralizer (twoPoint (X := X) (F := F) : Set X)) :
    Subgroup.centralizer (twoPoint (X := X) (F := F) : Set X) =
      twoPoint (X := X) (F := F) := by
  apply le_antisymm
  · exact (le_inf (c.centralizer_le_stabilizer_of_normalizer_not_le le_rfl hNC)
      (Subgroup.centralizer_le_normalizer _)).trans
      (c.stabilizer_inf_twoPoint_normalizer_eq hNC).le
  · let := c.twoPoint_isCyclic
    intro g hg u hu
    exact congrArg Subtype.val (mul_comm
      (⟨u, hu⟩ : twoPoint (X := X) (F := F)) ⟨g, hg⟩)

/-- The literal coefficient normalizer has twice the coefficient order. -/
theorem card_twoPoint_normalizer [Finite X] [Finite F]
    (hNC : ¬ Subgroup.normalizer (twoPoint (X := X) (F := F) : Set X) ≤
      Subgroup.centralizer (twoPoint (X := X) (F := F) : Set X)) :
    Nat.card (Subgroup.normalizer (twoPoint (X := X) (F := F) : Set X)) =
      2 * Nat.card (twoPoint (X := X) (F := F)) := by
  classical
  let Γ := twoPoint (X := X) (F := F)
  let N := Subgroup.normalizer (Γ : Set X)
  have hstab : stabilizer N (0 : F) = Γ.subgroupOf N := by
    ext g
    change (g : X) • (0 : F) = 0 ↔ (g : X) ∈ Γ
    constructor
    · intro h
      exact (congrArg (fun H : Subgroup X => (g : X) ∈ H)
        (c.stabilizer_inf_twoPoint_normalizer_eq hNC)).mp ⟨h, g.property⟩
    · intro h
      exact mem_stabilizer_iff.mp h.1
  have hstabcard : Nat.card (stabilizer N (0 : F)) = Nat.card Γ := by
    rw [hstab]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.le_normalizer : Γ ≤ N)).toEquiv
  have horbit : Nat.card (orbit N (0 : F)) = 2 := by
    have h0 : (0 : F) ∈ orbit N (0 : F) := mem_orbit_self _
    have h1 : (1 : F) ∈ orbit N (0 : F) := by
      obtain ⟨g, hgN, hgC⟩ := Set.not_subset.mp hNC
      have hg0 : g • (0 : F) ≠ 0 := by
        intro h
        exact hgC (c.stabilizer_inf_normalizer_le_centralizer le_rfl ⟨h, hgN⟩)
      have hf := normalizer_smul_fixed hgN
        (fun u (hu : u ∈ Γ) => mem_stabilizer_iff.mp hu.1)
      have hg1 := (c.fixed_eq_zero_or_one_of_normalizer_not_le le_rfl hNC hf).resolve_left hg0
      exact ⟨⟨g, hgN⟩, hg1⟩
    apply (Nat.card_eq_two_iff' (⟨0, h0⟩ : orbit N (0 : F))).mpr
    refine ⟨⟨1, h1⟩, ?_, ?_⟩
    · exact fun h => one_ne_zero (congrArg Subtype.val h)
    · intro x hx
      apply Subtype.ext
      obtain ⟨g, hg⟩ := x.property
      have hf := normalizer_smul_fixed g.property
        (fun u (hu : u ∈ Γ) => mem_stabilizer_iff.mp hu.1)
      change (g : X) • (0 : F) = (x : F) at hg
      rw [hg] at hf
      have hfix : ∀ u ∈ Γ, u • (x : F) = x := hf
      rcases c.fixed_eq_zero_or_one_of_normalizer_not_le le_rfl hNC hfix with hz | ho
      · exact False.elim (hx (Subtype.ext hz))
      · exact ho
  calc
    Nat.card N = Nat.card (orbit N (0 : F) × stabilizer N (0 : F)) :=
      Nat.card_congr (orbitProdStabilizerEquivGroup N (0 : F)).symm
    _ = 2 * Nat.card Γ := by rw [Nat.card_prod, horbit, hstabcard]

end MulAction.SemilinearPointStabilizer.Coordinates
