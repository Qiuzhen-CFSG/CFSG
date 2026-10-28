module
public import Theory.GroupAction.SymplecticRankThree.PolarityDesign
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Higman's condition (i) and full line sizes

For a faithful incidence action on a polarity design, evaluation embeds the
pointwise block kernel in any punctured hyperbolic line. Semiregularity is
proved in `PolarityDesign`, and the line bound is q+1. Thus a kernel of order
at least q has order exactly q and forces that line to have q+1 points.
Transitivity propagates the conclusion from one pole to all hyperbolic lines;
the singular-line argument then gives the same size for every line.

The explicit binary specialization uses q=2 directly throughout. These are
Higman's geometric steps before the Dembowski–Wagner reconstruction and
projective coordinatization, not a symplectic recognition theorem.

Source: D. G. Higman, *Finite permutation groups of rank 3*, Math. Z. 86
(1964), §7(vii)–(viii), Lemma 10 and Theorem 2(i), printed pp.152–154.
-/

public noncomputable section
namespace Theory.GroupAction.SymplecticRankThree.PolarityDesign
open MulAction
variable {Ω G : Type*} [Finite Ω] [Group G] [MulAction G Ω] [FaithfulSMul G Ω]
variable {q : ℕ} (D : PolarityDesign Ω q)
variable (hact : ∀ (g : G) x y, D.incident (g • x) (g • y) ↔ D.incident x y)

include hact

/-- The pointwise block kernel is semiregular outside that block. -/
theorem kernel_fixed_eq_one (hq : 2 ≤ q) {a b : Ω}
    (hab : ¬ D.incident a b) (g : fixingSubgroup G (D.block a))
    (hg : (g : G) • b = b) : g = 1 := by
  have he := D.eq_refl_of_fixes_block_and_point hq (MulAction.toPerm (g : G))
    (hact g) ((mem_fixingSubgroup_iff G).mp g.property) hab hg
  apply Subtype.ext
  change (g : G) = 1
  apply eq_of_smul_eq_smul (α := Ω)
  intro x
  have hx := Equiv.congr_fun he x
  simpa only [MulAction.toPerm_apply, Equiv.refl_apply, one_smul] using hx

/-- Evaluating the entire block kernel at an outside point is injective. -/
theorem kernel_eval_injective (hq : 2 ≤ q) {a b : Ω} (hab : ¬ D.incident a b) :
    Function.Injective (fun g : fixingSubgroup G (D.block a) => (g : G) • b) := by
  intro g h he
  change (g : G) • b = (h : G) • b at he
  have hg : ((g⁻¹*h : fixingSubgroup G (D.block a)) : G) • b = b := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul]
    rw [← he, inv_smul_smul]
  exact inv_mul_eq_one.mp (D.kernel_fixed_eq_one hact hq hab (g⁻¹*h) hg)

/-- Evaluation lands in the punctured hyperbolic line through the pole. -/
def kernelLineMap {a b : Ω} (hab : ¬ D.incident a b) :
    fixingSubgroup G (D.block a) → ↥(D.line a b \ {a}) := fun g =>
  ⟨(g : G) • b, D.map_mem_line_of_fixes_block (MulAction.toPerm (g : G))
    (hact g) ((mem_fixingSubgroup_iff G).mp g.property) b, by
      have hga : (g : G) • a = a := ((mem_fixingSubgroup_iff G).mp g.property) a (D.refl a)
      intro h
      have hba : b = a := (MulAction.injective (g : G)) (h.trans hga.symm)
      exact hab (hba.symm ▸ D.refl a)⟩

/-- The kernel order is bounded by one less than the hyperbolic line size. -/
theorem kernel_card_le_line (hq : 2 ≤ q) {a b : Ω} (hab : ¬ D.incident a b) :
    Nat.card (fixingSubgroup G (D.block a)) ≤ (D.line a b).ncard - 1 := by
  have hi : Function.Injective (D.kernelLineMap hact hab) :=
    fun g h he => D.kernel_eval_injective hact hq hab (congrArg Subtype.val he)
  have hh := Nat.card_le_card_of_injective _ hi
  change Nat.card (fixingSubgroup G (D.block a)) ≤ (D.line a b \ {a}).ncard at hh
  simpa only [Set.ncard_sdiff_singleton_of_mem (D.left_mem_line a b)] using hh

/-- Higman's condition (i) forces the full hyperbolic line, including q=2. -/
theorem hyperbolic_line_card_of_kernel (hq : 2 ≤ q) {a b : Ω}
    (hab : ¬ D.incident a b) (hk : q ≤ Nat.card (fixingSubgroup G (D.block a))) :
    (D.line a b).ncard = q+1 := by
  have hne : a ≠ b := fun h => hab (h ▸ D.refl a)
  have hu := D.line_card_le (by omega) hne
  have hl := D.kernel_card_le_line hact hq hab
  omega

/-- Condition (i) also determines the entire block kernel order. -/
theorem kernel_card_eq (hq : 2 ≤ q) {a b : Ω}
    (hab : ¬ D.incident a b) (hk : q ≤ Nat.card (fixingSubgroup G (D.block a))) :
    Nat.card (fixingSubgroup G (D.block a)) = q := by
  have hh := D.kernel_card_le_line hact hq hab
  rw [D.hyperbolic_line_card_of_kernel hact hq hab hk] at hh
  omega

/-- A kernel lower bound at one point suffices for every line in a transitive action. -/
theorem all_lines_card_of_kernel [IsPretransitive G Ω] (hq : 2 ≤ q) (a : Ω)
    (hk : q ≤ Nat.card (fixingSubgroup G (D.block a))) :
    ∀ x y, x ≠ y → (D.line x y).ncard = q+1 := by
  apply D.all_lines_card
  intro x y hxy
  obtain ⟨g, hg⟩ := exists_smul_eq G a x
  have hz : ¬ D.incident a (g⁻¹ • y) := by
    intro h
    have hh := (hact g a (g⁻¹ • y)).mpr h
    rw [hg, smul_inv_smul] at hh
    exact hxy hh
  have hline := D.line_card_map (MulAction.toPerm g) (hact g) a (g⁻¹ • y)
  change (D.line (g • a) (g • (g⁻¹ • y))).ncard = _ at hline
  rw [hg, smul_inv_smul, D.hyperbolic_line_card_of_kernel hact hq hz hk] at hline
  exact hline

omit hact in
/-- The q=2 extension of the line-size argument, without invoking the printed
q>2 theorem: blocks have seven points, intersections and all lines have three. -/
theorem binary_all_lines_card {D : PolarityDesign Ω 2}
    (hact : ∀ (g : G) x y, D.incident (g • x) (g • y) ↔ D.incident x y)
    [IsPretransitive G Ω] (a : Ω)
    (hk : 2 ≤ Nat.card (fixingSubgroup G (D.block a))) :
    ∀ x y, x ≠ y → (D.line x y).ncard = 3 :=
  D.all_lines_card_of_kernel hact (by decide) a hk

end Theory.GroupAction.SymplecticRankThree.PolarityDesign
