module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.LinearBudget
public import Theory.GroupAction.HyperplaneCommutatorGeneration
public import Theory.Representation.BinaryGroupAction
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDecomposition.Rigidity

/-!
# Invariant lines and their centralizer complements

Hyperplane-centralizer generation and the source hyperplane bound show that
all actual invariant order-three lines generate the elementary core. Distinct
lines with binary plane supports fix each other's supports, by small-support
rigidity. Coprime fixed/moved splitting gives independence of the supports;
faithfulness gives independence of the lines. Each chosen line splits off
with its literal pointwise centralizer on the support as complement.

Source: Aschbacher--Smith, D.2.14(3),(7)(ii), printed p.187. The small-support
rigidity input is D.2.12, printed pp.183--184.
-/

public section

open Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The actual invariant order-three lines generate the original core. -/
theorem Reduced.invariant_lines_generate {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) :
    (⨆ Z : {Z : Subgroup G // IsInvariantLine P A Z}, Z.val) = P := by
  let : IsElementaryAbelian 2 A := h.starred.1.2.1.2
  let : IsElementaryAbelian 3 P := h.elementary
  let : P.Normal := h.normal
  have hn : A ≤ Subgroup.normalizer (P : Set G) := by rw [Subgroup.normalizer_eq_top]; exact le_top
  apply le_antisymm (iSup_le fun Z => Z.property.1)
  conv_lhs => rw [← h.core_commutator, ← Subgroup.iSup_hyperplane_centralizer_commutator
    (by decide : 3 ≠ 2) P A (IsElementaryAbelian.isPGroup 3 P) hn]
  apply iSup₂_le
  intro B hB
  let D := P ⊓ Subgroup.centralizer (B.map A.subtype : Set G)
  have hBA : B.map A.subtype ≤ A := Subgroup.map_subtype_le B
  have hnD : A ≤ Subgroup.normalizer (D : Set G) := by
    apply (le_inf hn ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    apply (le_trans ?_ (Subgroup.centralizer_le_normalizer (B.map A.subtype : Set G))).trans
      (Subgroup.normalizer_le_normalizer_centralizer _)
    exact (Subgroup.le_centralizer A).trans (Subgroup.centralizer_le hBA)
  have hcom : ⁅D, A⁆ ≤ D := Subgroup.le_normalizer_iff_commutator_le_left.mp hnD
  by_cases hd : D = ⊥
  · exact hcom.trans (hd.le.trans bot_le)
  have hc : Nat.card (B.map A.subtype) = 2 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    have hh := B.card_mul_index
    rw [hB, h.card_actor] at hh
    omega
  have hr : rank (B.map A.subtype) = 1 := by simp only [rank, hc]; decide
  have hD3 : Nat.card D = 3 := (h.hyperplane_support _ hBA hr hd).1
  exact hcom.trans (le_iSup_of_le ⟨D, inf_le_left, hD3, hnD⟩ le_rfl)

variable [FiniteDimensional (ZMod 2) V]

/-- Distinct invariant support planes are fixed by each other's lines. -/
theorem Reduced.invariant_lines_cross_fixed {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hsmall : SmallInvariantSupports ρ P A)
    {X Y : Subgroup G} (hX : IsInvariantLine P A X) (hY : IsInvariantLine P A Y)
    (hne : X ≠ Y) : subspaceCommutator ρ ⊤ Y ≤ fixedSpace ρ X := by
  let := Representation.BinaryGroupAction.action ρ
  let : IsElementaryAbelian 2 (Multiplicative V) := Representation.BinaryGroupAction.elementary
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : FaithfulSMul G (Multiplicative V) := Representation.BinaryGroupAction.faithful ρ h.faithful
  let : IsElementaryAbelian 3 P := h.elementary
  have hPF : P ≤ fittingSubgroup G :=
    le_sSup ⟨h.normal, (IsElementaryAbelian.isPGroup 3 P).isNilpotent⟩
  have hmem (Z : Subgroup G) (hZ : IsInvariantLine P A Z) :
      Z ∈ smallSupportFactors G (Multiplicative V) 1 := by
    refine ⟨hZ.1.trans hPF, hZ.2.1, ?_⟩
    rw [Representation.BinaryGroupAction.commutator_card, hsmall Z hZ]
  have hh := smallSupportFactors_cross_fixed_of_commuting (V := Multiplicative V)
    (Or.inl rfl : 1 = 1 ∨ 1 = 2) (hmem X hX) (hmem Y hY) hne
    (hX.1.trans ((Subgroup.le_centralizer P).trans (Subgroup.centralizer_le hY.1)))
  rw [Representation.BinaryGroupAction.commutator_eq,
    Representation.BinaryGroupAction.fixedPoints_eq] at hh
  exact (Representation.BinaryGroupAction.submoduleEquivSubgroup (V := V)).le_iff_le.mp hh

/-- Coprime splitting separates each support from the sum of all the others. -/
theorem Reduced.invariant_supports_independent {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hsmall : SmallInvariantSupports ρ P A) :
    iSupIndep (fun Z : {Z : Subgroup G // IsInvariantLine P A Z} =>
      subspaceCommutator ρ ⊤ Z.val) := by
  rw [iSupIndep_def]
  intro Z
  apply (odd_fixed_moved_complement ρ (Z.property.2.1 ▸ (by decide : Odd 3))).disjoint.mono_right
  exact iSup_le fun Y => iSup_le fun hne =>
    h.invariant_lines_cross_fixed ρ hsmall Z.property Y.property
      (fun he => hne (Subtype.ext he.symm))

omit [FiniteDimensional (ZMod 2) V] in
private theorem line_support_faithful {Z : Subgroup G}
    (hf : Function.Injective ρ) (hZ : Nat.card Z = 3)
    {z : G} (hz : z ∈ Z)
    (hfix : ∀ v ∈ subspaceCommutator ρ ⊤ Z, ρ z v = v) : z = 1 := by
  apply hf
  ext v
  have hc := odd_fixed_moved_complement ρ (hZ ▸ (by decide : Odd 3))
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp
    (hc.sup_eq_top ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) V)))
  have hwf : ρ z w = w := hw ⟨z, hz⟩
  simp only [map_add, hfix u hu, hwf, map_one, Module.End.one_apply]

/-- Faithfulness on each support makes the original core lines independent. -/
theorem Reduced.invariant_lines_independent {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hsmall : SmallInvariantSupports ρ P A) :
    iSupIndep (fun Z : {Z : Subgroup G // IsInvariantLine P A Z} => Z.val) := by
  rw [iSupIndep_def]
  intro Z
  apply Subgroup.disjoint_def.mpr
  intro z hz hrest
  apply line_support_faithful ρ h.faithful Z.property.2.1 hz
  have hle : (⨆ Y : {Y : Subgroup G // IsInvariantLine P A Y}, ⨆ (_ : Y ≠ Z), Y.val) ≤
      subspaceKernel ρ (subspaceCommutator ρ ⊤ Z.val) ⊤ := by
    apply iSup_le
    intro Y
    apply iSup_le
    intro hne y hy
    refine ⟨Subgroup.mem_top _, ?_⟩
    intro v hv
    exact h.invariant_lines_cross_fixed ρ hsmall Y.property Z.property
      (fun he => hne (Subtype.ext he)) hv ⟨y, hy⟩
  exact (hle hrest).2

omit [FiniteDimensional (ZMod 2) V] in
/-- All the literal supports span the original moved module. -/
theorem Reduced.invariant_supports_generate {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) :
    (⨆ Z : {Z : Subgroup G // IsInvariantLine P A Z}, subspaceCommutator ρ ⊤ Z.val) = ⊤ := by
  rw [← Representation.BinaryGroupAction.moved_iSup, h.invariant_lines_generate ρ, h.moved]

/-- The source centralizer complement splits off any chosen invariant plane.
The kernel is the literal pointwise centralizer of that plane inside `P`. -/
theorem Reduced.invariant_line_centralizer_complement {P A Z : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hsmall : SmallInvariantSupports ρ P A)
    (hZ : IsInvariantLine P A Z) :
    Z ⊔ subspaceKernel ρ (subspaceCommutator ρ ⊤ Z) P = P ∧
      Disjoint Z (subspaceKernel ρ (subspaceCommutator ρ ⊤ Z) P) := by
  constructor
  · apply le_antisymm (sup_le hZ.1 (subspaceKernel_le ρ _ P))
    conv_lhs => rw [← h.invariant_lines_generate ρ]
    apply iSup_le
    intro Y
    by_cases he : Y.val = Z
    · exact he ▸ le_sup_left
    · apply le_trans ?_ le_sup_right
      intro y hy
      refine ⟨Y.property.1 hy, ?_⟩
      intro v hv
      exact h.invariant_lines_cross_fixed ρ hsmall Y.property hZ he hv ⟨y, hy⟩
  · apply Subgroup.disjoint_def.mpr
    intro z hz hk
    exact line_support_faithful ρ h.faithful hZ.2.1 hz hk.2

omit [FiniteDimensional (ZMod 2) V] in
/-- The centralizer complement is faithful on the complementary fixed space. -/
theorem Reduced.invariant_line_complement_faithful {P A Z : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hZ : IsInvariantLine P A Z) :
    subspaceKernel ρ (fixedSpace ρ Z)
      (subspaceKernel ρ (subspaceCommutator ρ ⊤ Z) P) = ⊥ := by
  apply bot_unique
  intro x hx
  apply h.faithful
  ext v
  have hc := odd_fixed_moved_complement ρ (hZ.2.1 ▸ (by decide : Odd 3))
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp
    (hc.sup_eq_top ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) V)))
  simp only [map_add, hx.1.2 u hu, hx.2 w hw, map_one, Module.End.one_apply]

/-- Splitting off a second invariant plane inside the first centralizer
complement uses the intersection of the two literal pointwise centralizers. -/
theorem Reduced.successive_centralizer_complement {P A X Y : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hsmall : SmallInvariantSupports ρ P A)
    (hX : IsInvariantLine P A X) (hY : IsInvariantLine P A Y) (hne : X ≠ Y) :
    let R := subspaceKernel ρ (subspaceCommutator ρ ⊤ X) P
    let S := subspaceKernel ρ (subspaceCommutator ρ ⊤ Y) P
    Y ≤ R ∧ Y ⊔ (R ⊓ S) = R ∧ Disjoint Y (R ⊓ S) := by
  dsimp only
  let R := subspaceKernel ρ (subspaceCommutator ρ ⊤ X) P
  let S := subspaceKernel ρ (subspaceCommutator ρ ⊤ Y) P
  have hYR : Y ≤ R := by
    intro y hy
    exact ⟨hY.1 hy, fun v hv =>
      h.invariant_lines_cross_fixed ρ hsmall hY hX hne.symm hv ⟨y, hy⟩⟩
  have hsplit := h.invariant_line_centralizer_complement ρ hsmall hY
  let : IsElementaryAbelian 3 P := h.elementary
  have hn : S ≤ Subgroup.normalizer (Y : Set G) :=
    ((subspaceKernel_le ρ _ P).trans ((Subgroup.le_centralizer P).trans
      (Subgroup.centralizer_le hY.1))).trans (Subgroup.centralizer_le_normalizer _)
  refine ⟨hYR, le_antisymm (sup_le hYR inf_le_left) ?_, hsplit.2.mono_right inf_le_right⟩
  intro r hr
  have hprod : r ∈ (Y : Set G) * (S : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y S hn]
    rw [hsplit.1]
    exact (subspaceKernel_le ρ _ P) hr
  obtain ⟨y, hy, t, ht, rfl⟩ := hprod
  have htR : t ∈ R := by
    have hh := R.mul_mem (R.inv_mem (hYR hy)) hr
    simpa only [inv_mul_cancel_left] using hh
  exact (Y ⊔ (R ⊓ S)).mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right ⟨htR, ht⟩)

end CFSG.Quasithin.ChapterD.FittingConfigurations
