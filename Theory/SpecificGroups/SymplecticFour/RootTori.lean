module

public import Theory.SpecificGroups.SymplecticFour.RootSubgroup
public import Theory.SpecificGroups.SymplecticFour.Sylow.Characters
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Regular cyclic tori for the eight symplectic root subgroups

For every standard matrix root subgroup of Sp₄ over a finite field of
characteristic two, an explicit one-dimensional diagonal torus complements
its centralizer in its normalizer. This torus is isomorphic to the field's
multiplicative group and acts regularly on the nonidentity root elements.
For fields of order greater than two its commutator with the root subgroup
is the whole root subgroup.

The four long roots have square weight; the four short roots have unit
weight. Squaring is bijective over a finite characteristic-two field.
Moreover, the affine dependence of a root matrix on its parameter forces
every matrix normalizer to act by a field scalar. Thus the explicit torus
realizes every normalizer action, proving the full centralizer complement
without identifying the normalizer with a parabolic.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the cyclic
complement and regular action used in E.6.11(3c), printed p.250 (PDF p.261).
-/

@[expose] public section

open Matrix Subgroup
open scoped commutatorElement
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.RootTori
variable {F : Type*} [Field F]

/-- Diagonal representatives for roots 0–7 in their original matrix order. -/
noncomputable def element (r : Fin 8) (s : Fˣ) : Sp F :=
  diagonalTorus (![s, s⁻¹, 1, 1, s, s⁻¹, s, s⁻¹] r)
    (![1, 1, s, s⁻¹, 1, 1, 1, 1] r)

/-- The diagonal representatives form a homomorphism from the field units. -/
noncomputable def parameter (r : Fin 8) : Fˣ →* Sp F where
  toFun := element r
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases r <;> rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;> simp [element, diagonalTorus, Matrix.diagonal]
  map_mul' s t := by
    apply Subtype.ext
    change (element r (s * t)).val = (element r s).val * (element r t).val
    simp only [element, diagonalTorus, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases r <;> rcases i with i | i <;> fin_cases i <;> simp [mul_comm]

/-- Long roots have square weight; short roots have unit weight. -/
def weight (r : Fin 8) (s : Fˣ) : Fˣ :=
  if r.val < 4 then s ^ 2 else s

/-- Actual conjugation on the original root matrices has the stated weight. -/
theorem conjugate (r : Fin 8) (s : Fˣ) (t : F) :
    element r s * rootElement r t * (element r s)⁻¹ =
      rootElement r ((weight r s : F) * t) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  ext i j
  change ((element r s).val * (rootElement r t).val) i j =
    ((rootElement r ((weight r s : F) * t)).val * (element r s).val) i j
  fin_cases r <;>
    simp only [element, diagonalTorus, Matrix.diagonal_mul, Matrix.mul_diagonal]
  all_goals dsimp [rootElement, rootMatrix, weight]
  all_goals rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [Matrix.fromBlocks, Matrix.single, pow_two, mul_assoc, mul_comm]

variable [CharP F 2]

/-- In characteristic two the torus weight is faithful for all eight roots. -/
theorem weight_injective (r : Fin 8) : Function.Injective (weight (F := F) r) := by
  intro s t h
  apply Units.ext
  unfold weight at h
  split at h
  · exact CharTwo.sq_injective (congrArg Units.val h)
  · exact congrArg Units.val h

/-- The one-dimensional torus is embedded in the symplectic matrix group. -/
theorem parameter_injective (r : Fin 8) : Function.Injective (parameter (F := F) r) := by
  intro s t h
  apply weight_injective r
  apply Units.ext
  have hc := congrArg (fun g : Sp F => g * rootElement r 1 * g⁻¹) h
  change element r s * rootElement r 1 * (element r s)⁻¹ =
    element r t * rootElement r 1 * (element r t)⁻¹ at hc
  simp only [conjugate, mul_one] at hc
  exact RootSubgroup.element_injective r hc

variable [Finite F]

/-- Over a finite characteristic-two field every nonzero scalar is a weight. -/
theorem weight_surjective (r : Fin 8) : Function.Surjective (weight (F := F) r) :=
  Finite.surjective_of_injective (weight_injective r)

omit [CharP F 2] [Finite F] in
private theorem rootMatrix_affine (r : Fin 8) (s t : F) :
    rootMatrix r (s * t) = (1 - t) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) +
      t • rootMatrix r s := by
  ext i j
  fin_cases r <;> rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.fromBlocks, Matrix.single] <;> ring

omit [CharP F 2] [Finite F] in
/-- The conjugate of the parameter-one element determines conjugation on the entire root. -/
theorem conjugate_of_one (r : Fin 8) (g : Sp F) (c : F)
    (h : g * rootElement r 1 * g⁻¹ = rootElement r c) (t : F) :
    g * rootElement r t * g⁻¹ = rootElement r (c * t) := by
  apply Subtype.ext
  have hm : g.val * rootMatrix r 1 * g⁻¹.val = rootMatrix r c :=
    congrArg Subtype.val h
  have hi : g.val * g⁻¹.val = 1 := congrArg Subtype.val (mul_inv_cancel g)
  change g.val * rootMatrix r t * g⁻¹.val = rootMatrix r (c * t)
  conv_lhs => rw [show t = (1 : F) * t by simp, rootMatrix_affine]
  rw [rootMatrix_affine]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    mul_one, hi, hm]

omit [CharP F 2] [Finite F] in
/-- Every matrix normalizer of a root acts by a nonzero field scalar. -/
theorem normalizer_scalar (r : Fin 8) (g : Sp F)
    (hg : g ∈ normalizer (RootSubgroup.group (F := F) r : Set (Sp F))) :
    ∃ c : Fˣ, ∀ t : F,
      g * rootElement r t * g⁻¹ = rootElement r ((c : F) * t) := by
  have h1 : rootElement r (1 : F) ∈ RootSubgroup.group r :=
    (RootSubgroup.mem_group_iff r _).mpr ⟨1, rfl⟩
  have hh := (Subgroup.mem_normalizer_iff.mp hg (rootElement r 1)).mp h1
  obtain ⟨c, hc⟩ := (RootSubgroup.mem_group_iff r _).mp hh
  have hc0 : c ≠ 0 := by
    intro he
    rw [he, RootSubgroup.element_zero] at hc
    have hh : rootElement r (1 : F) = rootElement r 0 := by
      rw [RootSubgroup.element_zero]
      simpa [mul_assoc] using congrArg (fun x : Sp F => g⁻¹ * x * g) hc.symm
    exact one_ne_zero (RootSubgroup.element_injective r hh)
  exact ⟨Units.mk0 c hc0, fun t => conjugate_of_one r g c hc.symm t⟩

/-- The one-dimensional diagonal torus for the specified matrix root. -/
noncomputable def torus (r : Fin 8) : Subgroup (Sp F) := (parameter r).range

/-- The actual embedded torus is isomorphic to the field units. -/
noncomputable def unitsEquiv (r : Fin 8) : Fˣ ≃* torus (F := F) r :=
  MonoidHom.ofInjective (parameter_injective r)

omit [CharP F 2] [Finite F] in
/-- Each diagonal torus normalizes its specified root subgroup. -/
theorem torus_le_normalizer (r : Fin 8) :
    torus (F := F) r ≤ normalizer (RootSubgroup.group (F := F) r : Set (Sp F)) := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro _ ⟨s, rfl⟩ x hx
  obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff r x).mp hx
  change element r s * rootElement r t * (element r s)⁻¹ ∈ RootSubgroup.group r
  rw [conjugate]
  exact (RootSubgroup.mem_group_iff r _).mpr ⟨_, rfl⟩

/-- The torus realizes every action of the full root normalizer. -/
theorem centralizer_sup_torus (r : Fin 8) :
    centralizer (RootSubgroup.group (F := F) r : Set (Sp F)) ⊔ torus r =
      normalizer (RootSubgroup.group (F := F) r : Set (Sp F)) := by
  apply le_antisymm (sup_le (centralizer_le_normalizer _) (torus_le_normalizer r))
  intro g hg
  obtain ⟨c, hc⟩ := normalizer_scalar r g hg
  obtain ⟨s, hs⟩ := weight_surjective r c
  have he (t : F) :
      g * rootElement r t * g⁻¹ = element r s * rootElement r t * (element r s)⁻¹ := by
    rw [hc, conjugate, hs]
  have hz : (element r s)⁻¹ * g ∈
      centralizer (RootSubgroup.group (F := F) r : Set (Sp F)) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff r x).mp hx
    have h := congrArg (fun z : Sp F => (element r s)⁻¹ * z * g) (he t)
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h.symm
  have hy : element r s ∈ torus r := ⟨s, rfl⟩
  have hh := (centralizer (RootSubgroup.group (F := F) r : Set (Sp F)) ⊔ torus r).mul_mem
    (mem_sup_right hy) (mem_sup_left hz)
  simpa only [mul_inv_cancel_left] using hh

omit [Finite F] in
/-- A torus element centralizing its root is the identity. -/
theorem centralizer_inf_torus (r : Fin 8) :
    centralizer (RootSubgroup.group (F := F) r : Set (Sp F)) ⊓ torus r = ⊥ := by
  apply eq_bot_iff.mpr
  rintro x ⟨hc, s, rfl⟩
  change element r s = 1
  have hh := (mem_centralizer_iff.mp hc) (rootElement r 1)
    ((RootSubgroup.mem_group_iff r _).mpr ⟨1, rfl⟩)
  change rootElement r 1 * element r s = element r s * rootElement r 1 at hh
  have hconj : element r s * rootElement r 1 * (element r s)⁻¹ = rootElement r 1 := by
    rw [← hh]
    simp
  rw [conjugate, mul_one] at hconj
  have hs : weight r s = weight r 1 := by
    apply Units.ext
    simpa [weight] using RootSubgroup.element_injective r hconj
  have h1 := weight_injective r hs
  change parameter r s = 1
  rw [h1, map_one]

/-- There is exactly one torus element conjugating any given nonidentity root element
into another. The equation is in the ambient symplectic matrix group. -/
theorem regular (r : Fin 8) (a b : Sp F)
    (ha : a ∈ RootSubgroup.group r) (hb : b ∈ RootSubgroup.group r)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃! y : torus (F := F) r, (y : Sp F) * a * (y : Sp F)⁻¹ = b := by
  obtain ⟨u, rfl⟩ := (RootSubgroup.mem_group_iff r a).mp ha
  obtain ⟨v, rfl⟩ := (RootSubgroup.mem_group_iff r b).mp hb
  have hu : u ≠ 0 := fun h => ha1 (h ▸ RootSubgroup.element_zero r)
  have hv : v ≠ 0 := fun h => hb1 (h ▸ RootSubgroup.element_zero r)
  obtain ⟨s, hs⟩ := weight_surjective r (Units.mk0 (v / u) (div_ne_zero hv hu))
  refine ⟨⟨element r s, ⟨s, rfl⟩⟩, ?_, ?_⟩
  · change element r s * rootElement r u * (element r s)⁻¹ = rootElement r v
    rw [conjugate, hs]
    simp [hu]
  · rintro ⟨y, t, rfl⟩ ht
    apply Subtype.ext
    change parameter r t = parameter r s
    congr 1
    apply weight_injective r
    apply Units.ext
    have hh : (weight r t : F) * u = v := by
      apply RootSubgroup.element_injective r
      simpa only [parameter, MonoidHom.coe_mk, OneHom.coe_mk, conjugate] using ht
    rw [hs]
    change (weight r t : F) = v / u
    exact (eq_div_iff hu).mpr hh

/-- A root torus over a field of order 2ⁿ is cyclic of order 2ⁿ − 1. -/
noncomputable def cyclicEquiv (r : Fin 8) {n : ℕ} (hcard : Nat.card F = 2 ^ n) :
    torus (F := F) r ≃* Multiplicative (ZMod (2 ^ n - 1)) :=
  (unitsEquiv r).symm.trans (mulEquivOfCyclicCardEq (by
    change Nat.card Fˣ = Nat.card (ZMod (2 ^ n - 1))
    rw [Nat.card_units, hcard, Nat.card_zmod]))

omit [CharP F 2] [Finite F] in
private theorem root_inv (r : Fin 8) (t : F) :
    (rootElement r t)⁻¹ = rootElement r (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [RootSubgroup.element_add, add_neg_cancel, RootSubgroup.element_zero]

omit [CharP F 2] [Finite F] in
private theorem torus_commutator (r : Fin 8) (s : Fˣ) (t : F) :
    ⁅element r s, rootElement r t⁆ = rootElement r (((weight r s : F) - 1) * t) := by
  rw [commutatorElement_def, conjugate, root_inv, RootSubgroup.element_add]
  congr 1
  ring

/-- A nontrivial scalar displacement generates every parameter in the root. -/
theorem commutator_eq (r : Fin 8) (hcard : 2 < Nat.card F) :
    ⁅RootSubgroup.group (F := F) r, torus (F := F) r⁆ = RootSubgroup.group (F := F) r := by
  apply le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp (torus_le_normalizer r))
  have hc : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Fˣ := (Finite.one_lt_card_iff_nontrivial).mp hc
  obtain ⟨s, hs⟩ := exists_ne (1 : Fˣ)
  have hw : (weight r s : F) ≠ 1 := by
    intro hh
    apply hs
    apply weight_injective r
    apply Units.ext
    simpa [weight] using hh
  intro x hx
  obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff r x).mp hx
  rw [Subgroup.commutator_comm]
  have hh := Subgroup.commutator_mem_commutator
    (show element r s ∈ torus r from ⟨s, rfl⟩)
    ((RootSubgroup.mem_group_iff r _).mpr ⟨t / ((weight r s : F) - 1), rfl⟩)
  rw [torus_commutator, mul_div_cancel₀ _ (sub_ne_zero.mpr hw)] at hh
  exact hh

/-- The intrinsic cyclic-complement and regular-conjugation conclusions for every
one of the eight original symplectic root families. -/
theorem exists_regular_cyclic_complement {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 < n) (r : Fin 8) :
    ∃ Y : Subgroup (Sp F),
      Y ≤ normalizer (RootSubgroup.group (F := F) r : Set (Sp F)) ∧
      Nonempty (Y ≃* Multiplicative (ZMod (2 ^ n - 1))) ∧
      centralizer (RootSubgroup.group (F := F) r : Set (Sp F)) ⊔ Y =
        normalizer (RootSubgroup.group (F := F) r : Set (Sp F)) ∧
      centralizer (RootSubgroup.group (F := F) r : Set (Sp F)) ⊓ Y = ⊥ ∧
      ⁅RootSubgroup.group (F := F) r, Y⁆ = RootSubgroup.group (F := F) r ∧
      ∀ a ∈ RootSubgroup.group (F := F) r, a ≠ 1 →
        ∀ b ∈ RootSubgroup.group (F := F) r, b ≠ 1 →
          ∃! y : Y, (y : Sp F) * a * (y : Sp F)⁻¹ = b := by
  have hF : 2 < Nat.card F := by
    rw [hcard]
    have hh : 2 ^ 1 < 2 ^ n := Nat.pow_lt_pow_right (by decide) hn
    simpa using hh
  exact ⟨torus r, torus_le_normalizer r, ⟨cyclicEquiv r hcard⟩,
    centralizer_sup_torus r, centralizer_inf_torus r, commutator_eq r hF,
    fun a ha ha1 b hb hb1 => regular r a b ha hb ha1 hb1⟩

end Theory.SpecificGroups.SymplecticFour.RootTori
