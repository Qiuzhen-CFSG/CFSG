module

public import Theory.Representation.FirstCohomologySymplecticFour.Quadratic
public import Theory.Representation.FirstCohomologySymplecticFour.RootCocycle
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Cocycle normal form for the natural symplectic four-space over larger fields

Over a finite characteristic-two field with more than two elements, every
cocycle for the natural action of `Sp₄(K)'` is a scalar multiple of the
quadratic-defect cocycle plus a principal cocycle.

First, a nonidentity unit supplies a diagonal conjugating element for each
root family. Its weight is either the unit or its square, both different from
one in characteristic two. The resulting commutator formula puts every root
element in the derived subgroup; elementary generation proves `Sp₄(K)' = Sp₄(K)`.

The subgroup on which the difference of two cocycles vanishes extends the
normal form from the eight root families to the full matrix group. The proved
perfectness then transports this normal form to the actual derived action.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(5), printed p.408 (PDF p.419), citing Jones--Parshall (1976).
This is the larger-field spanning calculation; the binary case and the
conversion to the source's binary dimension belong to the assembly consumers.
-/

open Matrix
open scoped commutatorElement
namespace Representation.OneCohomology.SymplecticFour.LargeField

variable {K : Type*} [Field K] [CharP K 2]
local notation "G" => Matrix.symplecticGroup (Fin 2) K

private def torus (u v : Kˣ) : G :=
  ⟨Matrix.diagonal (Sum.elim ![(u : K), (v : K)] ![(↑u⁻¹ : K), (↑v⁻¹ : K)]), by
    rw [SymplecticGroup.mem_iff]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.J, Matrix.fromBlocks, Matrix.diagonal,
        CharTwo.neg_eq]⟩

private def rootTorus (r : Fin 8) (s : Kˣ) : G :=
  torus (![s, s⁻¹, 1, 1, s, s⁻¹, s, s⁻¹] r) (![1, 1, s, s⁻¹, 1, 1, 1, 1] r)

private def weight (r : Fin 8) (s : Kˣ) : K :=
  if r.val < 4 then (s : K) ^ 2 else (s : K)

private lemma torus_root (r : Fin 8) (s : Kˣ) (t : K) :
    rootTorus r s * rootElement r t =
      rootElement r (weight r s * t) * rootTorus r s := by
  apply Subtype.ext
  ext i j
  change ((rootTorus r s).val * (rootElement r t).val) i j =
    ((rootElement r (weight r s * t)).val * (rootTorus r s).val) i j
  fin_cases r <;>
    simp only [rootTorus, torus, Matrix.diagonal_mul, Matrix.mul_diagonal]
  all_goals dsimp [rootElement, rootMatrix, weight]
  all_goals rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [Matrix.fromBlocks, Matrix.single, pow_two, mul_assoc, mul_comm]

omit [CharP K 2] in
private lemma root_add (r : Fin 8) (s t : K) :
    rootElement r s * rootElement r t = rootElement r (s + t) := by
  apply Subtype.ext
  change rootMatrix r s * rootMatrix r t = rootMatrix r (s + t)
  fin_cases r <;>
    simp [rootMatrix, Matrix.fromBlocks_multiply, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.single_add] <;> abel_nf <;> simp

omit [CharP K 2] in
private lemma root_zero (r : Fin 8) : rootElement r (0 : K) = 1 := by
  apply Subtype.ext
  fin_cases r <;> simp [rootElement, rootMatrix, Matrix.single_zero]

omit [CharP K 2] in
private lemma root_inv (r : Fin 8) (t : K) :
    (rootElement r t)⁻¹ = rootElement r (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [root_add, add_neg_cancel, root_zero]

private lemma torus_commutator (r : Fin 8) (s : Kˣ) (t : K) :
    ⁅rootTorus r s, rootElement r t⁆ = rootElement r ((weight r s - 1) * t) := by
  simp only [commutatorElement_def, torus_root, mul_assoc, mul_inv_cancel_left,
    root_inv, root_add]
  congr 1
  ring

private lemma weight_ne_one (r : Fin 8) (s : Kˣ) (hs : (s : K) ≠ 1) :
    weight r s ≠ 1 := by
  unfold weight
  split
  · intro h
    apply hs
    exact CharTwo.sq_injective (by simpa using h)
  · exact hs

variable [Finite K]

omit [CharP K 2] in
private lemma exists_nontrivial_unit (hcard : 2 < Nat.card K) :
    ∃ s : Kˣ, (s : K) ≠ 1 := by
  classical
  let := Fintype.ofFinite K
  have hc : 2 < Fintype.card K := by simpa only [Nat.card_eq_fintype_card] using hcard
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp hc
  have hex : ∃ x : K, x ≠ 0 ∧ x ≠ 1 := by
    by_contra! h
    have hx := h x
    have hy := h y
    have hz := h z
    by_cases hx0 : x = 0 <;> by_cases hy0 : y = 0 <;> by_cases hz0 : z = 0 <;> simp_all
  obtain ⟨s, hs0, hs1⟩ := hex
  exact ⟨Units.mk0 s hs0, hs1⟩

/-- The symplectic four-dimensional matrix group is perfect over a finite
characteristic-two field with more than two elements. -/
public theorem commutator_eq_top (hcard : 2 < Nat.card K) : commutator G = ⊤ := by
  obtain ⟨s, hs⟩ := exists_nontrivial_unit (K := K) hcard
  apply eq_top_of_rootElement_mem
  intro r t
  have hm : ⁅rootTorus r s, rootElement r (t / (weight r s - 1))⁆ ∈ commutator G := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [torus_commutator, mul_div_cancel₀ _ (sub_ne_zero.mpr (weight_ne_one r s hs))] at hm
  exact hm

omit [CharP K 2] [Finite K] in
private lemma eq_of_root_values (f q : cocycles (symplecticNatural (k := K) 2))
    (hv : ∀ r t, f.val (rootElement r t) = q.val (rootElement r t)) : f = q := by
  let d := f - q
  have h1 : d.val 1 = 0 := by
    have h := d.property 1 1
    simpa using h.symm
  let H : Subgroup G :=
    { carrier := {g | d.val g = 0}
      one_mem' := h1
      mul_mem' := by
        intro g h hg hh
        change d.val (g * h) = 0
        rw [d.property, hg, hh, map_zero, add_zero]
      inv_mem' := by
        intro g hg
        change d.val g = 0 at hg
        change d.val g⁻¹ = 0
        have h := d.property g⁻¹ g
        simpa only [inv_mul_cancel, h1, hg, map_zero, zero_add] using h.symm }
  have ht : H = ⊤ := eq_top_of_rootElement_mem H (by
    intro r t
    change f.val (rootElement r t) - q.val (rootElement r t) = 0
    exact sub_eq_zero.mpr (hv r t))
  apply sub_eq_zero.mp
  apply Subtype.ext
  funext g
  have hg : g ∈ H := by rw [ht]; exact Subgroup.mem_top g
  exact hg

/-- The root normal form extends to every element of the full symplectic group. -/
public theorem exists_natural_normal_form (hcard : 2 < Nat.card K)
    (f : cocycles (symplecticNatural (k := K) 2)) :
    ∃ (t : K) (v : (Fin 2 ⊕ Fin 2) → K),
      f = t • quadraticCocycle + principal (symplecticNatural 2) v := by
  obtain ⟨t, v, hv⟩ := exists_root_normal_form hcard f
  exact ⟨t, v, eq_of_root_values f _ hv⟩

/-- Every cocycle for the natural derived symplectic four-space is a scalar
multiple of the quadratic-defect cocycle modulo a principal cocycle, when
there are more than two field elements. -/
public theorem exists_normal_form (hcard : 2 < Nat.card K)
    (f : cocycles (symplecticDerivedNatural (k := K) 2)) :
    ∃ (t : K) (v : (Fin 2 ⊕ Fin 2) → K),
      f = t • derivedQuadraticCocycle + principal (symplecticDerivedNatural 2) v := by
  have hall (g : G) : g ∈ commutator G := by
    rw [commutator_eq_top hcard]
    exact Subgroup.mem_top g
  let f' : cocycles (symplecticNatural (k := K) 2) :=
    ⟨fun g => f.val ⟨g, hall g⟩, fun g h => f.property ⟨g, hall g⟩ ⟨h, hall h⟩⟩
  obtain ⟨t, v, hv⟩ := exists_natural_normal_form hcard f'
  refine ⟨t, v, Subtype.ext ?_⟩
  funext g
  exact congrArg (fun q : cocycles (symplecticNatural (k := K) 2) => q.val g.val) hv

end Representation.OneCohomology.SymplecticFour.LargeField
