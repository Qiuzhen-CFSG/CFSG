module

public import Theory.Representation.BinaryPermutationAlternatingActions
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Sylow

/-!
# Even augmentation for point-stabilizer Sylows in A₈

The stabilizer of a weight-two word contains an involution interchanging
four disjoint coordinate pairs. Every full vector fixed by that involution
has even augmentation. Conjugate its cyclic two-subgroup into any supplied
Sylow of the point stabilizer and use permutation invariance of augmentation.
This proves the fixed-space assertion without an order computation or a
claim that the point stabilizer's Sylow is Sylow in A₈.

Source: Aschbacher--Smith, 12.2.16, printed p.800; the corrected
point-fixed cocycle argument uses the full permutation module of B.3.1.
-/

@[expose] public section
open Subgroup Representation
namespace BinaryPermutation.EightPointSylow
abbrev Ω := Fin 8
abbrev A8 := alternatingGroup Ω
abbrev S8 := Equiv.Perm Ω

def stabilizer (v : Full Ω) : Subgroup A8 where
  carrier := {g | alternatingRepresentation Ω g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change (alternatingRepresentation Ω a * alternatingRepresentation Ω b) v = v
    rw [Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    change alternatingRepresentation Ω a⁻¹ v = v
    have hh := congrArg (alternatingRepresentation Ω a⁻¹) ha
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using hh.symm

private def pair (i j : Ω) : Full Ω := Pi.single i 1 + Pi.single j 1
private def transport (i j : Ω) : S8 := Equiv.swap 0 i * Equiv.swap 1 (Equiv.swap 0 i j)
private def switches : S8 := Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7

private theorem transport_pair : ∀ i j : Ω, i ≠ j →
    representation Ω (transport i j) (pair 0 1) = pair i j := by
  decide +kernel

private theorem switches_even : switches ∈ alternatingGroup Ω := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private theorem switches_square : switches ^ 2 = 1 := by decide +kernel
private theorem switches_pair : representation Ω switches (pair 0 1) = pair 0 1 := by
  decide +kernel

private theorem switches_fixed_le_core (w : Full Ω)
    (hw : representation Ω switches w = w) : w ∈ core Ω := by
  have h01 := congrFun hw 0
  have h23 := congrFun hw 2
  have h45 := congrFun hw 4
  have h67 := congrFun hw 6
  change w 1 = w 0 at h01
  change w 3 = w 2 at h23
  change w 5 = w 4 at h45
  change w 7 = w 6 at h67
  rw [mem_core]
  simp only [Fin.sum_univ_succ]
  change w 0 + (w 1 + (w 2 + (w 3 + (w 4 + (w 5 + (w 6 + (w 7 + 0))))))) = 0
  rw [h01, h23, h45, h67]
  simp only [CharTwo.add_self_eq_zero, add_zero]

private theorem pair_of_weight_two (v : Full Ω)
    (hw : (Finset.univ.filter fun i => v i ≠ 0).card = 2) :
    ∃ i j : Ω, i ≠ j ∧ v = pair i j := by
  obtain ⟨i,j,hij,he⟩ := Finset.card_eq_two.mp hw
  refine ⟨i,j,hij,?_⟩
  have hc (k : Ω) : v k ≠ 0 ↔ k = i ∨ k = j := by
    have hh := congrArg (fun s : Finset Ω => k ∈ s) he
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton] using Iff.of_eq hh
  funext k
  have hb : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  by_cases hi : k = i
  · subst k
    simpa [pair,hij] using hb (v i) ((hc i).mpr (Or.inl rfl))
  by_cases hj : k = j
  · subst k
    simpa [pair,hij.symm] using hb (v j) ((hc j).mpr (Or.inr rfl))
  · have hz : v k = 0 := Classical.not_not.mp (fun hn => (hc k).mp hn |>.elim hi hj)
    simp [pair, hi, hj, hz]

private theorem inv_action (g : S8) (w : Full Ω) :
    representation Ω g⁻¹ (representation Ω g w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private theorem conjugate_fixed (g a : S8) (w : Full Ω)
    (hw : representation Ω (g * a * g⁻¹) w = w) :
    representation Ω a (representation Ω g⁻¹ w) = representation Ω g⁻¹ w := by
  have hh := congrArg (representation Ω g⁻¹) hw
  simpa only [map_mul, Module.End.mul_apply, inv_action] using hh

/-- A weight-two stabilizer contains an involution whose full fixed vectors are even. -/
theorem exists_even_fixed_involution (v : Full Ω)
    (hw : (Finset.univ.filter fun i => v i ≠ 0).card = 2) :
    ∃ a : stabilizer v, a ^ 2 = 1 ∧
      ∀ w : Full Ω, alternatingRepresentation Ω a.val w = w → w ∈ core Ω := by
  obtain ⟨i,j,hij,rfl⟩ := pair_of_weight_two v hw
  let g := transport i j
  let a : A8 := ⟨g * switches * g⁻¹,
    (inferInstance : (alternatingGroup Ω).Normal).conj_mem switches switches_even g⟩
  have ha : a ∈ stabilizer (pair i j) := by
    change representation Ω (g * switches * g⁻¹) (pair i j) = pair i j
    rw [← transport_pair i j hij]
    change representation Ω (g * switches * g⁻¹) (representation Ω g (pair 0 1)) = _
    simp only [map_mul, Module.End.mul_apply, inv_action, switches_pair]
    rfl
  refine ⟨⟨a, ha⟩, ?_, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    change (g * switches * g⁻¹) ^ 2 = 1
    rw [← MulAut.conj_apply, ← map_pow, switches_square, map_one]
  · intro w hw
    have hh := switches_fixed_le_core _ (conjugate_fixed g switches w hw)
    change augmentation Ω (representation Ω g⁻¹ w) = 0 at hh
    change augmentation Ω w = 0
    simpa only [augmentation_permute] using hh

/-- Every full vector fixed by a Sylow of the weight-two stabilizer has even augmentation. -/
theorem sylow_fixed_le_core (v : Full Ω)
    (hw : (Finset.univ.filter fun i => v i ≠ 0).card = 2)
    (P : Sylow 2 (stabilizer v)) :
    Representation.BinaryOffender.fixedSpace (alternatingRepresentation Ω)
      ((P : Subgroup (stabilizer v)).map (stabilizer v).subtype) ≤ core Ω := by
  obtain ⟨a,ha2,ha⟩ := exists_even_fixed_involution v hw
  have hp : IsPGroup 2 (zpowers a) :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one ha2).isPGroup 2 _
  obtain ⟨Q,hQ⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (stabilizer v) Q P
  have hc : g * a * g⁻¹ ∈ (P : Subgroup (stabilizer v)) := by
    rw [← hg]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hQ (mem_zpowers a))
  intro w hw
  have hh := hw ⟨(g * a * g⁻¹).val, mem_map_of_mem _ hc⟩
  have he := ha (representation Ω (g.val.val)⁻¹ w)
    (conjugate_fixed g.val.val a.val.val w hh)
  change augmentation Ω (representation Ω (g.val.val)⁻¹ w) = 0 at he
  change augmentation Ω w = 0
  simpa only [augmentation_permute] using he
end BinaryPermutation.EightPointSylow
