module
public import Theory.Representation.BinaryPermutation.SevenParabolic.Conjugation
public import Theory.Alternating.theorem_5_2_1_2
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Pair vectors and two five-letter subgroups in the binary seven-letter core

The A₅ fixing 0 and 1 and its conjugate by (02)(13) contain all star
three-cycles based at 4 and 5, so generate A₇. Their moved spaces contain
six pair vectors ending at 6, a basis of the even-weight core. The pair
01 is a transposition displacement, is fixed by the first A₅, and moves
to pair 23 under the same even conjugator. Chart lemmas transport these
identities to the literal ambient commutators and subgroup containments.
All finite checks concern specified permutations or 128 binary words.

Source: Aschbacher--Smith, original 4.3.7, printed p.616.
-/

@[expose] public section
open Subgroup Equiv BinaryPermutation
open BinaryPermutation.SevenParabolic BinaryPermutation.SevenParabolic.Ordinary
open scoped BigOperators commutatorElement
namespace BinaryPermutation.SevenPairGeneration
def pair (i j : Fin 7) : Space :=
  ⟨Pi.single i 1 + Pi.single j 1, by
    simp [mem_core, Finset.sum_add_distrib]; decide⟩
def exchange : Perm (Fin 7) := swap 0 2 * swap 1 3
def five : Subgroup (Perm (Fin 7)) :=
  (fixingSubgroup (alternatingGroup (Fin 7)) ({0,1} : Set (Fin 7))).map
    (alternatingGroup (Fin 7)).subtype
lemma mem_five (g : Perm (Fin 7)) : g ∈ five ↔
    g ∈ alternatingGroup (Fin 7) ∧ g 0 = 0 ∧ g 1 = 1 := by
  constructor
  · rintro ⟨a,ha,rfl⟩
    have h := (mem_fixingSubgroup_iff _).mp ha
    exact ⟨a.property,h 0 (by simp),h 1 (by simp)⟩
  · rintro ⟨hg,h0,h1⟩
    refine ⟨⟨g,hg⟩,(mem_fixingSubgroup_iff _).mpr ?_,rfl⟩
    intro i hi
    rcases hi with rfl | rfl <;> assumption
lemma exchange_even : exchange ∈ alternatingGroup (Fin 7) := by
  rw [Perm.mem_alternatingGroup]; decide +kernel
lemma exchange_inv : exchange⁻¹ = exchange := by decide +kernel
lemma exchange_pair : action exchange⁻¹ (pair 0 1) = pair 2 3 := by decide +kernel
lemma pair_ne : pair 0 1 ≠ 0 := by decide +kernel
lemma pair_two (v : Space) : v + v = 0 := ZModModule.add_self v
lemma pair_fixed (g : Perm (Fin 7)) (h0 : g 0 = 0) (h1 : g 1 = 1) :
    action g (pair 0 1) = pair 0 1 := by
  apply Subtype.ext
  funext i
  change (pair 0 1).val (g.symm i) = (pair 0 1).val i
  simp only [pair, Pi.add_apply, Pi.single_apply]
  have h0' : g.symm i = 0 ↔ i = 0 := by rw [Equiv.symm_apply_eq,h0]
  have h1' : g.symm i = 1 ↔ i = 1 := by rw [Equiv.symm_apply_eq,h1]
  simp only [h0',h1']
lemma pair_displacement : pair 0 2 - action (swap 0 1) (pair 0 2) = pair 0 1 := by
  decide +kernel
def cycle (i : Fin 7) : Perm (Fin 7) :=
  swap i 6 * (if i = 4 ∨ i = 5 then swap 2 3 else swap 4 5)
lemma cycle_mem (i : Fin 7) (hi : 2 ≤ i.val) (hi6 : i ≠ 6) : cycle i ∈ five := by
  rw [mem_five]
  simp only [Perm.mem_alternatingGroup]
  exact (by decide +kernel : ∀ i : Fin 7, 2 ≤ i.val → i ≠ 6 →
    Perm.sign (cycle i) = 1 ∧ cycle i 0 = 0 ∧ cycle i 1 = 1) i hi hi6
lemma cycle_displacement (i : Fin 7) (hi : 2 ≤ i.val) (hi6 : i ≠ 6) :
    pair i 0 - action (cycle i) (pair i 0) = pair i 6 := by
  exact (by decide +kernel : ∀ i : Fin 7, 2 ≤ i.val → i ≠ 6 →
    pair i 0 - action (cycle i) (pair i 0) = pair i 6) i hi hi6
lemma pair23_expression : pair 2 3 = pair 2 6 + pair 3 6 := by decide +kernel
lemma pair06_exchange : pair 0 6 = action exchange⁻¹ (pair 2 6) := by decide +kernel
lemma pair16_exchange : pair 1 6 = action exchange⁻¹ (pair 3 6) := by decide +kernel
lemma pair_basis (v : Space) :
    v = ∑ i : Fin 6, v.val i.castSucc • pair i.castSucc 6 := by
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  exact (by decide +kernel : ∀ v : Full (Fin 7), (∑ i, v i) = 0 →
    v = ∑ i : Fin 6, v i.castSucc • (pair i.castSucc 6).val) v.val v.property

lemma star_placement : ∀ i : Fin 7, i ≠ 4 → i ≠ 5 →
    swap 4 5 * swap 4 i ∈ five ∨
      exchange * (swap 4 5 * swap 4 i) * exchange⁻¹ ∈ five := by
  intro i h4 h5
  simp only [mem_five,Perm.mem_alternatingGroup]
  exact (by decide +kernel : ∀ i : Fin 7, i ≠ 4 → i ≠ 5 →
    (Perm.sign (swap 4 5 * swap 4 i) = 1 ∧ (swap 4 5 * swap 4 i : Perm (Fin 7)) 0 = 0 ∧
      (swap 4 5 * swap 4 i : Perm (Fin 7)) 1 = 1) ∨
    (Perm.sign (exchange * (swap 4 5 * swap 4 i) * exchange⁻¹) = 1 ∧
      (exchange * (swap 4 5 * swap 4 i) * exchange⁻¹ : Perm (Fin 7)) 0 = 0 ∧
      (exchange * (swap 4 5 * swap 4 i) * exchange⁻¹ : Perm (Fin 7)) 1 = 1)) i h4 h5

lemma five_generation : five ⊔ five.map (MulAut.conj exchange⁻¹).toMonoidHom =
    alternatingGroup (Fin 7) := by
  let H := five ⊔ five.map (MulAut.conj exchange⁻¹).toMonoidHom
  have hle : H ≤ alternatingGroup (Fin 7) := by
    apply sup_le
    · exact map_subtype_le _
    · rintro _ ⟨g,hg,rfl⟩
      exact (alternatingGroup (Fin 7)).mul_mem
        ((alternatingGroup (Fin 7)).mul_mem
          ((alternatingGroup (Fin 7)).inv_mem exchange_even) (map_subtype_le _ hg))
        (by simpa only [inv_inv] using exchange_even)
  apply le_antisymm hle
  have htop : H.subgroupOf (alternatingGroup (Fin 7)) = ⊤ := by
    apply top_unique
    rw [← GLS3.Chapter5.starThreeCycles_closure_eq_top (a := (4 : Fin 7)) (b := 5) (by decide)]
    apply (closure_le _).mpr
    rintro g ⟨i,hi4,hi5,he⟩
    change g.val ∈ H
    rw [he]
    rcases star_placement i hi4 hi5 with h | h
    · exact mem_sup_left h
    · apply (show five.map (MulAut.conj exchange⁻¹).toMonoidHom ≤ H from le_sup_right)
      exact mem_map.mpr ⟨exchange * (swap 4 5 * swap 4 i) * exchange⁻¹,h,by
        simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,
          mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one]⟩
  intro g hg
  exact htop.ge (mem_top (⟨g,hg⟩ : alternatingGroup (Fin 7)))
end BinaryPermutation.SevenPairGeneration

namespace BinaryPermutation.SevenParabolic.Ordinary.Chart
variable {G : Type*} [Group G] {J C W : Subgroup G} (c : Chart J C W)
lemma lift_zero : c.lift 0 = 1 := c.moduleEquiv.symm.map_one
lemma lift_sub (v w : Space) : c.lift (v-w) = c.lift v * (c.lift w)⁻¹ := by
  rw [sub_eq_add_neg,c.lift_add]
  exact congrArg (fun a => c.lift v * a)
    (c.moduleEquiv.symm.map_inv (Multiplicative.ofAdd w))
lemma lift_displacement (j : J) (v : Space) :
    (c.lift (v - action (c.actor j) v) : G) = ⁅(c.lift v : G),j.val⁆ := by
  rw [c.lift_sub]
  change (c.lift v : G) * (c.lift (action (c.actor j) v) : G)⁻¹ = _
  rw [c.lift_action]
  simp only [commutatorElement_def,mul_inv_rev,inv_inv,mul_assoc]
lemma lift_displacement_mem (B : Subgroup G) (g : Perm (Fin 7))
    (hg : g ∈ (B.subgroupOf J).map c.actor) (v : Space) :
    (c.lift (v - action g v) : G) ∈ ⁅W,B⁆ := by
  obtain ⟨j,hj,rfl⟩ := hg
  rw [c.lift_displacement]
  exact commutator_mem_commutator (c.lift v).property hj
lemma lift_two (v : Space) : (c.lift v : G)^2 = 1 := by
  have he := congrArg Subtype.val (c.lift_add v v)
  rw [ZModModule.add_self,c.lift_zero] at he
  simpa only [pow_two,Subgroup.coe_mul,Subgroup.coe_one] using he.symm
lemma lift_pair_basis_le (H : Subgroup G)
    (h : ∀ i : Fin 6, (c.lift (BinaryPermutation.SevenPairGeneration.pair i.castSucc 6) : G) ∈ H) : W ≤ H := by
  have hsum (f : Fin 6 → Space) (s : Finset (Fin 6))
      (hf : ∀ i ∈ s, (c.lift (f i) : G) ∈ H) :
      (c.lift (∑ i ∈ s, f i) : G) ∈ H := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty,c.lift_zero,Subgroup.coe_one] using H.one_mem
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi,c.lift_add]
      exact H.mul_mem (hf i (Finset.mem_insert_self i s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
  intro w hw
  let v := (c.moduleEquiv ⟨w,hw⟩).toAdd
  have hv : (c.lift v : G) = w := congrArg Subtype.val (c.moduleEquiv.symm_apply_apply ⟨w,hw⟩)
  rw [← hv,BinaryPermutation.SevenPairGeneration.pair_basis v]
  apply hsum
  intro i _
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (v.val i.castSucc) with hi | hi
  · simp only [hi,zero_smul,c.lift_zero,Subgroup.coe_one,H.one_mem]
  · simpa only [hi,one_smul] using h i
end BinaryPermutation.SevenParabolic.Ordinary.Chart
