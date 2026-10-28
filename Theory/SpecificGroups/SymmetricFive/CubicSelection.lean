module
public import Theory.SpecificGroups.SymmetricFive.OuterFourGeometry
import all Theory.SpecificGroups.SymmetricFive.OuterFourGeometry
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryOffender.Basic
public import Mathlib.Tactic
/-!
# The selected cubic inside the alternating-five layer

The three-point symmetric subgroup intersects A₅ in its actual cubic,
not the full S₃. This cubic is normalized by the transposition four-group,
and together with the marked full Sylow it generates S₅. It moves a
vector fixed by the four-group in the original natural module.

This is an internal computational companion to OuterFourGeometry: its
private finite word tables are imported solely to check the same marked
subgroups, without duplicating their definitions or changing their API.
The checks use three cubic words and twelve local words.
Source: Aschbacher–Smith C.1.23(1), printed p.130.
-/
public section
open Subgroup Equiv Representation.BinaryOffender
open scoped commutatorElement
namespace Theory.SpecificGroups.SymmetricFive.CubicSelection
open OuterFourGeometry
abbrev Sym := Perm (Fin 5)
@[expose] def cycle : Sym := swap 0 1 * swap 1 4
private def word : Fin 3 → Sym := ![1,cycle,cycle^2]
def cubic : Subgroup Sym where
  carrier := Set.range word
  one_mem' := ⟨0,rfl⟩
  mul_mem' := by
    have hc : ∀ i j, ∃ k, word i * word j = word k := by decide +kernel
    rintro x y ⟨i,rfl⟩ ⟨j,rfl⟩
    obtain ⟨k,hk⟩ := hc i j
    exact ⟨k,hk.symm⟩
  inv_mem' := by
    have hc : ∀ i, ∃ j, (word i)⁻¹ = word j := by decide +kernel
    rintro x ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := hc i
    exact ⟨j,hj.symm⟩
def symmetricThree : Subgroup Sym where
  carrier := {g | g 2=2 ∧ g 3=3}
  one_mem' := by simp
  mul_mem' := by rintro a b ⟨ha2,ha3⟩ ⟨hb2,hb3⟩; exact ⟨by simpa [Perm.mul_apply,hb2],by simpa [Perm.mul_apply,hb3]⟩
  inv_mem' := by rintro a ⟨ha2,ha3⟩; exact ⟨a.symm_apply_eq.mpr ha2.symm,a.symm_apply_eq.mpr ha3.symm⟩

theorem cycle_mem : cycle ∈ cubic := ⟨1,rfl⟩

theorem cubic_card : Nat.card cubic = 3 := by
  have hi : Function.Injective word := by decide +kernel
  change Nat.card (Set.range word)=3
  rw [←Nat.card_congr (Equiv.ofInjective _ hi)]
  simp

theorem three_inf_alternating : symmetricThree ⊓ alternatingGroup (Fin 5) = cubic := by
  have hc : ∀ g : Sym, g 2=2 ∧ g 3=3 ∧ g.sign=1 ↔ ∃ i, word i=g := by decide +kernel
  ext g
  change (g 2=2 ∧ g 3=3) ∧ g∈alternatingGroup (Fin 5) ↔ ∃ i, word i=g
  rw [Perm.mem_alternatingGroup]
  exact (and_assoc).trans (hc g)

theorem cubic_le_alternating : cubic ≤ alternatingGroup (Fin 5) := by
  rw [←three_inf_alternating]
  exact inf_le_right

theorem cubic_le_local : cubic ≤ localGroup := by
  have hc : ∀ i, word i ∈ localGroup := by
    change ∀ i, ∃ d : DihedralGroup 6, OuterFourGeometry.localHom d = word i
    decide +kernel
  rintro g ⟨i,rfl⟩
  exact hc i

theorem four_normalizes_cubic : four ≤ normalizer (cubic : Set Sym) := by
  have hc : ∀ (g : Sym), g∈four → ∀ i, ∃ j, g*word i*g⁻¹=word j := by
    change ∀ g, (∃ k, OuterFourGeometry.fourWord k=g) → ∀ i, ∃ j, g*word i*g⁻¹=word j
    decide +kernel
  intro g hg
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := hc g hg i
    exact ⟨j,hj.symm⟩
  · rintro ⟨i,hi⟩
    obtain ⟨j,hj⟩ := hc g⁻¹ (four.inv_mem hg) i
    refine ⟨j,?_⟩
    rw [←hj,hi]
    simp [mul_assoc]

theorem cubic_sup_four : cubic ⊔ four = localGroup := by
  apply le_antisymm (sup_le cubic_le_local four_le_local)
  intro g hg
  have hc : ∀ g : Sym, g ∈ localGroup → ∃ i, ∃ b : Sym, b∈four ∧ g=word i*b := by
    have ht : ∀ d : DihedralGroup 6, ∃ i j, OuterFourGeometry.localHom d=word i*OuterFourGeometry.fourWord j := by decide +kernel
    rintro g ⟨d,rfl⟩
    obtain ⟨i,j,hij⟩ := ht d
    exact ⟨i,_,⟨j,rfl⟩,hij⟩
  obtain ⟨i,b,hb,he⟩ := hc g hg
  rw [he]
  exact mul_mem ((le_sup_left : cubic ≤ cubic ⊔ four) ⟨i,rfl⟩) ((le_sup_right : four ≤ cubic ⊔ four) hb)

theorem cubic_sup_eight : cubic ⊔ eight = ⊤ := by
  apply top_unique
  rw [←local_sup_eight,←cubic_sup_four]
  exact sup_le (sup_le le_sup_left (four_le_eight.trans le_sup_right)) le_sup_right

/-- The marked outer four-group inverts the cubic, so its commutators generate it. -/
theorem cubic_eq_commutator_four : cubic = ⁅cubic,four⁆ := by
  apply le_antisymm ?_ (le_normalizer_iff_commutator_le_left.mp four_normalizes_cubic)
  have ht : Equiv.swap (0 : Fin 5) 1 ∈ four := ⟨1,rfl⟩
  have he : ⁅cycle^2,Equiv.swap (0 : Fin 5) 1⁆=cycle := by decide +kernel
  have hc : cycle∈⁅cubic,four⁆ := he ▸ commutator_mem_commutator (cubic.pow_mem cycle_mem 2) ht
  rintro g ⟨i,rfl⟩
  fin_cases i
  · exact one_mem _
  · exact hc
  · exact pow_mem hc 2

theorem cubic_residual : pResidual 2 cubic = ⊤ := by
  apply top_unique
  intro g _
  have hp : IsPGroup 3 cubic := IsPGroup.of_card (n:=1) (by simpa using cubic_card)
  exact mem_pResidual_of_orderOf_coprime (hp.orderOf_coprime (by decide : Nat.Coprime 3 2) g).symm

private def fixedPair : BinaryPermutation.core (Fin 5) := ⟨![1,1,0,0,0], by rw [BinaryPermutation.mem_core]; decide⟩

theorem cubic_moves_four_fixed : ∃ v ∈ fixedSpace (BinaryPermutation.coreRepresentation (Fin 5)) four,
    BinaryPermutation.coreRepresentation (Fin 5) cycle v ≠ v := by
  refine ⟨fixedPair,?_,?_⟩
  · have hc : ∀ g : Sym, g∈four → BinaryPermutation.representation (Fin 5) g fixedPair.val=fixedPair.val := by
      change ∀ g, (∃ i, OuterFourGeometry.fourWord i=g) → _
      decide +kernel
    intro g
    exact Subtype.ext (hc g g.property)
  · intro he
    have hh := congrArg (fun v : BinaryPermutation.core (Fin 5) => v.val 4) he
    exact (by decide : BinaryPermutation.representation (Fin 5) cycle fixedPair.val 4 ≠ fixedPair.val 4) hh
end Theory.SpecificGroups.SymmetricFive.CubicSelection
