module
public import Theory.Representation.BinaryPermutation.SixCoreOrbits
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Mathlib.GroupTheory.Sylow

/-!
# The Sylow fixed space in the six-letter augmentation core

The Klein four-group on the first four letters fixes words of the form
(a,a,a,a,b,b) in the binary augmentation core. Its fixed space has at most
four elements. Embedding this two-subgroup in a Sylow subgroup and using
Sylow conjugacy gives the same upper bound for every Sylow subgroup of A₆.
This is the model bound used in Aschbacher–Smith 12.2.16, printed p.800.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation
namespace SixCoreSylow
private abbrev A := alternatingGroup (Fin 6)
private abbrev K := Multiplicative (ZMod 2 × ZMod 2)
private abbrev ρ := alternatingCoreRepresentation (Fin 6)
private def x : A := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def y : A := ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private def klein : K →* A where
  toFun a := (if a.toAdd.1 = 0 then 1 else x) * (if a.toAdd.2 = 0 then 1 else y)
  map_one' := by decide +kernel
  map_mul' := by decide +kernel
private theorem klein_two : IsPGroup 2 K := by
  intro a
  exact ⟨1, (by decide : ∀ a : K, a ^ 2 = 1) a⟩

private theorem shape (v : core (Fin 6)) (hx : ρ x v = v) (hy : ρ y v = v) :
    v.val = ![v.val 0,v.val 0,v.val 0,v.val 0,v.val 4,v.val 4] := by
  have h01 := congrArg (fun w : core (Fin 6) => w.val 0) hx
  have h23 := congrArg (fun w : core (Fin 6) => w.val 2) hx
  have h02 := congrArg (fun w : core (Fin 6) => w.val 0) hy
  change v.val 1 = v.val 0 at h01
  change v.val 3 = v.val 2 at h23
  change v.val 2 = v.val 0 at h02
  have hs := v.property
  rw [mem_core] at hs
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hs
  change v.val 0 + (v.val 1 + (v.val 2 + (v.val 3 + (v.val 4 + (v.val 5 + 0))))) = 0 at hs
  rw [h01,h23,h02] at hs
  have hs' : v.val 4 + v.val 5 = 0 := by
    simpa only [← add_assoc, CharTwo.add_self_eq_zero, zero_add, add_zero] using hs
  have h45 : v.val 5 = v.val 4 := by
    have hh := congrArg (fun z : ZMod 2 => v.val 4 + z) hs'
    simpa only [← add_assoc, CharTwo.add_self_eq_zero, zero_add, add_zero] using hh
  funext i
  fin_cases i <;> simp [h01,h23,h02,h45]

private theorem fixed_card : Nat.card (fixedSpace ρ klein.range) ≤ 4 := by
  let f : fixedSpace ρ klein.range → ZMod 2 × ZMod 2 := fun v => (v.val.val 0, v.val.val 4)
  have hf : Function.Injective f := by
    intro v w he
    have hx : x ∈ klein.range := ⟨Multiplicative.ofAdd (1,0), by decide +kernel⟩
    have hy : y ∈ klein.range := ⟨Multiplicative.ofAdd (0,1), by decide +kernel⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [shape v.val (v.property ⟨x,hx⟩) (v.property ⟨y,hy⟩),
      shape w.val (w.property ⟨x,hx⟩) (w.property ⟨y,hy⟩)]
    rw [show v.val.val 0 = w.val.val 0 from congrArg Prod.fst he,
      show v.val.val 4 = w.val.val 4 from congrArg Prod.snd he]
  simpa using Nat.card_le_card_of_injective f hf

/-- Every actual A₆ Sylow subgroup fixes at most four vectors in its core. -/
theorem card_fixed_le_four (S : Sylow 2 (alternatingGroup (Fin 6))) :
    Nat.card (fixedSpace (alternatingCoreRepresentation (Fin 6))
      (S : Subgroup (alternatingGroup (Fin 6)))) ≤ 4 := by
  have hp : IsPGroup 2 klein.range := klein_two.of_surjective klein.rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  have hb : Nat.card (fixedSpace ρ (P : Subgroup A)) ≤ 4 :=
    (Nat.card_le_card_of_injective
      (Submodule.inclusion (show fixedSpace ρ (P : Subgroup A) ≤ fixedSpace ρ klein.range from
        fun _ hv a => hv ⟨a,hP a.property⟩))
      (Submodule.inclusion_injective _)).trans fixed_card
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A P S
  have he : (P : Subgroup A).map (MulAut.conj g).toMonoidHom = S := by
    change ((g • P : Sylow 2 A) : Subgroup A) = _
    rw [hg]
  rw [← he, ← Nat.card_congr (fixedSpaceConjEquiv ρ (P : Subgroup A) g).toEquiv]
  exact hb
end SixCoreSylow
end BinaryPermutation
