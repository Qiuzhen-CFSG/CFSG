module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Four fixed vectors for every binary subgroup of S₆

The stabilizer of a duad fixes every core vector constant on that duad
and on its four-point complement. These two coordinates embed F₂² in
its fixed space. Every two-subgroup lies in a Sylow subgroup; the actual
six-letter Sylow marking places it in a conjugate duad stabilizer.
Transporting the fixed space gives the lower bound without enumeration.

The original five-dimensional amalgam uses this to prove that its full
central four-group lies in the chosen module, retaining the Sylow action.
Source: Aschbacher--Smith, Notation 13.2.1 and Proposition 13.4.7(1),
printed pp.877 and900.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation.SixCoreSylow
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry

private def block (a b : ZMod 2) : core (Fin 6) :=
  ⟨fun i => if i = 4 ∨ i = 5 then b else a, by
    rw [mem_core]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp [show ∀ a : ZMod 2, a + a = 0 from CharTwo.add_self_eq_zero]⟩

private theorem block_fixed (g : S) (hg : g ∈ H1) (a b : ZMod 2) :
    coreRepresentation (Fin 6) g (block a b) = block a b := by
  apply Subtype.ext
  funext i
  change (if g⁻¹ i = 4 ∨ g⁻¹ i = 5 then b else a) =
    if i = 4 ∨ i = 5 then b else a
  have hi : (g⁻¹ i = 4 ∨ g⁻¹ i = 5) ↔ (i = 4 ∨ i = 5) := by
    change (pair 4 5).image g = pair 4 5 at hg
    have hm : i ∈ (pair 4 5).map g.toEmbedding ↔ i ∈ pair 4 5 := by
      rw [Finset.map_eq_image]
      exact Iff.of_eq (congrArg (fun s : Finset (Fin 6) => i ∈ s) hg)
    simpa only [Finset.mem_map_equiv,Equiv.Perm.inv_def,pair,Finset.mem_insert,Finset.mem_singleton] using hm
  simp only [hi]

private theorem four_le_point_fixed :
    4 ≤ Nat.card (fixedSpace (coreRepresentation (Fin 6)) H1) := by
  let f : ZMod 2 × ZMod 2 → fixedSpace (coreRepresentation (Fin 6)) H1 :=
    fun a => ⟨block a.1 a.2,fun g => block_fixed g.val g.property a.1 a.2⟩
  have hf : Function.Injective f := by
    intro a b he
    have h0 := congrArg (fun v : fixedSpace (coreRepresentation (Fin 6)) H1 => v.val.val 0) he
    have h4 := congrArg (fun v : fixedSpace (coreRepresentation (Fin 6)) H1 => v.val.val 4) he
    exact Prod.ext (by simpa [f,block] using h0)
      (by simpa [f,block] using h4)
  simpa using Nat.card_le_card_of_injective f hf

/-- Every two-subgroup of S₆ fixes at least four vectors in the augmentation core. -/
theorem four_le_card_fixed_of_twoGroup (P : Subgroup S) (hP : IsPGroup 2 P) :
    4 ≤ Nat.card (fixedSpace (coreRepresentation (Fin 6)) P) := by
  obtain ⟨T,hT⟩ := hP.exists_le_sylow
  obtain ⟨g,hg,_⟩ := sylow_flag T
  have hTP : (T : Subgroup S) ≤ H1.map (MulAut.conj g).toMonoidHom := by
    rw [←hg]
    exact map_mono inf_le_left
  have hf : fixedSpace (coreRepresentation (Fin 6)) (H1.map (MulAut.conj g).toMonoidHom) ≤
      fixedSpace (coreRepresentation (Fin 6)) P :=
    fun _ hv p => hv ⟨p.val,hTP (hT p.property)⟩
  have hc : 4 ≤ Nat.card (fixedSpace (coreRepresentation (Fin 6))
      (H1.map (MulAut.conj g).toMonoidHom)) := by
    rw [←Nat.card_congr (fixedSpaceConjEquiv (coreRepresentation (Fin 6)) H1 g).toEquiv]
    exact four_le_point_fixed
  exact hc.trans (Nat.card_le_card_of_injective (Submodule.inclusion hf)
    (Submodule.inclusion_injective hf))
end BinaryPermutation.SixCoreSylow
