module

public import Theory.Representation.HexacodeAction.CubicLocalModel
public import Theory.Representation.BinaryOffender.EquivariantStabilizer
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Models
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Theory.GroupTheory.CComponent.HexacodeTheta.ExponentThree

/-!
# Point stabilizers in the concrete triple cover

Every line of the binary natural module is spanned by a duad vector. Double
transitivity of the alternating coordinate group, and surjectivity of the
hexacode coordinate map, conjugate its stabilizer to that of the duad {0,1}.
The existing signed four-letter permutation model identifies the coordinate
stabilizer with S₄. Thus each actual stabilizer surjects onto S₄ with central
kernel of order three. The cover's checked exponent-three Sylow calculation
also excludes elements of order nine in these stabilizers.

These are structural inputs to the cubic calculation in Aschbacher–Smith,
combined manuscript of 1 March 2004, Notation 13.2.1 and Lemma 13.2.2(3),
printed pp.876–877. The full stabilizer is kept distinct from its A₄ residual.
The monomial cover and its coordinate map are those of the licensed ATLAS
port imported by `Cover`; no alternative group model or splitting is assumed.
-/

public section

noncomputable section
open Subgroup
namespace Representation.Hexacode.CubicLocalModel.Orders
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Atlas.Codes

private def baseLine : Submodule (ZMod 2) Natural :=
  Submodule.span (ZMod 2) {pairVector 0 1}

private theorem exists_baseLine_image (W : Submodule (ZMod 2) Natural)
    (hdim : Module.finrank (ZMod 2) W = 1) :
    ∃ g : H, baseLine.map (naturalAction g) = W := by
  have hW : W ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at hdim
    contradiction
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨d, rfl⟩ := (vector_cases v).resolve_left hv0
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hdim hv
    (duadVector_ne_zero d)
  have := alternatingGroup.isMultiplyPretransitive (Fin 6)
  have ht : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 6)) (Fin 6) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card (Fin 6) - 2)
      (by norm_num) (Nat.sub_le _ _)
  obtain ⟨a, ha, hb⟩ := (MulAction.is_two_pretransitive_iff.mp ht)
    (by decide : (0 : Fin 6) ≠ 1) (ne_of_lt d.property)
  obtain ⟨g, hg⟩ := hexEvenCoordinate_surjective a
  refine ⟨g, ?_⟩
  rw [baseLine, Submodule.map_span]
  simp only [Set.image_singleton]
  change Submodule.span (ZMod 2)
    {BinaryPermutation.naturalRepresentation (Fin 6) (hexEvenCoordinate g).val
      (pairVector 0 1)} = W
  rw [hg, pairVector_map]
  change Submodule.span (ZMod 2) {pairVector (a.val 0) (a.val 1)} = W
  rw [show a.val 0 = d.val.1 from ha, show a.val 1 = d.val.2 from hb]
  exact hspan.symm

private def actionEquiv (g : H) : Natural ≃ₗ[ZMod 2] Natural :=
  LinearEquiv.ofLinearMap (naturalAction g) (naturalAction g⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

private theorem actionEquiv_conj (g x : H) (v : Natural) :
    actionEquiv g (naturalAction x v) =
      naturalAction (MulAut.conj g x) (actionEquiv g v) := by
  change naturalAction g (naturalAction x v) =
    naturalAction (g * x * g⁻¹) (naturalAction g v)
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

private theorem stabilizer_map_conj (W : Submodule (ZMod 2) Natural) (g : H) :
    (stabilizer W).map (MulAut.conj g).toMonoidHom =
      stabilizer (W.map (naturalAction g)) :=
  BinaryOffender.map_subspaceStabilizer_equivariant naturalAction naturalAction
    (MulAut.conj g) (actionEquiv g) (actionEquiv_conj g) W

private def stabilizerConjEquiv (W : Submodule (ZMod 2) Natural) (g : H) :
    stabilizer W ≃* stabilizer (W.map (naturalAction g)) :=
  ((MulAut.conj g).subgroupMap _).trans (MulEquiv.subgroupCongr (stabilizer_map_conj W g))

private theorem mem_stabilizer_iff_map (W : Submodule (ZMod 2) Natural) (x : H) :
    x ∈ stabilizer W ↔ W.map (naturalAction x) = W := by
  constructor
  · intro hx
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact (hx v).2 hv
    · intro v hv
      refine ⟨naturalAction x⁻¹ v, ?_, ?_⟩
      · apply (hx (naturalAction x⁻¹ v)).1
        simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
          map_one, Module.End.one_apply] using hv
      · simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
          map_one, Module.End.one_apply]
  · intro hx v
    constructor
    · intro hv
      rw [← hx] at hv
      obtain ⟨w, hw, he⟩ := hv
      have hinj : Function.Injective (naturalAction x) := (actionEquiv x).injective
      exact hinj he ▸ hw
    · intro hv
      rw [← hx]
      exact Submodule.mem_map_of_mem hv

private theorem baseLine_stabilizer_eq :
    stabilizer baseLine = a6DuadStabilizer.comap hexEvenCoordinate := by
  ext x
  rw [mem_stabilizer_iff_map]
  change baseLine.map (BinaryPermutation.naturalRepresentation (Fin 6)
    (hexEvenCoordinate x).val) = baseLine ↔
    (pair 0 1).image (hexEvenCoordinate x).val = pair 0 1
  set a := (hexEvenCoordinate x).val
  rw [baseLine, Submodule.map_span]
  simp only [Set.image_singleton, pairVector_map]
  constructor
  · intro he
    have hv : pairVector (a 0) (a 1) ∈ Submodule.span (ZMod 2) {pairVector 0 1} := by
      rw [← he]
      exact Submodule.subset_span (by simp)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    have hvec : pairVector (a 0) (a 1) = pairVector 0 1 := by
      fin_cases c
      · change (0 : ZMod 2) • pairVector 0 1 = pairVector (a 0) (a 1) at hc
        exact False.elim (pairVector_ne_zero (a.injective.ne (by decide : (0 : Fin 6) ≠ 1))
          (by simpa using hc.symm))
      · change (1 : ZMod 2) • pairVector 0 1 = pairVector (a 0) (a 1) at hc
        simpa using hc.symm
    have hp := (pairVector_eq_iff (a.injective.ne (by decide : (0 : Fin 6) ≠ 1))
      (by decide : (0 : Fin 6) ≠ 1)).mp hvec
    simpa [pair] using hp
  · intro hp
    have hvec := (pairVector_eq_iff (a.injective.ne (by decide : (0 : Fin 6) ≠ 1))
      (by decide : (0 : Fin 6) ≠ 1)).mpr
      (by simpa [pair] using hp)
    rw [hvec]

private def baseCoordinate : stabilizer baseLine →* a6DuadStabilizer :=
  (hexEvenCoordinate.comp (stabilizer baseLine).subtype).codRestrict _
    (fun x => by
      change hexEvenCoordinate x.val ∈ a6DuadStabilizer
      simpa only [baseLine_stabilizer_eq, mem_comap] using x.property)

private theorem baseCoordinate_surjective : Function.Surjective baseCoordinate := by
  intro a
  obtain ⟨g, hg⟩ := hexEvenCoordinate_surjective a.val
  refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
  rw [baseLine_stabilizer_eq, mem_comap, hg]
  exact a.property

private theorem baseCoordinate_kernel_map :
    baseCoordinate.ker.map (stabilizer baseLine).subtype = hexEvenCoordinate.ker := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact congrArg Subtype.val hx
  · intro hg
    have hs : g ∈ stabilizer baseLine := by
      rw [baseLine_stabilizer_eq, mem_comap]
      change hexEvenCoordinate g ∈ a6DuadStabilizer
      rw [show hexEvenCoordinate g = 1 from hg]
      exact one_mem _
    exact ⟨⟨g, hs⟩, Subtype.ext hg, rfl⟩

private theorem baseCoordinate_kernel_card : Nat.card baseCoordinate.ker = 3 := by
  rw [← card_map_of_injective (stabilizer baseLine).subtype_injective,
    baseCoordinate_kernel_map, hexEven_kernel_card]

private theorem baseCoordinate_kernel_central : baseCoordinate.ker ≤ center (stabilizer baseLine) := by
  intro x hx
  have hm : x.val ∈ hexEvenCoordinate.ker := by
    rw [← baseCoordinate_kernel_map]
    exact mem_map.mpr ⟨x, hx, rfl⟩
  rw [even_kernel_eq_center] at hm
  rw [mem_center_iff]
  intro y
  apply Subtype.ext
  exact mem_center_iff.mp hm y.val

private def pointStabilizerEquiv (W : Submodule (ZMod 2) Natural)
    (hdim : Module.finrank (ZMod 2) W = 1) : stabilizer W ≃* stabilizer baseLine :=
  ((stabilizerConjEquiv baseLine (exists_baseLine_image W hdim).choose).trans
    (MulEquiv.subgroupCongr (congrArg stabilizer (exists_baseLine_image W hdim).choose_spec))).symm

/-- The actual point stabilizer maps onto the symmetric group on four letters. -/
def symmetricFourMap (W : Submodule (ZMod 2) Natural)
    (hdim : Module.finrank (ZMod 2) W = 1) : stabilizer W →* Equiv.Perm (Fin 4) :=
  a6DuadModelEquiv.symm.toMonoidHom.comp
    (baseCoordinate.comp (pointStabilizerEquiv W hdim).toMonoidHom)

/-- Every four-letter permutation has a lift in the point stabilizer. -/
theorem symmetricFourMap_surjective (W : Submodule (ZMod 2) Natural)
    (hdim : Module.finrank (ZMod 2) W = 1) : Function.Surjective (symmetricFourMap W hdim) :=
  a6DuadModelEquiv.symm.surjective.comp
    (baseCoordinate_surjective.comp (pointStabilizerEquiv W hdim).surjective)

private theorem symmetricFourMap_kernel_map (W : Submodule (ZMod 2) Natural)
    (hdim : Module.finrank (ZMod 2) W = 1) :
    (symmetricFourMap W hdim).ker.map (pointStabilizerEquiv W hdim).toMonoidHom =
      baseCoordinate.ker := by
  ext x
  rw [mem_map_equiv, MonoidHom.mem_ker, MonoidHom.mem_ker]
  change a6DuadModelEquiv.symm
    (baseCoordinate (pointStabilizerEquiv W hdim ((pointStabilizerEquiv W hdim).symm x))) = 1 ↔ _
  rw [MulEquiv.apply_symm_apply, map_eq_one_iff _ a6DuadModelEquiv.symm.injective]

/-- The point-stabilizer map retains exactly the cubic coordinate kernel. -/
theorem symmetricFourMap_kernel_card (W : Submodule (ZMod 2) Natural)
    (hdim : Module.finrank (ZMod 2) W = 1) : Nat.card (symmetricFourMap W hdim).ker = 3 := by
  have hc := card_map_of_injective (K := (symmetricFourMap W hdim).ker)
    (f := (pointStabilizerEquiv W hdim).toMonoidHom) (pointStabilizerEquiv W hdim).injective
  rw [symmetricFourMap_kernel_map, baseCoordinate_kernel_card] at hc
  exact hc.symm

/-- Kernel centrality is relative to the actual point stabilizer. -/
theorem symmetricFourMap_kernel_central (W : Submodule (ZMod 2) Natural)
    (hdim : Module.finrank (ZMod 2) W = 1) :
    (symmetricFourMap W hdim).ker ≤ center (stabilizer W) := by
  intro x hx
  have hm : pointStabilizerEquiv W hdim x ∈ baseCoordinate.ker := by
    rw [← symmetricFourMap_kernel_map W hdim]
    exact mem_map_of_mem _ hx
  have hc := baseCoordinate_kernel_central hm
  rw [mem_center_iff] at hc ⊢
  intro y
  apply (pointStabilizerEquiv W hdim).injective
  simpa only [map_mul] using hc (pointStabilizerEquiv W hdim y)

/-- Point stabilizers inherit the absence of elements of order nine. -/
theorem stabilizer_cube_eq_one_of_ninth (W : Submodule (ZMod 2) Natural)
    {g : stabilizer W} (hg : g ^ 9 = 1) : g ^ 3 = 1 := by
  apply Subtype.ext
  exact Theory.GroupTheory.HexacodeTheta.cube_eq_one_of_ninth (congrArg Subtype.val hg)

end Representation.Hexacode.CubicLocalModel.Orders
