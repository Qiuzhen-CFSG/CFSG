module

public import Theory.Representation.SymplecticFourOrthogonalCover.Roots
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# The binary transvection obstruction

In the explicit duad polar realization S₆ ≃ Sp₄(2), the first transvection
is the swap (3 5). A fifteen-point table verifies this matrix identity.
Its odd sign excludes it from the genuine commutator subgroup. Transport
through a field isomorphism and inner conjugation gives the obstruction
over every two-element field; the literal root intersection with Sp₄(K)′
is trivial. This does not affect the binary orthogonal cover or its fixed space.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.2.3(1b),(3),
printed p.413/PDF p.424, with the six-letter polar table from I.5.4, I.5.8–9.
This verifies the small-field convention needed when interpreting its roots.
-/

@[expose] public section

noncomputable section
namespace Representation.SymplecticFourOrthogonalCover.Roots
open Matrix Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymplecticFour

private lemma swap_table : ∀ d : Duad, ∃ d' : Duad,
    duadSet d' = (duadSet d).image (Equiv.swap (3 : Fin 6) 5) ∧
      rootMatrix 0 (1 : ZMod 2) *ᵥ (polarVector d).val = (polarVector d').val := by
  decide

lemma binary_root_is_swap :
    rootElement 0 (1 : ZMod 2) = polarRepresentation (Equiv.swap (3 : Fin 6) 5) := by
  apply Subtype.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨d, hd⟩ := polarVector_bijective.2 ⟨v, hv⟩
  have hd' : (polarVector d).val = v := congrArg Subtype.val hd
  rw [← hd', polarRepresentation_equivariant]
  obtain ⟨d', he, hm⟩ := swap_table d
  have he' : d' = (Equiv.swap (3 : Fin 6) 5) • d :=
    duadSet_injective (he.trans (duadSet_smul _ d).symm)
  exact hm.trans (congrArg (fun d => (polarVector d).val) he')

/-- The transvection is odd in the explicit S₆ realization, hence outside Sp₄(2)′. -/
theorem binary_root_not_mem_derived :
    rootElement 0 (1 : ZMod 2) ∉ commutator (Sp (ZMod 2)) := by
  intro h
  have hm : Binary.symmetricSixEquiv.symm (rootElement 0 (1 : ZMod 2)) ∈
      (commutator (Sp (ZMod 2))).map Binary.symmetricSixEquiv.symm.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨_, h, rfl⟩
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr Binary.symmetricSixEquiv.symm.surjective,
    ← commutator_def, alternatingGroup.commutator_perm_eq (by norm_num)] at hm
  rw [binary_root_is_swap, ← Binary.symmetricSixEquiv_apply,
    Binary.symmetricSixEquiv.symm_apply_apply] at hm
  have hn : Equiv.swap (3 : Fin 6) 5 ∉ alternatingGroup (Fin 6) := by decide
  exact hn hm

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

def fieldMap (f : K →+* ZMod 2) : Sp K →* Sp (ZMod 2) where
  toFun g := ⟨g.val.map f, SymplecticGroup.map_mem g.property f⟩
  map_one' := Subtype.ext (Matrix.map_one _ (map_zero _) (map_one _))
  map_mul' _ _ := Subtype.ext Matrix.map_mul

omit [Finite K] [CharP K 2] in
lemma fieldMap_root (f : K →+* ZMod 2) :
    fieldMap f (rootElement 0 1) = rootElement 0 1 := by
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [fieldMap, rootElement, rootMatrix, Matrix.map_apply, Matrix.fromBlocks, Matrix.single]

theorem card_two_root_not_mem_derived (hcard : Nat.card K = 2) :
    rootElement 0 (1 : K) ∉ commutator (Sp K) := by
  let := Fintype.ofFinite K
  let e := ZMod.ringEquiv K (by simpa [Nat.card_eq_fintype_card] using hcard)
  intro h
  apply binary_root_not_mem_derived
  rw [← fieldMap_root e.symm.toRingHom]
  have hm : (commutator (Sp K)).map (fieldMap e.symm.toRingHom) ≤ commutator (Sp (ZMod 2)) := by
    rw [map_commutator_eq, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  exact hm (Subgroup.mem_map.mpr ⟨_, h, rfl⟩)

theorem card_two_conjugate_root_not_mem_derived (hcard : Nat.card K = 2) (g : Sp K) :
    g * rootElement 0 1 * g⁻¹ ∉ commutator (Sp K) := by
  intro h
  apply card_two_root_not_mem_derived hcard
  have hm := (inferInstance : (commutator (Sp K)).Normal).conj_mem (g * rootElement 0 1 * g⁻¹) h g⁻¹
  simpa only [inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hm

/-- In the binary case the intersection of this transvection root with the
actual derived subgroup is trivial. -/
theorem card_two_root_group_bot (hcard : Nat.card K = 2) : group (K := K) = ⊥ := by
  apply bot_unique
  intro g hg
  obtain ⟨t, ht⟩ := (RootSubgroup.mem_group_iff 0 g.val).mp hg
  have ht0 : t = 0 := by
    by_contra hn
    let := Fintype.ofFinite K
    let e := ZMod.ringEquiv K (by simpa [Nat.card_eq_fintype_card] using hcard)
    have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    have ht1 : t = 1 := by
      rcases hz (e.symm t) with h | h
      · exact (hn (by simpa using congrArg e h)).elim
      · simpa using congrArg e h
    exact card_two_root_not_mem_derived hcard (ht1 ▸ ht.symm ▸ g.property)
  apply Subtype.ext
  change g.val = 1
  rw [← ht, ht0, RootSubgroup.element_zero]

end Representation.SymplecticFourOrthogonalCover.Roots
