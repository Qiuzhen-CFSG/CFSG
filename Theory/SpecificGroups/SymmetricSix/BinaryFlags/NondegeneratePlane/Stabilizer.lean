module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane.Orbit
public import Mathlib.GroupTheory.Perm.Finite

/-!
# The stabilizer of a nondegenerate plane in the native S₆ module

In the binary augmentation quotient, the nonzero vectors of the canonical
plane are precisely the duads contained in the first three letters. Thus its
setwise stabilizer preserves the two three-letter blocks. The literal block
embedding identifies this stabilizer with S₃ × S₃. Only three-letter and duad
identities are checked finitely; the stabilizer recognition is structural.

Source: Aschbacher--Smith, Lemma 13.5.6, printed p.917, the two cubic directions
of the nondegenerate-plane stabilizer in the actual natural module.
-/

@[expose] public section

open Subgroup BinaryPermutation Equiv Equiv.Perm
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane
open NaturalGeometry NaturalPairing Representation.BinaryOffender

theorem pairVector_triangle (i j k : Ω) :
    pairVector i j + pairVector i k = pairVector j k := by
  apply Subtype.ext
  change (constants Ω).mkQ _ + (constants Ω).mkQ _ = (constants Ω).mkQ _
  rw [← map_add]
  congr 1
  ext l
  simp only [Pi.add_apply, Pi.single_apply]
  split_ifs <;> decide

private theorem pairs_small (i j : Ω) (hij : i ≠ j) :
    (pair i j = pair 0 1 ∨ pair i j = pair 0 2 ∨ pair i j = pair 1 2) ↔
      i.val < 3 ∧ j.val < 3 := by decide +revert

theorem pairVector_mem_plane_iff_small {i j : Ω} (hij : i ≠ j) :
    pairVector i j ∈ plane ↔ i.val < 3 ∧ j.val < 3 := by
  rw [← pairs_small i j hij]
  constructor
  · intro h
    obtain ⟨a,b,h⟩ := Submodule.mem_span_pair.mp h
    fin_cases a <;> fin_cases b
    all_goals simp only [show (⟨0, by decide⟩ : Fin 2) = (0 : ZMod 2) from rfl,
      show (⟨1, by decide⟩ : Fin 2) = (1 : ZMod 2) from rfl,
      zero_smul, one_smul, zero_add, add_zero] at h
    · exact False.elim (pairVector_ne_zero hij h.symm)
    · exact Or.inr (Or.inl ((pairVector_eq_iff hij (by decide)).mp h.symm))
    · exact Or.inl ((pairVector_eq_iff hij (by decide)).mp h.symm)
    · rw [pairVector_triangle] at h
      exact Or.inr (Or.inr ((pairVector_eq_iff hij (by decide)).mp h.symm))
  · intro h
    rcases h with h | h | h
    · rw [(pairVector_eq_iff hij (by decide)).mpr h]
      exact Submodule.subset_span (by simp)
    · rw [(pairVector_eq_iff hij (by decide)).mpr h]
      exact Submodule.subset_span (by simp)
    · rw [(pairVector_eq_iff hij (by decide)).mpr h, ← pairVector_triangle 0 1 2]
      exact plane.add_mem (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))

noncomputable abbrev planeStabilizer : Subgroup S := subspaceStabilizer (naturalRepresentation Ω) plane

theorem mem_planeStabilizer_iff (g : S) : g ∈ planeStabilizer ↔
    (g 0).val < 3 ∧ (g 1).val < 3 ∧ (g 2).val < 3 := by
  constructor
  · intro hg
    have h01 := (hg (pairVector 0 1)).mpr (Submodule.subset_span (by simp))
    have h02 := (hg (pairVector 0 2)).mpr (Submodule.subset_span (by simp))
    rw [pairVector_map, pairVector_mem_plane_iff_small (g.injective.ne (by decide))] at h01 h02
    exact ⟨h01.1,h01.2,h02.2⟩
  · rintro ⟨h0,h1,h2⟩
    apply (mem_stabilizer_iff_map _ _).mpr
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [plane, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
      apply Submodule.span_le.mpr
      rintro v (rfl | rfl)
      · rw [pairVector_map]
        exact (pairVector_mem_plane_iff_small (g.injective.ne (by decide))).mpr ⟨h0,h1⟩
      · rw [pairVector_map]
        exact (pairVector_mem_plane_iff_small (g.injective.ne (by decide))).mpr ⟨h0,h2⟩
    · exact move_finrank g plane

abbrev TriplePerm := Equiv.Perm (Fin 3)
def tripleProductHom : TriplePerm × TriplePerm →* S :=
  (Equiv.permCongrHom (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6)).toMonoidHom.comp
    (Equiv.Perm.sumCongrHom _ _)

theorem tripleProductHom_injective : Function.Injective tripleProductHom :=
  (Equiv.permCongrHom _).injective.comp Equiv.Perm.sumCongrHom_injective

private theorem tripleProduct_small (x : TriplePerm × TriplePerm) :
    (tripleProductHom x 0).val < 3 ∧ (tripleProductHom x 1).val < 3 ∧
      (tripleProductHom x 2).val < 3 := by decide +revert

theorem tripleProduct_mem (x : TriplePerm × TriplePerm) :
    tripleProductHom x ∈ planeStabilizer :=
  (mem_planeStabilizer_iff _).mpr (tripleProduct_small x)


theorem tripleProduct_range : tripleProductHom.range = planeStabilizer := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    exact tripleProduct_mem x
  · intro g hg
    obtain ⟨h0,h1,h2⟩ := (mem_planeStabilizer_iff g).mp hg
    let e : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv
    let σ : Perm (Fin 3 ⊕ Fin 3) := e.symm.permCongr g
    have hi (i : Fin 3) : (g (e (Sum.inl i))).val < 3 := by
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    have hmap : Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl) := by
      rintro _ ⟨i,rfl⟩
      refine ⟨⟨(g (e (Sum.inl i))).val,hi i⟩,?_⟩
      apply e.injective
      change e (Sum.inl _) = e (e.symm (g (e (Sum.inl i))))
      rw [e.apply_symm_apply]
      apply Fin.ext
      rfl
    obtain ⟨x,hx⟩ := mem_sumCongrHom_range_of_perm_mapsTo_inl hmap
    refine ⟨x,?_⟩
    apply (Equiv.permCongrHom e.symm).injective
    change e.symm.permCongr (e.permCongr ((sumCongrHom _ _) x)) = σ
    calc
      e.symm.permCongr (e.permCongr ((sumCongrHom _ _) x)) = (sumCongrHom _ _) x := by
        ext i
        simp [Equiv.permCongr_apply]
      _ = σ := hx

noncomputable def tripleProductEquiv : TriplePerm × TriplePerm ≃* planeStabilizer :=
  MulEquiv.ofBijective (tripleProductHom.codRestrict _ tripleProduct_mem)
    ⟨fun x y h => tripleProductHom_injective (congrArg Subtype.val h), by
      intro g
      have hg : (g : S) ∈ tripleProductHom.range := by rw [tripleProduct_range]; exact g.property
      obtain ⟨x,hx⟩ := hg
      exact ⟨x,Subtype.ext hx⟩⟩

theorem planeStabilizer_card : Nat.card planeStabilizer = 36 := by
  rw [← Nat.card_congr tripleProductEquiv.toEquiv, Nat.card_prod]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane
