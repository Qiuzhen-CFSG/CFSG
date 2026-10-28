module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.DeletedEightAction

/-!
Adapted from `Atlas/Comparisons/Exceptional/DeletedEightFaithful.lean`.
The quotient retains its two-subset geometry, so its permutation action is faithful.
Membership is adapted to CFSG’s quadratic-isometry subgroup.
-/

@[expose] public noncomputable section
namespace Atlas.Order20160A8.DeletedEight
open Atlas.Codes Atlas.Order20160A8.HalfWeight ClassicalOrthogonal

def permutationHom : Equiv.Perm (Fin 8) →* isometrySubgroup quotientQuadratic where
  toFun p := ⟨quotientPerm p, (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr
    (permutationIsometry p).map_app⟩
  map_one' := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl
  map_mul' p r := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

def duadVector (i j : Fin 8) : V := Pi.single i 1 + Pi.single j 1

def duad (i j : Fin 8) : evenCode := ⟨duadVector i j, by
  change (∑ k : Fin 8, ((Pi.single i (1 : Bit) : V) k + (Pi.single j (1 : Bit) : V) k)) = 0
  simp [Finset.sum_add_distrib]⟩

theorem duad_permute (p : Equiv.Perm (Fin 8)) (i j : Fin 8) :
    evenPerm p (duad i j) = duad (p i) (p j) := by
  ext k
  simp [duad, duadVector, Pi.single_apply, Equiv.symm_apply_eq]

/-- A duad cannot become another duad by adding the all-ones word. -/
theorem duad_constant_test (i j k l : Fin 8) (a : Bit)
    (hij : i ≠ j) (_hkl : k ≠ l)
    (h : a • (fun _ : Fin 8 => (1 : Bit)) = duadVector i j - duadVector k l) :
    i = k ∨ i = l := by
  classical
  have hcard : ({i,j,k,l} : Finset (Fin 8)).card < Fintype.card (Fin 8) := by
    have hle : ({i,j,k,l} : Finset (Fin 8)).card ≤ 4 := by
      calc
        _ ≤ 1 + (1 + (1 + 1)) := by
          exact le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right
            (le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right
              (le_trans (Finset.card_insert_le _ _) (by simp)) 1)) 1)
        _ = 4 := rfl
    simpa using (lt_of_le_of_lt hle (by decide : 4 < 8))
  have hex : ∃ t : Fin 8, t ∉ ({i,j,k,l} : Finset (Fin 8)) := by
    by_contra hn
    push Not at hn
    have hs : ({i,j,k,l} : Finset (Fin 8)) = Finset.univ := by
      ext t
      simp [hn t]
    rw [hs, Finset.card_univ] at hcard
    exact (lt_irrefl _ hcard)
  obtain ⟨t, ht⟩ := hex
  have ht' : t ≠ i ∧ t ≠ j ∧ t ≠ k ∧ t ≠ l := by simpa using ht
  have ha : a = 0 := by
    have he := congrFun h t
    simpa [duadVector, Pi.single_apply, ht'.1, ht'.2.1, ht'.2.2.1, ht'.2.2.2] using he
  by_contra hn
  push Not at hn
  have he := congrFun h i
  simp [ha, duadVector, hij, hn.1, hn.2] at he

theorem duad_quotient_test (i j k l : Fin 8) (hij : i ≠ j) (hkl : k ≠ l)
    (h : (Submodule.Quotient.mk (duad i j) : W) = Submodule.Quotient.mk (duad k l)) :
    i = k ∨ i = l := by
  have hm := (Submodule.Quotient.eq constants).mp h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
  exact duad_constant_test i j k l a hij hkl (congrArg Subtype.val ha)

theorem permutationHom_injective : Function.Injective permutationHom := by
  apply (MonoidHom.ker_eq_bot_iff permutationHom).mp
  apply eq_bot_iff.mpr
  intro p hp
  have he : permutationHom p = 1 := hp
  change p = 1
  apply Equiv.ext
  intro i
  have hd (j : Fin 8) (hij : i ≠ j) : p i = i ∨ p i = j := by
    have h := congrArg (fun f : isometrySubgroup quotientQuadratic =>
      f.val (Submodule.Quotient.mk (duad i j))) he
    change (Submodule.Quotient.mk (evenPerm p (duad i j)) : W) =
      Submodule.Quotient.mk (duad i j) at h
    rw [duad_permute] at h
    exact duad_quotient_test _ _ _ _ (fun h => hij (p.injective h)) hij h
  have test : ∀ a b : Fin 8, (∀ j : Fin 8, a ≠ j → b = a ∨ b = j) → b = a := by decide
  exact test i (p i) hd

end Atlas.Order20160A8.DeletedEight
