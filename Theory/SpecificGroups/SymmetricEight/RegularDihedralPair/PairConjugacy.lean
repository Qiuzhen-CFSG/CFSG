module

public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.PairRecognition
import all Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.PairRecognition

/-!
# Retaining the permutation marking in pair recognition

This new strengthening reuses the frozen proof's private, checked pair
transporters. The intentional local `import all` keeps those certificates
private while exposing the actual conjugacy needed by module consumers.
-/

public section
open Equiv Subgroup
namespace Theory.SpecificGroups.SymmetricEight.RegularDihedralPair

theorem marked_pair_conjugate {X : Subgroup P8} (hX : MaximalTwo X)
    (A B : Subgroup P8) (hAX : A ≤ X) (hBX : B ≤ X)
    (hTA : twoGroup ≤ A) (hTB : twoGroup ≤ B)
    (eA : A ≃* Perm (Fin 4)) (eB : B ≃* Perm (Fin 4)) (hne : A ≠ B) :
    ∃ p : P8, X.map (MulAut.conj p).toMonoidHom = modelGroup := by
  obtain ⟨i, rfl⟩ := symmetricFour_classification hX A hAX hTA eA
  obtain ⟨j, rfl⟩ := symmetricFour_classification hX B hBX hTB eB
  have hij : i ≠ j := fun h => hne (congrArg localGroup h)
  have hgen (k : Fin 4) : pairGenerators i j k ∈ X := by
    fin_cases k
    · exact hX.1 r_mem
    · exact hX.1 s_mem
    · exact hAX (cubic_mem_localGroup i)
    · exact hBX (cubic_mem_localGroup j)
  have hc : Compatible i j = true := by
    cases hh : Compatible i j with
    | true => rfl
    | false =>
      have he := pair_escape i j hij hh
      have hm := eval_mem X (pairGenerators i j) hgen (pairEscape i j)
      exact False.elim (he.2 (mem_twoGroup_of_obstruction hX hm (treeTest_mem he.1)))
  let f := MulAut.conj (pairMarking i j)
  have hmodel : modelGroup ≤ X.map f.toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    exact ⟨_, eval_mem _ _ hgen (pairBack i j k), pair_back i j k hc⟩
  exact ⟨pairMarking i j,
    overgroup_eq_model (maximalTwo_map hX f (pair_map_twoGroup i j)) hmodel⟩

theorem sylow_pair_conjugate (X : Subgroup P8) (S : Sylow 2 X)
    (hS : (S : Subgroup X).map X.subtype = twoGroup)
    (A B : Subgroup P8) (hAX : A ≤ X) (hBX : B ≤ X)
    (hTA : twoGroup ≤ A) (hTB : twoGroup ≤ B)
    (eA : A ≃* Perm (Fin 4)) (eB : B ≃* Perm (Fin 4)) (hne : A ≠ B) :
    ∃ p : P8, X.map (MulAut.conj p).toMonoidHom = modelGroup :=
  marked_pair_conjugate (maximalTwo_of_sylow X S hS) A B hAX hBX hTA hTB eA eB hne

end Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
