module

public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.OneLocalExtension.Certificate

/-! The fixed-zero certificate forces a second actual S4 in every proper
overgroup of a local S4 whose regular D8 remains Sylow. -/

@[expose] public section
open Equiv Subgroup
namespace Theory.SpecificGroups.SymmetricEight.RegularDihedralPair

private theorem zero_local_second {X : Subgroup P8} (hX : MaximalTwo X)
    (hL : localGroup 0 ≤ X) (hne : X ≠ localGroup 0) :
    ∃ j : Fin 4, j ≠ 0 ∧ localGroup j ≤ X := by
  obtain ⟨g, hg, hgn⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hL (Ne.symm hne))
  obtain ⟨i, hi⟩ := twoGroup_regular.2 (g 0)
  let a := (tWord i)⁻¹ * g
  have ha : a 0 = 0 := by
    change (tWord i).symm (g 0) = 0
    rw [← hi, Equiv.symm_apply_apply]
  have haX : a ∈ X := X.mul_mem (X.inv_mem (hX.1 (tWord_mem i))) hg
  have han : a ∉ localGroup 0 := by
    intro hm
    apply hgn
    have hh := (localGroup 0).mul_mem (twoGroup_le_localGroup 0 (tWord_mem i)) hm
    simpa only [a, mul_inv_cancel_left] using hh
  rcases fixed_zero_extension_certificate a ha with h1 | hc | hc2 | ⟨j, hj, w, he⟩ | ⟨w, ht, hn⟩
  · exact False.elim (han (h1 ▸ (localGroup 0).one_mem))
  · exact False.elim (han (hc ▸ cubic_mem_localGroup 0))
  · exact False.elim (han (hc2 ▸ (localGroup 0).pow_mem (cubic_mem_localGroup 0) 2))
  all_goals
    have hv : eval ![r,s,cubic 0,a] w ∈ X := eval_mem X ![r,s,cubic 0,a] (by
      intro k
      fin_cases k
      · exact hX.1 r_mem
      · exact hX.1 s_mem
      · exact hL (cubic_mem_localGroup 0)
      · exact haX) _
  · exact ⟨j, hj, localGroup_le _ hX.1 (he ▸ hv)⟩
  · exact False.elim (hn (mem_twoGroup_of_obstruction hX hv (treeTest_mem ht)))

private def localMarking (j : Fin 4) : P8 where
  toFun := ![![0,1,2,3,4,5,6,7],![0,1,7,3,2,4,6,5],![0,1,5,3,7,2,6,4],![0,1,4,3,5,7,6,2]] j
  invFun := ![![0,1,2,3,4,5,6,7],![0,1,4,3,5,7,6,2],![0,1,5,3,7,2,6,4],![0,1,7,3,2,4,6,5]] j
  left_inv := by fin_cases j <;> decide
  right_inv := by fin_cases j <;> decide

private def markingTo (j : Fin 4) (k : Fin 3) : List (Fin 3) :=
  ![![[0],[1],[2]],![[0],[0,1],[2]],![[0],[0,0,1],[2]],![[0],[1,0],[2,2]]] j k

private def markingBack (j : Fin 4) (k : Fin 3) : List (Fin 3) :=
  ![![[0],[1],[2]],![[0],[1,0],[2]],![[0],[0,0,1],[2]],![[0],[0,1],[2,2]]] j k

private theorem marking_to (j : Fin 4) (k : Fin 3) :
    (MulAut.conj (localMarking j)) (![r,s,cubic j] k) =
      eval ![r,s,cubic 0] (markingTo j k) := by decide +revert +kernel

private theorem marking_back (j : Fin 4) (k : Fin 3) :
    (MulAut.conj (localMarking j)) (eval ![r,s,cubic j] (markingBack j k)) =
      (![r,s,cubic 0] : Fin 3 → P8) k := by decide +revert +kernel

private theorem marking_two (j : Fin 4) (i : Fin 8) :
    (MulAut.conj (localMarking j)) (tWord i) ∈ twoGroup := by decide +revert +kernel

private theorem marking_map_two (j : Fin 4) :
    twoGroup.map (MulAut.conj (localMarking j)).toMonoidHom = twoGroup := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨g, ⟨i, rfl⟩, rfl⟩
    exact marking_two j i
  · rw [card_map_of_injective (MulAut.conj (localMarking j)).injective]

private theorem marking_map_local (j : Fin 4) :
    (localGroup j).map (MulAut.conj (localMarking j)).toMonoidHom = localGroup 0 := by
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    change (MulAut.conj (localMarking j)) (![r,s,cubic j] k) ∈ localGroup 0
    rw [marking_to]
    exact eval_mem _ _ (local_generator_mem 0) _
  · apply (closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    exact ⟨_, eval_mem _ _ (local_generator_mem j) _, marking_back j k⟩

private noncomputable def localEquivZero (j : Fin 4) : localGroup j ≃* localGroup 0 :=
  ((localGroup j).equivMapOfInjective (MulAut.conj (localMarking j)).toMonoidHom
    (MulAut.conj (localMarking j)).injective).trans (MulEquiv.subgroupCongr (marking_map_local j))

private theorem maximalTwo_conjugate {X : Subgroup P8} (hX : MaximalTwo X) (j : Fin 4) :
    MaximalTwo (X.map (MulAut.conj (localMarking j)).toMonoidHom) := by
  let f := MulAut.conj (localMarking j)
  have hf : twoGroup.map f.toMonoidHom = twoGroup := marking_map_two j
  refine ⟨hf ▸ map_mono hX.1, ?_⟩
  intro K hK hKX hTK
  have hLX : K.comap f.toMonoidHom ≤ X := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hKX hx
    exact f.injective he ▸ hy
  have hTL : twoGroup ≤ K.comap f.toMonoidHom := by
    intro x hx
    exact hTK (hf ▸ mem_map_of_mem f.toMonoidHom hx)
  have hL := hX.2 _ (hK.comap_of_injective f.toMonoidHom f.injective) hLX hTL
  calc
    K = (K.comap f.toMonoidHom).map f.toMonoidHom :=
      (map_comap_eq_self (by intro x _; exact ⟨f.symm x, f.apply_symm_apply x⟩)).symm
    _ = twoGroup := by rw [hL, hf]

private def zeroWords : Fin 24 → List (Fin 3) :=
  ![[],[0],[1],[2],[0,0],[0,1],[0,2],[1,0],[1,2],[2,0],[2,1],[2,2],[0,0,0],[0,0,1],[0,0,2],[0,1,2],[0,2,1],[0,2,2],[1,0,2],[2,2,0],[0,0,0,2],[0,0,2,1],[0,0,2,2],[1,0,2,2]]
private def zeroWord (i : Fin 24) : P8 := eval ![r,s,cubic 0] (zeroWords i)

private def zeroNext : Fin 24 → Fin 3 → Fin 24 :=
  ![![1,2,3],![4,5,6],![7,0,8],![9,10,11],![12,13,14],![2,1,15],![11,16,17],![13,12,18],![16,11,10],![15,18,12],![14,3,2],![19,8,0],![0,7,20],![5,4,19],![17,21,22],![21,17,16],![20,6,5],![18,15,1],![10,9,23],![23,22,21],![22,23,9],![3,14,13],![8,19,4],![6,20,7]]

private def zeroPrev : Fin 24 → Fin 3 → Fin 24 :=
  ![![12,2,11],![0,5,17],![5,0,10],![21,10,0],![1,13,22],![13,1,16],![23,16,1],![2,12,23],![22,11,2],![3,18,20],![18,3,8],![6,8,3],![4,7,9],![7,4,21],![10,21,4],![9,17,5],![8,6,15],![14,15,6],![17,9,7],![11,22,13],![16,23,12],![15,14,19],![20,19,14],![19,20,18]]

private theorem zero_next (i : Fin 24) (k : Fin 3) :
    zeroWord i * (![r,s,cubic 0] : Fin 3 → P8) k = zeroWord (zeroNext i k) := by
  decide +revert +kernel
private theorem zero_prev (i : Fin 24) (k : Fin 3) :
    zeroWord i * ((![r,s,cubic 0] : Fin 3 → P8) k)⁻¹ = zeroWord (zeroPrev i k) := by
  decide +revert +kernel

private theorem zero_word_of_mem (g : P8) (hg : g ∈ localGroup 0) :
    ∃ i : Fin 24, zeroWord i = g := by
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨0, rfl⟩
  | mul_right x hx y hy ih =>
    obtain ⟨i, rfl⟩ := ih
    obtain ⟨k, rfl⟩ := hy
    exact ⟨zeroNext i k, (zero_next i k).symm⟩
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨i, rfl⟩ := ih
    obtain ⟨k, rfl⟩ := hy
    exact ⟨zeroPrev i k, (zero_prev i k).symm⟩

private theorem local_index_of_cubic_mem (j : Fin 4) (h : cubic j ∈ localGroup 0) : j = 0 := by
  obtain ⟨i, hi⟩ := zero_word_of_mem _ h
  have hj : ∀ j : Fin 4, ∀ i : Fin 24, zeroWord i = cubic j → j = 0 := by decide +kernel
  exact hj j i hi

/-- Every proper overgroup of an actual S4 containing the regular Sylow D8
contains a second, distinct actual S4 over that same Sylow subgroup. -/
theorem proper_overgroup_second_local {X : Subgroup P8} (hX : MaximalTwo X)
    (A : Subgroup P8) (hAX : A ≤ X) (hTA : twoGroup ≤ A)
    (eA : A ≃* Perm (Fin 4)) (hne : X ≠ A) :
    ∃ B : Subgroup P8, B ≤ X ∧ twoGroup ≤ B ∧
      Nonempty (B ≃* Perm (Fin 4)) ∧ A ≠ B := by
  obtain ⟨i, hi⟩ := symmetricFour_classification hX A hAX hTA eA
  let f := MulAut.conj (localMarking i)
  have hi0 : A.map f.toMonoidHom = localGroup 0 := by rw [hi]; exact marking_map_local i
  have h0 : localGroup 0 ≤ X.map f.toMonoidHom := hi0 ▸ map_mono hAX
  have hn0 : X.map f.toMonoidHom ≠ localGroup 0 := by
    rw [← hi0]
    exact fun hh => hne (map_injective f.injective hh)
  obtain ⟨j, hj, hBX⟩ := zero_local_second (maximalTwo_conjugate hX i) h0 hn0
  let B := (localGroup j).comap f.toMonoidHom
  have hBmap : B.map f.toMonoidHom = localGroup j :=
    map_comap_eq_self (by intro x _; exact ⟨f.symm x, f.apply_symm_apply x⟩)
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨x, hx, he⟩ := hBX hb
    exact f.injective he ▸ hx
  · intro x hx
    exact twoGroup_le_localGroup j (marking_map_two i ▸ mem_map_of_mem f.toMonoidHom hx)
  · exact ⟨(B.equivMapOfInjective f.toMonoidHom f.injective).trans
      ((MulEquiv.subgroupCongr hBmap).trans ((localEquivZero j).trans
        (((localEquivZero i).symm.trans (MulEquiv.subgroupCongr hi.symm)).trans eA)))⟩
  · intro he
    have hh : localGroup 0 = localGroup j := hi0.symm.trans ((congrArg (map f.toMonoidHom) he).trans hBmap)
    have hc : cubic j ∈ localGroup 0 := hh ▸ cubic_mem_localGroup j
    exact hj (local_index_of_cubic_mem j hc)

end Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
