module

public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.Overgroups
public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.Recognition

/-! Recognition and generation by two S₄ overgroups of the marked regular D₈. -/

@[expose] public section
open Equiv Subgroup
open scoped MatrixGroups
namespace Theory.SpecificGroups.SymmetricEight.RegularDihedralPair

private def pairMarking0 : P8 where
  toFun := ![0,1,2,3,4,5,6,7]
  invFun := ![0,1,2,3,4,5,6,7]
  left_inv := by decide
  right_inv := by decide

private def pairMarking1 : P8 where
  toFun := ![0,1,4,3,5,7,6,2]
  invFun := ![0,1,7,3,2,4,6,5]
  left_inv := by decide
  right_inv := by decide

private def pairMarking2 : P8 where
  toFun := ![0,1,5,3,7,2,6,4]
  invFun := ![0,1,5,3,7,2,6,4]
  left_inv := by decide
  right_inv := by decide

private def pairMarking3 : P8 where
  toFun := ![0,1,7,3,2,4,6,5]
  invFun := ![0,1,4,3,5,7,6,2]
  left_inv := by decide
  right_inv := by decide

private def pairMarking : Fin 4 → Fin 4 → P8 :=
  ![![pairMarking0,pairMarking1,pairMarking0,pairMarking2],![pairMarking1,pairMarking0,pairMarking0,pairMarking0],![pairMarking0,pairMarking0,pairMarking0,pairMarking3],![pairMarking2,pairMarking0,pairMarking3,pairMarking0]]

private def pairBack : Fin 4 → Fin 4 → Fin 4 → List (Fin 4) :=
  ![![![[],[],[],[]],![[0],[0,1],[3],[2]],![[],[],[],[]],![[0],[0,0,1],[2],[3,3]]],![![[0],[0,1],[2],[3]],![[],[],[],[]],![[0],[1],[3],[2]],![[],[],[],[]]],![![[],[],[],[]],![[0],[1],[2],[3]],![[],[],[],[]],![[0],[1,0],[3,3],[2]]],![![[0],[0,0,1],[3],[2,2]],![[],[],[],[]],![[0],[1,0],[2,2],[3]],![[],[],[],[]]]]

private def pairEscape : Fin 4 → Fin 4 → List (Fin 4) :=
  ![![[],[],[2,3,3,2],[]],![[],[],[],[2,3,2]],![[2,3,3,2],[],[],[]],![[],[2,3,2],[],[]]]

private def Compatible : Fin 4 → Fin 4 → Bool :=
  ![![false,true,false,true],![true,false,true,false],![false,true,false,true],![true,false,true,false]]

private def pairGenerators (i j : Fin 4) : Fin 4 → P8 := ![r,s,cubic i,cubic j]

private theorem pair_escape (i j : Fin 4) (hne : i ≠ j) (h : Compatible i j = false) :
    TreeTest (eval (pairGenerators i j) (pairEscape i j)) ∧
      eval (pairGenerators i j) (pairEscape i j) ∉ twoGroup := by
  decide +revert +kernel

private theorem pair_preserves (i j : Fin 4) (k : Fin 8) :
    (MulAut.conj (pairMarking i j)) (tWord k) ∈ twoGroup := by
  decide +revert +kernel

private theorem pair_back (i j k : Fin 4) (h : Compatible i j = true) :
    (MulAut.conj (pairMarking i j)) (eval (pairGenerators i j) (pairBack i j k)) =
      modelGenerators k := by
  decide +revert +kernel

private theorem pair_map_twoGroup (i j : Fin 4) :
    twoGroup.map (MulAut.conj (pairMarking i j)).toMonoidHom = twoGroup := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨g, ⟨k, rfl⟩, rfl⟩
    exact pair_preserves i j k
  · rw [card_map_of_injective (MulAut.conj (pairMarking i j)).injective]

private theorem maximalTwo_map {X : Subgroup P8} (hX : MaximalTwo X) (f : P8 ≃* P8)
    (hf : twoGroup.map f.toMonoidHom = twoGroup) : MaximalTwo (X.map f.toMonoidHom) := by
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
      (map_comap_eq_self (by
        intro x _
        exact ⟨f.symm x, f.apply_symm_apply x⟩)).symm
    _ = twoGroup := by rw [hL, hf]


theorem marked_pair_recognition {X : Subgroup P8} (hX : MaximalTwo X)
    (A B : Subgroup P8) (hAX : A ≤ X) (hBX : B ≤ X)
    (hTA : twoGroup ≤ A) (hTB : twoGroup ≤ B)
    (eA : A ≃* Perm (Fin 4)) (eB : B ≃* Perm (Fin 4)) (hne : A ≠ B) :
    X = A ⊔ B ∧ Nonempty (X ≃* PSL(3, ZMod 2)) := by
  obtain ⟨i, rfl⟩ := symmetricFour_classification hX A hAX hTA eA
  obtain ⟨j, rfl⟩ := symmetricFour_classification hX B hBX hTB eB
  have hij : i ≠ j := fun h => hne (congrArg localGroup h)
  have hgen (k : Fin 4) : pairGenerators i j k ∈ localGroup i ⊔ localGroup j := by
    fin_cases k
    · exact (le_sup_left : localGroup i ≤ localGroup i ⊔ localGroup j)
        (twoGroup_le_localGroup i r_mem)
    · exact (le_sup_left : localGroup i ≤ localGroup i ⊔ localGroup j)
        (twoGroup_le_localGroup i s_mem)
    · exact (le_sup_left : localGroup i ≤ localGroup i ⊔ localGroup j)
        (cubic_mem_localGroup i)
    · exact (le_sup_right : localGroup j ≤ localGroup i ⊔ localGroup j)
        (cubic_mem_localGroup j)
  have hjoin : localGroup i ⊔ localGroup j ≤ X := sup_le hAX hBX
  have hc : Compatible i j = true := by
    cases hh : Compatible i j with
    | true => rfl
    | false =>
      have he := pair_escape i j hij hh
      have hm := eval_mem X (pairGenerators i j) (fun k => hjoin (hgen k)) (pairEscape i j)
      exact False.elim (he.2 (mem_twoGroup_of_obstruction hX hm (treeTest_mem he.1)))
  let f := MulAut.conj (pairMarking i j)
  have hmodel : modelGroup ≤ (localGroup i ⊔ localGroup j).map f.toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    exact ⟨_, eval_mem _ _ hgen (pairBack i j k), pair_back i j k hc⟩
  have he : X.map f.toMonoidHom = modelGroup :=
    overgroup_eq_model (maximalTwo_map hX f (pair_map_twoGroup i j))
      (hmodel.trans (map_mono hjoin))
  have hEq : X = localGroup i ⊔ localGroup j := by
    apply le_antisymm ?_ hjoin
    intro x hx
    have hfx : f x ∈ (localGroup i ⊔ localGroup j).map f.toMonoidHom :=
      hmodel (he ▸ mem_map_of_mem f.toMonoidHom hx)
    obtain ⟨y, hy, hfy⟩ := hfx
    exact f.injective hfy ▸ hy
  refine ⟨hEq, ⟨?_⟩⟩
  exact (X.equivMapOfInjective f.toMonoidHom f.injective).trans
    ((MulEquiv.subgroupCongr he).trans modelEquivPsl3)

/-- The marked theorem stated with the actual Sylow inclusion. -/
theorem sylow_pair_recognition (X : Subgroup P8) (S : Sylow 2 X)
    (hS : (S : Subgroup X).map X.subtype = twoGroup)
    (A B : Subgroup P8) (hAX : A ≤ X) (hBX : B ≤ X)
    (hTA : twoGroup ≤ A) (hTB : twoGroup ≤ B)
    (eA : A ≃* Perm (Fin 4)) (eB : B ≃* Perm (Fin 4)) (hne : A ≠ B) :
    X = A ⊔ B ∧ Nonempty (X ≃* PSL(3, ZMod 2)) :=
  marked_pair_recognition (maximalTwo_of_sylow X S hS) A B hAX hBX hTA hTB eA eB hne

/-- An injective marked eight-point representation retains the original group
and both original local subgroups in the recognition and generation statement. -/
theorem representation_pair_recognition {G : Type*} [Group G]
    (f : G →* P8) (hf : Function.Injective f) (S : Sylow 2 G)
    (hS : (S : Subgroup G).map f = twoGroup)
    (A B : Subgroup G) (hSA : (S : Subgroup G) ≤ A) (hSB : (S : Subgroup G) ≤ B)
    (eA : A ≃* Perm (Fin 4)) (eB : B ≃* Perm (Fin 4)) (hne : A ≠ B) :
    A ⊔ B = ⊤ ∧ Nonempty (G ≃* PSL(3, ZMod 2)) := by
  have hmax : MaximalTwo f.range := by
    refine ⟨hS ▸ map_le_range _ _, ?_⟩
    intro K hK hKr hTK
    have hSK : (S : Subgroup G) ≤ K.comap f := by
      intro x hx
      exact hTK (hS ▸ mem_map_of_mem f hx)
    have he := S.is_maximal' (hK.comap_of_injective f hf) hSK
    calc
      K = (K.comap f).map f := (map_comap_eq_self hKr).symm
      _ = twoGroup := by rw [he, hS]
  have hpair := marked_pair_recognition hmax (A.map f) (B.map f)
    (map_le_range _ _) (map_le_range _ _) (hS ▸ map_mono hSA) (hS ▸ map_mono hSB)
    ((A.equivMapOfInjective f hf).symm.trans eA)
    ((B.equivMapOfInjective f hf).symm.trans eB)
    (fun h => hne (map_injective hf h))
  refine ⟨?_, ?_⟩
  · apply map_injective hf
    rw [Subgroup.map_sup]
    exact hpair.1.symm.trans (MonoidHom.range_eq_map f)
  · obtain ⟨e⟩ := hpair.2
    exact ⟨(MonoidHom.ofInjective hf).trans e⟩

end Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
