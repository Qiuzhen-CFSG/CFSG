module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.MiddleParabolic.Coordinates
public import Theory.AlgebraicGroup.Representations.Unipotent.Flag

/-!
# Transport of the middle-node flag calculations

An adapted basis for the chain 0 < L < P < F < V gives an actual linear
equivalence carrying the coordinate flag to any incident flag of dimensions
1,2,3. Conjugation by this equivalence identifies both the line--hyperplane
stabilizer and the full flag stabilizer, with their ambient embeddings.

Reference: the middle minimal parabolic in Aschbacher--Smith 13.8.25,
printed p.962 (PDF p.979).
-/

public section

namespace BinaryLinear.MiddleParabolic

private theorem dimension : Module.finrank (ZMod 2) V = 4 := by simp [V]

theorem exists_adapted_basis (L P F : Submodule (ZMod 2) V)
    (hLP : L ≤ P) (hPF : P ≤ F)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hF : Module.finrank (ZMod 2) F = 3) :
    ∃ b : Module.Basis (Fin 4) (ZMod 2) V,
      L = Submodule.span (ZMod 2) (Set.range fun i : Fin 1 => b (Fin.castLE (by decide) i)) ∧
      P = Submodule.span (ZMod 2) (Set.range fun i : Fin 2 => b (Fin.castLE (by decide) i)) ∧
      F = Submodule.span (ZMod 2) (Set.range fun i : Fin 3 => b (Fin.castLE (by decide) i)) := by
  let C : ℕ → Submodule (ZMod 2) V := fun n =>
    if n = 0 then ⊥ else if n = 1 then L else if n = 2 then P else if n = 3 then F else ⊤
  have hm : Monotone C := by
    apply monotone_nat_of_le_succ
    intro n
    by_cases hn : n < 4
    · interval_cases n <;> simp [C, hLP, hPF]
    · have hn0 : n ≠ 0 := by omega
      have hn1 : n ≠ 1 := by omega
      have hn2 : n ≠ 2 := by omega
      have hn3 : n ≠ 3 := by omega
      have hs2 : n+1 ≠ 2 := by omega
      have hs3 : n+1 ≠ 3 := by omega
      simp [C, hn0, hn1, hn2, hn3, hs2, hs3]
  have hd : ∀ i, Module.finrank (ZMod 2) (C i) = min i (Module.finrank (ZMod 2) V) := by
    intro i
    rw [dimension]
    by_cases hi : i < 4
    · interval_cases i <;> simp [C, hL, hP, hF]
    · have hi0 : i ≠ 0 := by omega
      have hi1 : i ≠ 1 := by omega
      have hi2 : i ≠ 2 := by omega
      have hi3 : i ≠ 3 := by omega
      have he : C i = ⊤ := by simp [C, hi0, hi1, hi2, hi3]
      rw [he, finrank_top, dimension, Nat.min_eq_right (by omega : 4 ≤ i)]
  obtain ⟨b, hb⟩ := Theory.AlgebraicGroup.exists_basis_adapted_to_full_submodule_chain C hm hd
  let b' := b.reindex (finCongr dimension)
  refine ⟨b', ?_, ?_, ?_⟩
  · simpa [C, b', Module.Basis.reindex_apply] using hb 1 (by rw [dimension]; decide)
  · simpa [C, b', Module.Basis.reindex_apply] using hb 2 (by rw [dimension]; decide)
  · simpa [C, b', Module.Basis.reindex_apply] using hb 3 (by rw [dimension]; decide)


private def coordPrefix (n : ℕ) (hn : n ≤ 4) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) (Set.range fun i : Fin n => (Pi.single (Fin.castLE hn i) 1 : V))

private theorem line_prefix : line = coordPrefix 1 (by decide) := by
  simp [line, coordPrefix, Set.range_unique]

private theorem plane_prefix : plane = coordPrefix 2 (by decide) := by
  apply le_antisymm
  · intro v hv
    have he : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 := by
      ext i
      fin_cases i <;> simp [show v 2 = 0 from hv.1, show v 3 = 0 from hv.2]
    rw [he]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    fin_cases i <;> constructor <;> simp

private theorem hyperplane_prefix : hyperplane = coordPrefix 3 (by decide) := by
  apply le_antisymm
  · intro v hv
    have he : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 2 • Pi.single 2 1 := by
      ext i
      fin_cases i <;> simp [show v 3 = 0 from hv]
    rw [he]
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    fin_cases i <;> change _ = 0 <;> simp

private theorem map_prefix (b : Module.Basis (Fin 4) (ZMod 2) V) (n : ℕ) (hn : n ≤ 4) :
    (coordPrefix n hn).map b.equivFun.symm.toLinearMap =
      Submodule.span (ZMod 2) (Set.range fun i : Fin n => b (Fin.castLE hn i)) := by
  have hb (i : Fin 4) : b.equivFun.symm (Pi.single i 1) = b i := by
    simp [Module.Basis.equivFun_symm_apply]
  rw [coordPrefix, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (hb _).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Pi.single (Fin.castLE hn i) 1, ⟨i, rfl⟩, hb _⟩

/-- Every incident 1,2,3 flag is the image of the standard coordinate flag. -/
theorem exists_flag_equiv (L P F : Submodule (ZMod 2) V)
    (hLP : L ≤ P) (hPF : P ≤ F)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hF : Module.finrank (ZMod 2) F = 3) :
    ∃ e : BinaryLinear.GL V, line.map e.toLinearMap = L ∧
      plane.map e.toLinearMap = P ∧ hyperplane.map e.toLinearMap = F := by
  obtain ⟨b, hLb, hPb, hFb⟩ := exists_adapted_basis L P F hLP hPF hL hP hF
  refine ⟨b.equivFun.symm, ?_, ?_, ?_⟩
  · rw [line_prefix, map_prefix, ← hLb]
  · rw [plane_prefix, map_prefix, ← hPb]
  · rw [hyperplane_prefix, map_prefix, ← hFb]

/-- Linear conjugation transports the actual geometric stabilizer. -/
theorem parabolic_map_conj (e : BinaryLinear.GL V) (W : Submodule (ZMod 2) V) :
    (parabolic W).map (MulAut.conj e).toMonoidHom = parabolic (W.map e.toLinearMap) := by
  ext x
  rw [Subgroup.mem_map_equiv]
  change (∀ v, (MulAut.conj e).symm x v ∈ W ↔ v ∈ W) ↔
    (∀ v, x v ∈ W.map e.toLinearMap ↔ v ∈ W.map e.toLinearMap)
  simp_rw [Submodule.mem_map_equiv]
  constructor
  · intro hx v
    have h := hx (e.symm v)
    simpa only [MulAut.conj_symm_apply, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using h
  · intro hx v
    have h := hx (e v)
    simpa only [MulAut.conj_symm_apply, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using h

/-- The adapted linear equivalence identifies both parabolics simultaneously. -/
theorem exists_flag_conjugation (L P F : Submodule (ZMod 2) V)
    (hLP : L ≤ P) (hPF : P ≤ F)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hF : Module.finrank (ZMod 2) F = 3) :
    ∃ e : BinaryLinear.GL V,
      (middle line hyperplane).map (MulAut.conj e).toMonoidHom = middle L F ∧
      (borel line plane hyperplane).map (MulAut.conj e).toMonoidHom = borel L P F := by
  obtain ⟨e, heL, heP, heF⟩ := exists_flag_equiv L P F hLP hPF hL hP hF
  refine ⟨e, ?_, ?_⟩
  · rw [middle, Subgroup.map_inf _ _ _ (MulAut.conj e).injective,
      parabolic_map_conj, parabolic_map_conj, heL, heF]
    rfl
  · simp only [borel, middle]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj e).injective,
      Subgroup.map_inf _ _ _ (MulAut.conj e).injective,
      parabolic_map_conj, parabolic_map_conj, parabolic_map_conj, heL, heP, heF]

end BinaryLinear.MiddleParabolic

end
