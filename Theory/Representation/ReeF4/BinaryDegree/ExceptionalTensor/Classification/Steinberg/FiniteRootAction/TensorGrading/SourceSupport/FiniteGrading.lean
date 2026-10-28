module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.TensorGrading.SourceSupport.DegreeSpaces

/-!
# Finite degree support and primitive vectors modulo lower layers

For an independent integer grading of a finite-dimensional space, strictly
lowering operators whose common kernel lies in degree zero exclude negative
degrees. The degree-zero space is the common kernel, and finite support bounds
the filtration above. The homogeneous component in degree `k` also gives the
primitive test modulo degree `k-1`. The source application instantiates all
these data with actual coroot spaces and coordinate root coefficients.

Source: Steinberg (1963), Section 12; elementary graded linear algebra.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.SourceSupportTools
variable {F V I : Type*} [Field F] [AddCommGroup V] [Module F V]

@[expose] def filtration (H : ℤ → Submodule F V) (k : ℤ) : Submodule F V := ⨆ i ≤ k, H i

private theorem filtration_step (H : ℤ → Submodule F V) (k : ℤ) :
    filtration H k = filtration H (k-1) ⊔ H k := by
  apply le_antisymm
  · apply iSup_le
    intro i
    apply iSup_le
    intro hi
    rcases (show i ≤ k-1 ∨ i=k by omega) with h | rfl
    · apply le_trans _ le_sup_left
      exact (show H i ≤ filtration H (k-1) from le_iSup_of_le i (le_iSup_of_le h le_rfl))
    · exact le_sup_right
  · apply sup_le
    · apply iSup_le
      intro i
      apply iSup_le
      intro hi
      exact le_iSup_of_le i (le_iSup_of_le (by omega : i ≤ k) le_rfl)
    · exact le_iSup_of_le k (le_iSup_of_le le_rfl le_rfl)

private theorem disjoint_lower {H : ℤ → Submodule F V} (hH : iSupIndep H) (k : ℤ) :
    Disjoint (H k) (filtration H (k-1)) := by
  have h := hH.disjoint_biSup (x := k) (y := {i : ℤ | i ≤ k-1}) (by simp)
  simpa only [filtration, Set.mem_ofPred_eq] using h

private theorem lowers_filtration (H : ℤ → Submodule F V) (P : Module.End F V)
    (d : ℤ) (hP : ∀k x, x ∈ H k → P x ∈ H (k-d)) (k : ℤ) :
    (filtration H k).map P ≤ filtration H (k-d) := by
  rw [Submodule.map_le_iff_le_comap]
  apply iSup_le
  intro i
  apply iSup_le
  intro hi x hx
  have hl : H (i-d) ≤ filtration H (k-d) :=
    le_iSup_of_le (i-d) (le_iSup_of_le (by omega : i-d ≤ k-d) le_rfl)
  exact hl (hP i x hx)

theorem primitive_mod_lower {H : ℤ → Submodule F V} (hH : iSupIndep H)
    (P : I → Module.End F V) (d : I → ℤ)
    (hP : ∀i k x, x ∈ H k → P i x ∈ H (k-d i))
    (hker : ∀x, (∀i, P i x = 0) → x ∈ H 0)
    (k : ℤ) (hk : k ≠ 0) (x : V) (hx : x ∈ filtration H k)
    (hpx : ∀i, P i x ∈ filtration H (k-d i-1)) : x ∈ filtration H (k-1) := by
  rw [filtration_step] at hx
  obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
  have hkill (i : I) : P i b = 0 := by
    have hpa := lowers_filtration H (P i) (d i) (hP i) (k-1) (Submodule.mem_map_of_mem ha)
    have hpb : P i b ∈ filtration H (k-d i-1) := by
      have hp := hpx i
      rw [map_add] at hp
      have he : k-1-d i = k-d i-1 := by omega
      rw [he] at hpa
      simpa only [add_sub_cancel_left] using (filtration H (k-d i-1)).sub_mem hp hpa
    have hbot := (disjoint_lower hH (k-d i)).le_bot ⟨hP i k b hb, hpb⟩
    exact hbot
  have hb0 : b = 0 := (hH.pairwiseDisjoint hk).le_bot ⟨hb,hker b hkill⟩
  simpa only [hb0,add_zero] using ha

/-- A least occupied negative degree would be primitive, hence have degree zero. -/
theorem negative_eq_bot [FiniteDimensional F V]
    {H : ℤ → Submodule F V} (hH : iSupIndep H)
    (P : I → Module.End F V) (d : I → ℤ) (hd : ∀i, 0 < d i)
    (hP : ∀i k x, x ∈ H k → P i x ∈ H (k-d i))
    (hker : ∀x, (∀i, P i x = 0) → x ∈ H 0)
    {k : ℤ} (hk : k < 0) : H k = ⊥ := by
  classical
  by_contra hkn
  have hfin := Submodule.finite_ne_bot_of_iSupIndep hH
  have hnegfin : {j : ℤ | H j ≠ ⊥ ∧ j < 0}.Finite :=
    hfin.subset (by intro j hj; exact hj.1)
  obtain ⟨j, hj, hmin⟩ := Set.exists_min_image _ (fun j : ℤ => j) hnegfin ⟨k,hkn,hk⟩
  have hjneg : j < 0 := hj.2
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hj.1
  have hkill (i : I) : P i x = 0 := by
    have hbot : H (j-d i) = ⊥ := by
      by_contra hn
      have hh := hmin (j-d i) ⟨hn,by have := hd i; omega⟩
      have := hd i
      omega
    have hh := hP i j x hx
    simpa only [hbot,Submodule.mem_bot] using hh
  have he := (hH.pairwiseDisjoint (show j ≠ 0 by omega)).le_bot ⟨hx,hker x hkill⟩
  exact hx0 he

/-- Negative support vanishes and the primitive subspace gives degree zero. -/
theorem filtration_zero [FiniteDimensional F V]
    {H : ℤ → Submodule F V} (hH : iSupIndep H)
    (P : I → Module.End F V) (d : I → ℤ) (hd : ∀i, 0 < d i)
    (hP : ∀i k x, x ∈ H k → P i x ∈ H (k-d i))
    (L : Submodule F V) (hL : L ≤ H 0)
    (hker : ∀x, (∀i, P i x = 0) ↔ x ∈ L) : filtration H 0 = L := by
  have hker' : ∀x, (∀i, P i x = 0) → x ∈ H 0 := fun x hx => hL ((hker x).mp hx)
  apply le_antisymm
  · apply iSup_le
    intro k
    apply iSup_le
    intro hk
    rcases lt_or_eq_of_le hk with hk | rfl
    · rw [negative_eq_bot hH P d hd hP hker' hk]
      exact bot_le
    · intro x hx
      apply (hker x).mp
      intro i
      have hbot := negative_eq_bot hH P d hd hP hker' (show 0-d i < 0 by have := hd i; omega)
      simpa only [hbot,Submodule.mem_bot] using hP i 0 x hx
  · exact hL.trans (le_iSup_of_le 0 (le_iSup_of_le le_rfl le_rfl))

/-- Finitely many independent occupied degrees give a natural upper bound. -/
theorem filtration_exists_top [FiniteDimensional F V]
    {H : ℤ → Submodule F V} (hH : iSupIndep H) (htop : iSup H = ⊤) :
    ∃ N : ℕ, filtration H N = ⊤ := by
  have hfin := Submodule.finite_ne_bot_of_iSupIndep hH
  obtain ⟨M,hM⟩ := hfin.bddAbove
  refine ⟨M.toNat, top_unique ?_⟩
  rw [← htop]
  apply iSup_le
  intro k
  by_cases hk : H k = ⊥
  · rw [hk]
    exact bot_le
  · exact le_iSup_of_le k (le_iSup_of_le ((hM hk).trans (Int.self_le_toNat M)) le_rfl)

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.SourceSupportTools
