module

public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Reconstructing binary flags from their stabilizers

The proper nonzero invariant subspaces of a full binary flag stabilizer are
exactly its cuts. Choose the last coordinate occurring in an invariant
subspace; upper transvections force all earlier basis vectors into it.
Adjacent swaps then detect exactly the retained cuts of any partial flag.
Consequently, containment of a full flag aligns all retained cuts by dimension,
and inner automorphisms preserving the full flag fix every partial flag.

These are the intrinsic flag calculations behind Aschbacher–Smith 13.8.25,
printed pp.959–960 of `refs/quasithin.pdf`. The cut dimensions and adjacent-swap
argument adapt the existing Chapter 15 `ParabolicIdentification.Linear.Flags`
proofs to the independently published Theory definitions, without upward imports.
-/

@[expose] public section

open Subgroup
namespace BinaryLinear.InvariantNodeActions
open OuterCyclic

theorem basis_mem_cutSpace {m : ℕ} (b : Basis m) (i : Fin m) (j : Fin (m + 1)) :
    b j ∈ cutSpace b i ↔ j.val ≤ i.val := b.self_mem_span_image

theorem cutSpace_mono {m : ℕ} (b : Basis m) : Monotone (cutSpace b) := by
  intro i j hij
  apply Submodule.span_mono
  exact Set.image_mono (fun _ hk => Nat.le_trans hk hij)

theorem cutSpace_finrank {m : ℕ} (b : Basis m) (i : Fin m) :
    Module.finrank (ZMod 2) (cutSpace b i) = i.val + 1 := by
  classical
  have he : b '' {j : Fin (m + 1) | j.val ≤ i.val} =
      Set.range (fun j : {j : Fin (m + 1) // j.val ≤ i.val} => b j.val) := by
    ext x
    simp
  have hlin : LinearIndependent (ZMod 2)
      (fun j : {j : Fin (m + 1) // j.val ≤ i.val} => b j.val) :=
    b.linearIndependent.comp _ Subtype.val_injective
  let e : {j : Fin (m + 1) // j.val ≤ i.val} ≃ Fin (i.val + 1) :=
    { toFun := fun j => ⟨j.val.val, by omega⟩
      invFun := fun j => ⟨⟨j.val, by have := i.isLt; omega⟩, by change j.val ≤ i.val; have := j.isLt; omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [cutSpace, he, finrank_span_eq_card hlin, Fintype.card_congr e, Fintype.card_fin]

theorem mem_cutStabilizer_maps {m : ℕ} (b : Basis m) (cuts : Set (Fin m))
    (g : LinearGroup (m + 1)) :
    g ∈ cutStabilizer b cuts ↔
      ∀ i ∈ cuts, ∀ v ∈ cutSpace b i, g v ∈ cutSpace b i := by
  rw [mem_cutStabilizer]
  constructor
  · exact fun h i hi v hv => (h i hi v).mpr hv
  · intro h i hi v
    refine ⟨?_, h i hi v⟩
    intro hv
    let f : cutSpace b i → cutSpace b i := fun w => ⟨g w, h i hi w w.property⟩
    have hf : Function.Injective f := fun x y hxy =>
      Subtype.ext (g.injective (congrArg Subtype.val hxy))
    obtain ⟨w, hw⟩ := (Finite.surjective_of_injective hf) ⟨g v, hv⟩
    exact (g.injective (congrArg Subtype.val hw)) ▸ w.property

private noncomputable def swapCut {m : ℕ} (b : Basis m) (i : Fin m) :
    LinearGroup (m + 1) := b.equiv b (Equiv.swap i.castSucc i.succ)

private theorem swapCut_mem {m : ℕ} (b : Basis m) (cuts : Set (Fin m)) (i : Fin m) :
    swapCut b i ∈ cutStabilizer b cuts ↔ i ∉ cuts := by
  classical
  constructor
  · intro h hi
    have hv := ((mem_cutStabilizer b cuts _).mp h i hi (b i.castSucc)).mpr
      ((basis_mem_cutSpace b i _).mpr le_rfl)
    rw [swapCut, Module.Basis.equiv_apply, Equiv.swap_apply_left, basis_mem_cutSpace] at hv
    simp at hv
  · intro hi
    rw [mem_cutStabilizer_maps]
    intro j hj v hv
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    have hle : cutSpace b j ≤ (cutSpace b j).comap (swapCut b i).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      change swapCut b i (b k) ∈ cutSpace b j
      rw [swapCut, Module.Basis.equiv_apply, basis_mem_cutSpace]
      by_cases hki : k = i.castSucc
      · subst k
        rw [Equiv.swap_apply_left]
        simp only [Fin.val_succ]
        have : j.val ≠ i.val := fun h => hji (Fin.ext h)
        change i.val ≤ j.val at hk
        omega
      · by_cases hks : k = i.succ
        · subst k
          rw [Equiv.swap_apply_right]
          simp only [Fin.val_castSucc]
          change i.val + 1 ≤ j.val at hk
          omega
        · rw [Equiv.swap_apply_of_ne_of_ne hki hks]
          exact hk
    exact hle hv

theorem cutStabilizer_le_iff {m : ℕ} (b : Basis m) (s t : Set (Fin m)) :
    cutStabilizer b s ≤ cutStabilizer b t ↔ t ⊆ s := by
  constructor
  · intro h i hi
    by_contra hn
    exact ((swapCut_mem b t i).mp (h ((swapCut_mem b s i).mpr hn))) hi
  · intro h g hg
    rw [mem_cutStabilizer] at hg ⊢
    exact fun i hi => hg i (h hi)


theorem cutSpace_ne_bot {m : ℕ} (b : Basis m) (i : Fin m) :
    cutSpace b i ≠ ⊥ := by
  intro h
  have hd := cutSpace_finrank b i
  rw [h, finrank_bot] at hd
  omega

theorem cutSpace_ne_top {m : ℕ} (b : Basis m) (i : Fin m) :
    cutSpace b i ≠ ⊤ := by
  intro h
  have hd := cutSpace_finrank b i
  rw [h, finrank_top, Module.finrank_fin_fun] at hd
  have := i.isLt
  omega

private theorem lowerTransvection_mem {m : ℕ} (b : Basis m)
    (j k : Fin (m + 1)) (hjk : j < k) :
    transvection (b j) (b.coord k)
      (by simp [Module.Basis.coord_apply, ne_of_lt hjk]) ∈
        cutStabilizer b Set.univ := by
  rw [mem_cutStabilizer]
  intro i _ v
  change v + b.coord k v • b j ∈ cutSpace b i ↔ v ∈ cutSpace b i
  by_cases hji : j.val ≤ i.val
  · exact (cutSpace b i).add_mem_iff_left
      ((cutSpace b i).smul_mem _ ((basis_mem_cutSpace b i j).mpr hji))
  · have hk : ∀ w ∈ cutSpace b i, b.coord k w = 0 := by
      intro w hw
      change b.repr w k = 0
      by_contra hn
      have hh := b.mem_span_image.mp hw (Finsupp.mem_support_iff.mpr hn)
      change k.val ≤ i.val at hh
      change j.val < k.val at hjk
      omega
    constructor
    · intro hv
      have hv0 := hk _ hv
      have hkj : b.coord k (b j) = 0 := by
        simp [Module.Basis.coord_apply, ne_of_lt hjk]
      simp only [map_add, map_smul, hkj, smul_zero, add_zero] at hv0
      simpa only [hv0, zero_smul, add_zero] using hv
    · intro hv
      simpa only [hk v hv, zero_smul, add_zero] using hv

/-- The proper nonzero invariant subspaces of a full binary flag stabilizer
are precisely the cuts of that flag. -/
theorem fullFlag_invariant_subspace {m : ℕ} (b : Basis m)
    (W : Submodule (ZMod 2) (Space (m + 1))) (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤)
    (h : cutStabilizer b Set.univ ≤ parabolic W) :
    ∃ i : Fin m, W = cutSpace b i := by
  classical
  let s : Finset (Fin (m + 1)) :=
    Finset.univ.filter (fun k => ∃ w ∈ W, b.repr w k ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hex : ∃ k, b.repr w k ≠ 0 := by
      by_contra! hn
      apply hw0
      apply b.repr.injective
      ext k
      simpa using hn k
    obtain ⟨k, hk⟩ := hex
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hw, hk⟩⟩
  obtain ⟨k, hks, hkmax⟩ := s.exists_max_image Fin.val hs
  obtain ⟨w, hw, hwk⟩ := (Finset.mem_filter.mp hks).2
  have hmax (v) (hv : v ∈ W) (j) (hj : b.repr v j ≠ 0) : j.val ≤ k.val :=
    hkmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, hv, hj⟩)
  have hwk1 : b.repr w k = 1 :=
    (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hwk
  have hlower (j : Fin (m + 1)) (hj : j < k) : b j ∈ W := by
    have hv := (h (lowerTransvection_mem b j k hj) w).mpr hw
    change w + b.coord k w • b j ∈ W at hv
    rw [Module.Basis.coord_apply, hwk1, one_smul] at hv
    exact (W.add_mem_iff_right hw).mp hv
  have hkW : b k ∈ W := by
    have hsum : ∑ j ∈ Finset.univ.erase k, b.repr w j • b j ∈ W := by
      apply W.sum_mem
      intro j hj
      by_cases hc : b.repr w j = 0
      · simp only [hc, zero_smul, W.zero_mem]
      · apply W.smul_mem
        apply hlower
        have hne := (Finset.mem_erase.mp hj).1
        have hh := hmax w hw j hc
        exact lt_of_le_of_ne (show j ≤ k from hh) hne
    have he := b.sum_repr w
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), hwk1, one_smul] at he
    exact (W.add_mem_iff_right hsum).mp (he.symm ▸ hw)
  have hkm : k.val < m := by
    by_contra hn
    apply hW1
    apply (Submodule.eq_top_iff_forall_basis_mem b).mpr
    intro j
    rcases lt_or_eq_of_le (show j ≤ k from by have := j.isLt; omega) with hj | hj
    · exact hlower j hj
    · simpa only [hj] using hkW
  refine ⟨⟨k.val, hkm⟩, le_antisymm ?_ ?_⟩
  · intro v hv
    apply b.mem_span_image.mpr
    intro j hj
    exact hmax v hv j (Finsupp.mem_support_iff.mp hj)
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    rcases lt_or_eq_of_le (show j ≤ k from hj) with hlt | heq
    · exact hlower j hlt
    · change b j ∈ W
      rw [heq]
      exact hkW

/-- Reconstruction also detects exactly which cuts occur in a partial flag. -/
theorem cutStabilizer_le_parabolic_iff {m : ℕ} (b : Basis m) (cuts : Set (Fin m))
    (W : Submodule (ZMod 2) (Space (m + 1))) (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤) :
    cutStabilizer b cuts ≤ parabolic W ↔ ∃ i ∈ cuts, W = cutSpace b i := by
  constructor
  · intro h
    obtain ⟨i, rfl⟩ := fullFlag_invariant_subspace b W hW0 hW1
      (((cutStabilizer_le_iff _ _ _).mpr (Set.subset_univ _)).trans h)
    refine ⟨i, ?_, rfl⟩
    by_contra hi
    have hs := (swapCut_mem b cuts i).mpr hi
    have hv := (h hs (b i.castSucc)).mpr
      ((basis_mem_cutSpace b i _).mpr le_rfl)
    rw [swapCut, Module.Basis.equiv_apply, Equiv.swap_apply_left, basis_mem_cutSpace] at hv
    simp at hv
  · rintro ⟨i, hi, rfl⟩ g hg
    exact (mem_cutStabilizer b cuts g).mp hg i hi

theorem cutSpace_map {m : ℕ} (b : Basis m) (g : LinearGroup (m + 1)) (i : Fin m) :
    cutSpace (b.map g) i = (cutSpace b i).map g.toLinearMap := by
  rw [cutSpace, cutSpace, Submodule.map_span]
  congr 1
  ext v
  simp

theorem cutStabilizer_map_conj {m : ℕ} (b : Basis m) (cuts : Set (Fin m))
    (g : LinearGroup (m + 1)) :
    (cutStabilizer b cuts).map (MulAut.conj g).toMonoidHom =
      cutStabilizer (b.map g) cuts := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_cutStabilizer, mem_cutStabilizer]
  simp_rw [cutSpace_map, Submodule.mem_map_equiv]
  constructor
  · intro hx i hi v
    have h := hx i hi (g.symm v)
    simpa only [MulAut.conj_symm_apply, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using h
  · intro hx i hi v
    have h := hx i hi (g v)
    simpa only [MulAut.conj_symm_apply, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using h

/-- A full flag contained in a partial flag stabilizer identifies every
retained cut, including its original dimension. -/
theorem cutSpace_eq_of_fullFlag_le {m : ℕ} (b c : Basis m) (cuts : Set (Fin m))
    (h : cutStabilizer b Set.univ ≤ cutStabilizer c cuts) (i : Fin m) (hi : i ∈ cuts) :
    cutSpace c i = cutSpace b i := by
  have hsub : cutStabilizer b Set.univ ≤ parabolic (cutSpace c i) := by
    intro g hg
    exact (mem_cutStabilizer c cuts g).mp (h hg) i hi
  obtain ⟨j, hj⟩ := fullFlag_invariant_subspace b (cutSpace c i)
    (cutSpace_ne_bot c i) (cutSpace_ne_top c i) hsub
  have hd := congrArg (fun U : Submodule (ZMod 2) (Space (m + 1)) => Module.finrank (ZMod 2) U) hj
  rw [cutSpace_finrank, cutSpace_finrank] at hd
  have hji : j = i := Fin.ext (by omega)
  simpa only [hji] using hj

/-- A common full flag aligns the original node labels of two partial flags. -/
theorem cutStabilizer_eq_of_fullFlag_le {m : ℕ} (b c : Basis m) (cuts : Set (Fin m))
    (h : cutStabilizer b Set.univ ≤ cutStabilizer c cuts) :
    cutStabilizer c cuts = cutStabilizer b cuts := by
  ext g
  rw [mem_cutStabilizer, mem_cutStabilizer]
  constructor <;> intro hg i hi v
  · rw [← cutSpace_eq_of_fullFlag_le b c cuts h i hi]
    exact hg i hi v
  · rw [cutSpace_eq_of_fullFlag_le b c cuts h i hi]
    exact hg i hi v

/-- Inner automorphisms preserving a full binary flag fix every partial
flag stabilizer individually, with the given basis marking. -/
theorem inner_fixes_cutStabilizer {m : ℕ} (b : Basis m) (g : LinearGroup (m + 1))
    (h : (cutStabilizer b Set.univ).map (MulAut.conj g).toMonoidHom =
      cutStabilizer b Set.univ) (cuts : Set (Fin m)) :
    (cutStabilizer b cuts).map (MulAut.conj g).toMonoidHom = cutStabilizer b cuts := by
  rw [cutStabilizer_map_conj] at h ⊢
  apply cutStabilizer_eq_of_fullFlag_le
  rw [← h]
  exact (cutStabilizer_le_iff _ _ _).mpr (Set.subset_univ _)

theorem inner_fixes_minimalParabolic {m : ℕ} (b : Basis m) (g : LinearGroup (m + 1))
    (h : (cutStabilizer b Set.univ).map (MulAut.conj g).toMonoidHom =
      cutStabilizer b Set.univ) (i : Fin m) :
    (minimalParabolic b i).map (MulAut.conj g).toMonoidHom = minimalParabolic b i :=
  inner_fixes_cutStabilizer b g h {i}ᶜ

theorem minimalParabolic_injective {m : ℕ} (b : Basis m) :
    Function.Injective (minimalParabolic b) := by
  intro i j h
  apply Set.singleton_injective
  apply compl_injective
  apply Set.Subset.antisymm
  · exact (cutStabilizer_le_iff b {j}ᶜ {i}ᶜ).mp h.ge
  · exact (cutStabilizer_le_iff b {i}ᶜ {j}ᶜ).mp h.le

end BinaryLinear.InvariantNodeActions
