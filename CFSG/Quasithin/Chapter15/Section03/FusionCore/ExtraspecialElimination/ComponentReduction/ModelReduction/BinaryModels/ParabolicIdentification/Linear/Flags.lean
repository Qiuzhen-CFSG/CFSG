module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Local
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.Geometry
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Deleted nodes from index-three linear flag coordinates

An adjacent basis swap preserves every cut except its own. Thus containment
of the concrete flag stabilizers reverses and detects containment of their
sets of cuts. If the full-flag stabilizer has index three in a partial-flag
stabilizer, the prime-index formula forces exactly one cut to be absent.
The remaining actual subspaces form the chapter's nonempty flag, with its
precise dimensions and stabilizer transported through the supplied PSL model.

This is the geometric comparison step for Aschbacher–Smith 15.3.49(l),
combined manuscript (1 March 2004), printed pp.1143–1145. Existence of flag
coordinates for a Sylow overgroup is a separate input to this module.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
open Chapter2.ComponentRefinement.LieType.Binary
open Chapter1

abbrev Basis (m : ℕ) := Module.Basis (Fin (m + 1)) (ZMod 2) (Vector (m + 1))

noncomputable def cutSpace {m : ℕ} (b : Basis m) (i : Fin m) : Space (m + 1) :=
  Submodule.span (ZMod 2) (b '' {j : Fin (m + 1) | j.val ≤ i.val})

noncomputable def cutStabilizer {m : ℕ} (b : Basis m) (cuts : Set (Fin m)) :
    Subgroup (BinaryLinear.GL (Vector (m + 1))) :=
  ⨅ i ∈ cuts, BinaryLinear.parabolic (cutSpace b i)

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

theorem mem_cutStabilizer {m : ℕ} (b : Basis m) (cuts : Set (Fin m))
    (g : BinaryLinear.GL (Vector (m + 1))) :
    g ∈ cutStabilizer b cuts ↔ ∀ i ∈ cuts, ∀ v, g v ∈ cutSpace b i ↔ v ∈ cutSpace b i := by
  simp only [cutStabilizer, mem_iInf]
  rfl

private theorem mem_cutStabilizer_maps {m : ℕ} (b : Basis m) (cuts : Set (Fin m))
    (g : BinaryLinear.GL (Vector (m + 1))) :
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
    BinaryLinear.GL (Vector (m + 1)) := b.equiv b (Equiv.swap i.castSucc i.succ)

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

theorem cuts_eq_compl_singleton_of_index_three {m : ℕ} (b : Basis m)
    (cuts : Set (Fin m))
    (hindex : (cutStabilizer b Set.univ).relIndex (cutStabilizer b cuts) = 3) :
    ∃ i : Fin m, cuts = {i}ᶜ := by
  classical
  have hnot : cuts ≠ Set.univ := by
    intro he
    rw [he, relIndex_self] at hindex
    contradiction
  obtain ⟨i, hi⟩ : ∃ i : Fin m, i ∉ cuts := by
    by_contra h
    push Not at h
    exact hnot (Set.eq_univ_of_forall h)
  refine ⟨i, ?_⟩
  have hBC : cutStabilizer b Set.univ ≤ cutStabilizer b {i}ᶜ :=
    (cutStabilizer_le_iff _ _ _).mpr (Set.subset_univ _)
  have hCP : cutStabilizer b {i}ᶜ ≤ cutStabilizer b cuts :=
    (cutStabilizer_le_iff _ _ _).mpr (fun j hj => by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (show j ≠ i from fun he => hi (he ▸ hj)))
  have heq := relIndex_mul_relIndex _ _ _ hBC hCP
  -- The first factor cannot be one: the adjacent swap breaks precisely cut i.
  have hfirst : (cutStabilizer b Set.univ).relIndex (cutStabilizer b {i}ᶜ) ≠ 1 := by
    intro h
    have hsub := (cutStabilizer_le_iff b {i}ᶜ Set.univ).mp (relIndex_eq_one.mp h)
    have : i ∉ ({i}ᶜ : Set (Fin m)) := by simp
    exact this (hsub (Set.mem_univ i))
  have hsecond : (cutStabilizer b {i}ᶜ).relIndex (cutStabilizer b cuts) = 1 := by
    have hprime : ((cutStabilizer b Set.univ).relIndex (cutStabilizer b {i}ᶜ) *
        (cutStabilizer b {i}ᶜ).relIndex (cutStabilizer b cuts)).Prime := by
      rw [heq, hindex]
      exact Nat.prime_three
    rcases Nat.prime_mul_iff.mp hprime with h | h
    · exact h.2
    · exact (hfirst h.2).elim
  exact Set.Subset.antisymm ((cutStabilizer_le_iff _ _ _).mp hCP)
    ((cutStabilizer_le_iff _ _ _).mp (relIndex_eq_one.mp hsecond))

noncomputable def deletedFlag {m : ℕ} (hm : 2 ≤ m) (b : Basis m) (i : Fin m) :
    Flag (m + 1) where
  spaces := (Finset.univ.erase i).image (cutSpace b)
  nonempty := by
    classical
    have hc : 0 < (Finset.univ.erase i).card := by simp; omega
    exact (Finset.card_pos.mp hc).image _
  proper W hW := by
    classical
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hW
    constructor
    · intro he
      have hd := cutSpace_finrank b j
      rw [he, finrank_bot] at hd
      omega
    · intro he
      have hd := cutSpace_finrank b j
      rw [he, finrank_top, Module.finrank_fin_fun] at hd
      have := j.isLt
      omega
  chain W hW W' hW' := by
    classical
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hW'
    exact (le_total j k).imp (fun h => cutSpace_mono b h) (fun h => cutSpace_mono b h)

theorem deletedFlag_types {m : ℕ} (hm : 2 ≤ m) (b : Basis m) (i : Fin m) :
    (deletedFlag hm b i).types = ((Finset.range (m + 1)).erase 0).erase (i.val + 1) := by
  classical
  ext d
  simp only [Flag.types, deletedFlag, Finset.mem_image, Finset.mem_erase,
    Finset.mem_univ, and_true, Finset.mem_range]
  constructor
  · rintro ⟨W, ⟨j, hji, rfl⟩, hd⟩
    rw [cutSpace_finrank] at hd
    subst d
    have hj := j.isLt
    have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
    omega
  · rintro ⟨hdi, hd0, hd⟩
    have hdpos : 0 < d := by omega
    let j : Fin m := ⟨d - 1, by omega⟩
    refine ⟨cutSpace b j, ⟨j, ?_, rfl⟩, ?_⟩
    · intro hji
      have := congrArg Fin.val hji
      change d - 1 = i.val at this
      omega
    · rw [cutSpace_finrank]
      change d - 1 + 1 = d
      omega

theorem deletedFlag_stabilizer {K : Type*} [Group K] {L : Subgroup K}
    {m : ℕ} (e : L ≃* PSL (m + 1)) (hm : 2 ≤ m) (b : Basis m) (i : Fin m) :
    flagStabilizer e (deletedFlag hm b i) =
      (cutStabilizer b {i}ᶜ).comap (linearModel e).toMonoidHom := by
  classical
  ext g
  simp [mem_flagStabilizer, deletedFlag, Subgroup.mem_comap, mem_cutStabilizer]

/-- Equality in linear coordinates transports to the literal ambient subgroup. -/
theorem ambient_eq_of_linear_image {K : Type*} [Group K] {L P : Subgroup K}
    {n : ℕ} [NeZero n] (e : L ≃* PSL n) (hPL : P ≤ L) (F : Flag n)
    (hP : (P.subgroupOf L).map (linearModel e).toMonoidHom =
      (flagStabilizer e F).map (linearModel e).toMonoidHom) :
    P = ambientFlagStabilizer e F := by
  have he := Subgroup.map_injective (linearModel e).injective hP
  rw [ambientFlagStabilizer, ← he, Subgroup.map_subgroupOf_eq_of_le hPL]

/-- The prime-index argument constructs the deleted node from actual flag
coordinates and retains the supplied projective marking. -/
theorem position_of_coordinates {K : Type*} [Group K]
    {L P : Subgroup K} {m : ℕ} (hm : 2 ≤ m) (e : L ≃* PSL (m + 1))
    (hPL : P ≤ L) (b : Basis m) (cuts : Set (Fin m))
    (hP : (P.subgroupOf L).map (linearModel e).toMonoidHom = cutStabilizer b cuts)
    (hi : (cutStabilizer b Set.univ).relIndex (cutStabilizer b cuts) = 3) :
    ∃ pos : ModelExclusions.BinaryGeometry.Position L P (m + 1), pos.model = e := by
  obtain ⟨i, rfl⟩ := cuts_eq_compl_singleton_of_index_three b cuts hi
  refine ⟨⟨e, deletedFlag hm b i, i.val + 1, by omega, by have := i.isLt; omega,
    deletedFlag_types hm b i, ?_⟩, rfl⟩
  apply ambient_eq_of_linear_image e hPL
  rw [deletedFlag_stabilizer, Subgroup.map_comap_eq_self_of_surjective
    (linearModel e).surjective, hP]

theorem sylow_relIndex_eq {D : Type*} [Group D] [Finite D]
    (S T : Sylow 2 D) (P : Subgroup D) (hSP : (S : Subgroup D) ≤ P)
    (hTP : (T : Subgroup D) ≤ P) :
    (S : Subgroup D).relIndex P = (T : Subgroup D).relIndex P := by
  have hs := relIndex_mul_relIndex (⊥ : Subgroup D) S P bot_le hSP
  have ht := relIndex_mul_relIndex (⊥ : Subgroup D) T P bot_le hTP
  simp only [relIndex_bot_left] at hs ht
  have hc : Nat.card (S : Subgroup D) = Nat.card (T : Subgroup D) := by
    rw [S.card_eq_multiplicity, T.card_eq_multiplicity]
  rw [hc] at hs
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hs.trans ht.symm)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
