module

public import Theory.Representation.BinaryPermutationAlternatingActions
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Order.Preorder.Chain

/-!
# Structure of binary alternating permutation modules

In degree at least five, every alternating-invariant subspace of the full binary
permutation module is zero, the constant line, the augmentation core, or the full
module. The natural section is irreducible. In even degree these four spaces form
the unique maximal chain, and successive terms cover each other in the lattice
of subrepresentations; this is the unique chief series of the module.

The proof extracts a weight-two vector from any nonconstant vector by applying a
three-cycle and adding. Double transitivity then supplies every weight-two vector,
and these span the core. Dimensions classify the remaining possibilities. Pulling
subrepresentations back along the core's quotient map proves irreducibility of
the actual natural action.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), §B.3, Lemma B.3.1, printed p. 83.
-/

@[expose] public section

namespace BinaryPermutation
open Equiv
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

private lemma binary_add (x y : ZMod 2) (h : x ≠ y) : x + y = 1 := by
  revert x y; decide

private lemma binary_cases (x y z : ZMod 2) (h : x ≠ y) : z = x ∨ z = y := by
  revert x y z; decide

private lemma cycle_pair (W : Submodule (ZMod 2) (Full Ω))
    (hW : ∀ g : alternatingGroup Ω, ∀ v ∈ W, representation Ω g.val v ∈ W)
    {v : Full Ω} (hv : v ∈ W) {a b c : Ω}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hvab : v a ≠ v b) (hvbc : v b = v c) :
    Pi.single a (1 : ZMod 2) + Pi.single b 1 ∈ W := by
  let g : alternatingGroup Ω := ⟨swap a b * swap b c, by
    simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap hbc]⟩
  have heq : v + representation Ω g.val v = Pi.single a 1 + Pi.single b 1 := by
    ext i
    by_cases hi : i = a
    · subst i
      simp [g, Equiv.Perm.mul_def, hab, ← hvbc, binary_add _ _ hvab]
    by_cases hj : i = b
    · subst i
      simp [g, Equiv.Perm.mul_def, swap_apply_of_ne_of_ne hab hac,
        hab.symm, binary_add _ _ hvab.symm]
    by_cases hk : i = c
    · subst i
      simp [g, Equiv.Perm.mul_def, swap_apply_of_ne_of_ne hac.symm hbc.symm,
        hac.symm, hbc.symm, ← hvbc, CharTwo.add_self_eq_zero]
    · simp [g, Equiv.Perm.mul_def, swap_apply_of_ne_of_ne hi hj,
        swap_apply_of_ne_of_ne hj hk, hi, hj, CharTwo.add_self_eq_zero]
  rw [← heq]
  exact W.add_mem hv (hW g v hv)

private lemma pair_of_nonconstant (hn : 3 ≤ Fintype.card Ω)
    (W : Submodule (ZMod 2) (Full Ω))
    (hW : ∀ g : alternatingGroup Ω, ∀ v ∈ W, representation Ω g.val v ∈ W)
    {v : Full Ω} (hv : v ∈ W) {a b : Ω} (hab : v a ≠ v b) :
    Pi.single a (1 : ZMod 2) + Pi.single b 1 ∈ W := by
  have hab' : a ≠ b := fun h => hab (congrArg v h)
  have hc : ({a,b} : Finset Ω).card < (Finset.univ : Finset Ω).card := by
    have := Finset.card_le_two (a := a) (b := b)
    simpa only [Finset.card_univ] using (lt_of_le_of_lt this (by omega))
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  rcases binary_cases (v a) (v b) (v c) hab with heq | heq
  · simpa [add_comm] using cycle_pair W hW hv hab'.symm (Ne.symm hc.1) (Ne.symm hc.2)
      hab.symm heq.symm
  · exact cycle_pair W hW hv hab' (Ne.symm hc.2) (Ne.symm hc.1) hab heq.symm

omit [Fintype Ω] in
private lemma permute_single (g : Equiv.Perm Ω) (a : Ω) :
    representation Ω g (Pi.single a (1 : ZMod 2)) = Pi.single (g a) 1 := by
  ext i
  simp [Pi.single_apply, Equiv.symm_apply_eq]

private lemma all_pairs (hn : 4 ≤ Fintype.card Ω)
    (W : Submodule (ZMod 2) (Full Ω))
    (hW : ∀ g : alternatingGroup Ω, ∀ v ∈ W, representation Ω g.val v ∈ W)
    {a b : Ω} (hab : a ≠ b)
    (hp : Pi.single a (1 : ZMod 2) + Pi.single b 1 ∈ W) (i j : Ω) :
    Pi.single i (1 : ZMod 2) + Pi.single j 1 ∈ W := by
  by_cases hij : i = j
  · subst j
    convert W.zero_mem using 1
    ext k
    exact CharTwo.add_self_eq_zero _
  have := alternatingGroup.isMultiplyPretransitive Ω
  have ht : MulAction.IsMultiplyPretransitive (alternatingGroup Ω) Ω 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card Ω - 2)
      (by simpa only [Nat.card_eq_fintype_card] using (show 2 ≤ Fintype.card Ω - 2 by omega))
      (Nat.sub_le _ _)
  obtain ⟨g, ha, hb⟩ := (MulAction.is_two_pretransitive_iff.mp ht) hab hij
  have hg := hW g _ hp
  rw [map_add, permute_single, permute_single] at hg
  exact (show g.val a = i from ha) ▸ (show g.val b = j from hb) ▸ hg

private lemma core_le_of_pairs (W : Submodule (ZMod 2) (Full Ω)) (a : Ω)
    (hp : ∀ i j, Pi.single i (1 : ZMod 2) + Pi.single j 1 ∈ W) : core Ω ≤ W := by
  intro v hv
  have heq : (∑ i, v i • (Pi.single i (1 : ZMod 2) + Pi.single a 1)) = v := by
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
    have hsum : ∑ i, v i = 0 := hv
    rw [hsum, zero_smul, add_zero]
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using Finset.univ_sum_single v
  rw [← heq]
  exact W.sum_mem fun i _ => W.smul_mem _ (hp i a)

/-- Every invariant subspace either consists of constants or contains the core. -/
theorem invariant_le_constants_or_core_le (hn : 5 ≤ Fintype.card Ω)
    (W : Submodule (ZMod 2) (Full Ω))
    (hW : ∀ g : alternatingGroup Ω, ∀ v ∈ W, representation Ω g.val v ∈ W) :
    W ≤ constants Ω ∨ core Ω ≤ W := by
  classical
  by_cases h : ∀ v ∈ W, ∀ a b, v a = v b
  · left
    intro v hv
    have : Nonempty Ω := Fintype.card_pos_iff.mp (by omega)
    let a : Ω := Classical.choice inferInstance
    apply Submodule.mem_span_singleton.mpr
    exact ⟨v a, funext fun i => by simpa [allOne] using h v hv a i⟩
  · push Not at h
    obtain ⟨v, hv, a, b, hab⟩ := h
    right
    apply core_le_of_pairs W a
    exact all_pairs (by omega) W hW (fun h => hab (congrArg v h))
      (pair_of_nonconstant (by omega) W hW hv hab)

/-- The only alternating-invariant subspaces of the binary permutation module. -/
theorem invariant_submodule_classification (hn : 5 ≤ Fintype.card Ω)
    (W : Submodule (ZMod 2) (Full Ω))
    (hW : ∀ g : alternatingGroup Ω, ∀ v ∈ W, representation Ω g.val v ∈ W) :
    W = ⊥ ∨ W = constants Ω ∨ W = core Ω ∨ W = ⊤ := by
  have : Nonempty Ω := Fintype.card_pos_iff.mp (by omega)
  rcases invariant_le_constants_or_core_le hn W hW with h | h
  · by_cases hz : W = ⊥
    · exact Or.inl hz
    · right; left
      apply Submodule.eq_of_le_of_finrank_eq h
      have hle := Submodule.finrank_mono h
      have hne : Module.finrank (ZMod 2) W ≠ 0 :=
        fun heq => hz (Submodule.finrank_eq_zero.mp heq)
      rw [finrank_constants] at hle ⊢
      omega
  · by_cases heq : W = core Ω
    · exact Or.inr (Or.inr (Or.inl heq))
    · right; right; right
      apply Submodule.eq_of_le_of_finrank_eq le_top
      have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne h (Ne.symm heq))
      have hle := Submodule.finrank_mono (show W ≤ ⊤ from le_top)
      rw [finrank_core] at hlt
      rw [finrank_top, finrank_full] at hle ⊢
      omega

omit [DecidableEq Ω] in
/-- The core maps onto the natural section. -/
theorem coreToNatural_surjective : Function.Surjective (coreToNatural (Ω := Ω)) := by
  rintro ⟨v, u, hu, rfl⟩
  exact ⟨⟨u, hu⟩, rfl⟩

omit [DecidableEq Ω] in
/-- The quotient map intertwines the coordinate actions. -/
theorem coreToNatural_equivariant (g : Equiv.Perm Ω) (v : core Ω) :
    coreToNatural Ω (coreRepresentation Ω g v) =
      naturalRepresentation Ω g (coreToNatural Ω v) := by
  apply Subtype.ext
  rfl

/-- The alternating group is irreducible on the actual natural section. -/
theorem alternatingNatural_isIrreducible (hn : 5 ≤ Fintype.card Ω) :
    Representation.IsIrreducible (alternatingNaturalRepresentation (Ω := Ω)) := by
  have : Nonempty Ω := Fintype.card_pos_iff.mp (by omega)
  have hdim : 0 < Module.finrank (ZMod 2) (natural Ω) := by
    rcases Nat.even_or_odd (Fintype.card Ω) with h | h
    · rw [finrank_natural_even Ω h]; omega
    · rw [finrank_natural_odd Ω h]; omega
  have : Nontrivial (natural Ω) := Module.nontrivial_of_finrank_pos hdim
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro P
  let S := P.toSubmodule.comap (coreToNatural (Ω := Ω))
  let W := S.map (core Ω).subtype
  have hW : ∀ g : alternatingGroup Ω, ∀ v ∈ W, representation Ω g.val v ∈ W := by
    intro g v hv
    obtain ⟨u, hu, rfl⟩ := hv
    refine ⟨coreRepresentation Ω g.val u, ?_, rfl⟩
    change coreToNatural Ω (coreRepresentation Ω g.val u) ∈ P.toSubmodule
    rw [coreToNatural_equivariant]
    exact P.apply_mem_toSubmodule g hu
  rcases invariant_le_constants_or_core_le hn W hW with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨v, rfl⟩ := coreToNatural_surjective x
    have hv : v.val ∈ W := ⟨v, hx, rfl⟩
    have hz : coreToNatural Ω v = 0 := by
      apply Subtype.ext
      exact (Submodule.Quotient.mk_eq_zero (constants Ω)).mpr (h hv)
    exact hz
  · right
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm le_top
    intro x _
    obtain ⟨v, rfl⟩ := coreToNatural_surjective x
    obtain ⟨u, hu, huv⟩ := h v.property
    have huv' : u = v := Subtype.ext huv
    exact huv' ▸ hu

/-- The constant line as an alternating-group subrepresentation. -/
def constantsSubrepresentation : Subrepresentation (alternatingRepresentation (Ω := Ω)) :=
  ⟨constants Ω, fun g _ hv => constants_invariant Ω g.val hv⟩

/-- The core as an alternating-group subrepresentation. -/
def coreSubrepresentation : Subrepresentation (alternatingRepresentation (Ω := Ω)) :=
  ⟨core Ω, fun g _ hv => core_invariant Ω g.val hv⟩

/-- Classification in the lattice of genuine subrepresentations. -/
theorem alternating_subrepresentation_classification (hn : 5 ≤ Fintype.card Ω)
    (W : Subrepresentation (alternatingRepresentation (Ω := Ω))) :
    W = ⊥ ∨ W = constantsSubrepresentation ∨ W = coreSubrepresentation ∨ W = ⊤ := by
  rcases invariant_submodule_classification hn W.toSubmodule
    (fun g _ hv => W.apply_mem_toSubmodule g hv) with h | h | h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Or.inl (Subrepresentation.toSubmodule_injective h))
  · exact Or.inr (Or.inr (Or.inl (Subrepresentation.toSubmodule_injective h)))
  · exact Or.inr (Or.inr (Or.inr (Subrepresentation.toSubmodule_injective h)))

/-- In even degree the three nonzero terms form a strictly increasing chain. -/
theorem alternating_chiefSeries_strict (hn : 5 ≤ Fintype.card Ω)
    (heven : Even (Fintype.card Ω)) :
    (⊥ : Subrepresentation (alternatingRepresentation (Ω := Ω))) < constantsSubrepresentation ∧
      constantsSubrepresentation (Ω := Ω) < coreSubrepresentation ∧
      coreSubrepresentation (Ω := Ω) < ⊤ := by
  have : Nonempty Ω := Fintype.card_pos_iff.mp (by omega)
  have hc : (⊥ : Submodule (ZMod 2) (Full Ω)) < constants Ω := by
    apply bot_lt_iff_ne_bot.mpr
    intro h
    have hf := finrank_constants Ω
    rw [h, finrank_bot] at hf
    omega
  exact ⟨hc, constants_lt_core Ω heven (by omega), core_lt_top Ω⟩

/-- Every adjacent pair is a chief factor: there is no intermediate invariant space. -/
theorem alternating_chiefSeries_covers (hn : 5 ≤ Fintype.card Ω)
    (heven : Even (Fintype.card Ω)) :
    (⊥ : Subrepresentation (alternatingRepresentation (Ω := Ω))) ⋖ constantsSubrepresentation ∧
      constantsSubrepresentation (Ω := Ω) ⋖ coreSubrepresentation ∧
      coreSubrepresentation (Ω := Ω) ⋖ ⊤ := by
  obtain ⟨h₀, h₁, h₂⟩ := alternating_chiefSeries_strict hn heven
  refine ⟨⟨h₀, ?_⟩, ⟨h₁, ?_⟩, ⟨h₂, ?_⟩⟩ <;> intro W ha hb <;>
    rcases alternating_subrepresentation_classification hn W with rfl | rfl | rfl | rfl
  all_goals order

/-- In even degree the only maximal chain of invariant subspaces is
`0 < constants < core < Full`. This is the module's unique chief series. -/
theorem alternating_unique_chiefSeries (hn : 5 ≤ Fintype.card Ω)
    (heven : Even (Fintype.card Ω))
    (S : Set (Subrepresentation (alternatingRepresentation (Ω := Ω)))) :
    IsMaxChain (· ≤ ·) S ↔ S = {⊥, constantsSubrepresentation, coreSubrepresentation, ⊤} := by
  have hall : ({⊥, constantsSubrepresentation, coreSubrepresentation, ⊤} :
      Set (Subrepresentation (alternatingRepresentation (Ω := Ω)))) = Set.univ := by
    ext W
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true] using
      alternating_subrepresentation_classification hn W
  have htotal : IsChain (· ≤ ·)
      (Set.univ : Set (Subrepresentation (alternatingRepresentation (Ω := Ω)))) := by
    obtain ⟨h₀, h₁, h₂⟩ := alternating_chiefSeries_strict hn heven
    intro U _ V _ _
    rcases alternating_subrepresentation_classification hn U with rfl | rfl | rfl | rfl <;>
      rcases alternating_subrepresentation_classification hn V with rfl | rfl | rfl | rfl
    all_goals order
  rw [hall]
  constructor
  · intro h
    exact h.2 htotal (Set.subset_univ _)
  · rintro rfl
    exact ⟨htotal, fun _ _ h => Set.Subset.antisymm h (Set.subset_univ _)⟩
end BinaryPermutation
