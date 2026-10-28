module

public import Theory.Representation.BinarySevenCode
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Theory.Representation.BinaryOffender.FixedSpaceSpan
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The binary seven-point action and fixed-space commutators

The even-word model is identified equivariantly with the natural binary
permutation module. Three standard even permutations fix exactly zero and
the words with supports `12`, `3456`, and `123456` (one-based notation).

For the groups `A1 = <(12),(34),(56)>` and
`A2 = <(12),(34)(56),(35)(46)>`, explicit vectors in element fixed spaces
produce respectively a weight-two commutator and a nonzero double
commutator. Equivariant transport retains the actual sum of element fixed
spaces and the actual commutator subspaces.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Lemmas 12.3.4 and 12.3.10, printed pp. 808–811.
The Sylow property and exhaustive subgroup/orbit classifications are
separate group-theoretic obligations, not assumptions hidden in these definitions.
-/

@[expose] public section

namespace BinarySevenCode
open Representation.BinaryOffender

theorem evenWords_eq_core : evenWords = BinaryPermutation.core (Fin 7) := by
  ext v
  rw [mem_evenWords_iff, BinaryPermutation.mem_core]

abbrev EvenWord := ↥evenWords

def evenRepresentation : Representation (ZMod 2) (Equiv.Perm (Fin 7)) EvenWord where
  toFun g := (BinaryPermutation.representation (Fin 7) g).restrict (by
    intro v hv
    rw [evenWords_eq_core] at hv ⊢
    exact BinaryPermutation.core_invariant (Fin 7) g hv)
  map_one' := by ext v i; rfl
  map_mul' g h := by ext v i; rfl

@[simp] theorem evenRepresentation_apply (g : Equiv.Perm (Fin 7)) (v : EvenWord)
    (i : Fin 7) : (evenRepresentation g v).val i = v.val (g.symm i) := rfl

theorem weight_evenRepresentation (g : Equiv.Perm (Fin 7)) (v : EvenWord) :
    weight (evenRepresentation g v).val = weight v.val := by
  unfold weight
  apply Finset.card_bij (fun i _ => g.symm i)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ h
    exact g.symm.injective h
  · intro j hj
    refine ⟨g j, ?_, g.symm_apply_apply j⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [evenRepresentation_apply, g.symm_apply_apply] using
      (Finset.mem_filter.mp hj).2

def evenWordsEquivCore : EvenWord ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 7) :=
  { toFun := fun v => ⟨v.val, evenWords_eq_core ▸ v.property⟩
    invFun := fun v => ⟨v.val, evenWords_eq_core.symm ▸ v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

noncomputable def evenWordsEquivNatural : EvenWord ≃ₗ[ZMod 2]
    BinaryPermutation.natural (Fin 7) :=
  evenWordsEquivCore.trans (BinaryPermutation.coreEquivNatural (Fin 7) (by decide))

theorem evenWordsEquivNatural_equivariant (g : Equiv.Perm (Fin 7)) (v : EvenWord) :
    evenWordsEquivNatural (evenRepresentation g v) =
      BinaryPermutation.naturalRepresentation (Fin 7) g (evenWordsEquivNatural v) := by
  exact BinaryPermutation.coreEquivNatural_equivariant (Fin 7) (by decide) g
    (evenWordsEquivCore v)

def e2 : EvenWord := ⟨![1, 1, 0, 0, 0, 0, 0], by rw [mem_evenWords_iff]; decide⟩
def e4 : EvenWord := ⟨![0, 0, 1, 1, 1, 1, 0], by rw [mem_evenWords_iff]; decide⟩
def e6 : EvenWord := ⟨![1, 1, 1, 1, 1, 1, 0], by rw [mem_evenWords_iff]; decide⟩

theorem representative_weights : weight e2.val = 2 ∧ weight e4.val = 4 ∧
    weight e6.val = 6 := by decide

theorem representative_nonzero : e2 ≠ 0 ∧ e4 ≠ 0 ∧ e6 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h
  · exact one_ne_zero (congrArg (fun v : EvenWord => v.val 0) h)
  · exact one_ne_zero (congrArg (fun v : EvenWord => v.val 2) h)
  · exact one_ne_zero (congrArg (fun v : EvenWord => v.val 0) h)

def swap12 : Equiv.Perm (Fin 7) := Equiv.swap 0 1
def swap34 : Equiv.Perm (Fin 7) := Equiv.swap 2 3
def swap56 : Equiv.Perm (Fin 7) := Equiv.swap 4 5
def kleinCross : Equiv.Perm (Fin 7) := Equiv.swap 2 4 * Equiv.swap 3 5

def A1 : Subgroup (Equiv.Perm (Fin 7)) :=
  Subgroup.closure {swap12, swap34, swap56}
def A2 : Subgroup (Equiv.Perm (Fin 7)) :=
  Subgroup.closure {swap12, swap34 * swap56, kleinCross}
def standardTwo : Subgroup (Equiv.Perm (Fin 7)) :=
  Subgroup.closure {swap12 * swap34, swap34 * swap56, kleinCross}

set_option maxRecDepth 4096 in
theorem standardTwo_fixed_iff (v : EvenWord) :
    v ∈ fixedSpace evenRepresentation standardTwo ↔
      v = 0 ∨ v = e2 ∨ v = e4 ∨ v = e6 := by
  rw [standardTwo, mem_fixedSpace_closure_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  have h : ∀ w : Word, (∑ i, w i = 0) →
      ((∀ i, w ((swap12 * swap34).symm i) = w i) ∧
       (∀ i, w ((swap34 * swap56).symm i) = w i) ∧
       (∀ i, w (kleinCross.symm i) = w i) ↔
        w = 0 ∨ w = e2.val ∨ w = e4.val ∨ w = e6.val) := by decide
  simpa only [Subtype.ext_iff, funext_iff, evenRepresentation_apply,
    ZeroMemClass.coe_zero] using
    h v.val ((mem_evenWords_iff _).mp v.property)

private def seed1 : EvenWord :=
  ⟨![1, 0, 1, 0, 0, 0, 0], by rw [mem_evenWords_iff]; decide⟩
private def seed2 : EvenWord :=
  ⟨![0, 0, 1, 0, 0, 0, 1], by rw [mem_evenWords_iff]; decide⟩

theorem e2_mem_commutator_fixedSpaceSpan_A1 :
    e2 ∈ subspaceCommutator evenRepresentation (fixedSpaceSpan evenRepresentation A1) A1 := by
  have hs : seed1 ∈ fixedSpaceSpan evenRepresentation A1 := by
    apply fixedSpace_le_fixedSpaceSpan evenRepresentation
      (show swap56 ∈ A1 from Subgroup.subset_closure (by simp)) (by decide)
    rw [mem_fixedSpace_zpowers_iff]
    apply Subtype.ext
    decide
  have he : evenRepresentation swap12 seed1 - seed1 = e2 := by
    apply Subtype.ext
    decide
  rw [← he]
  exact Submodule.subset_span ⟨swap12, Subgroup.subset_closure (by simp), seed1, hs, rfl⟩

theorem e4_mem_double_commutator_fixedSpaceSpan_A2 :
    e4 ∈ subspaceCommutator evenRepresentation
      (subspaceCommutator evenRepresentation (fixedSpaceSpan evenRepresentation A2) A2) A2 := by
  have hs : seed2 ∈ fixedSpaceSpan evenRepresentation A2 := by
    apply fixedSpace_le_fixedSpaceSpan evenRepresentation
      (show swap12 ∈ A2 from Subgroup.subset_closure (by simp)) (by decide)
    rw [mem_fixedSpace_zpowers_iff]
    apply Subtype.ext
    decide
  have hfirst : evenRepresentation (swap34 * swap56) seed2 - seed2 ∈
      subspaceCommutator evenRepresentation (fixedSpaceSpan evenRepresentation A2) A2 :=
    Submodule.subset_span ⟨swap34 * swap56, Subgroup.subset_closure (by simp), seed2, hs, rfl⟩
  have he : evenRepresentation kleinCross
      (evenRepresentation (swap34 * swap56) seed2 - seed2) -
      (evenRepresentation (swap34 * swap56) seed2 - seed2) = e4 := by
    apply Subtype.ext
    decide
  rw [← he]
  exact Submodule.subset_span ⟨kleinCross, Subgroup.subset_closure (by simp), _, hfirst, rfl⟩

section Transport
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) G V) (f : Equiv.Perm (Fin 7) →* G)
  (hf : Function.Injective f) (E : EvenWord ≃ₗ[ZMod 2] V)
  (hE : ∀ g v, E (evenRepresentation g v) = σ (f g) (E v))

include hE in
private theorem transport_commutator_mem (A : Subgroup (Equiv.Perm (Fin 7)))
    (U : Submodule (ZMod 2) EvenWord) (W : Submodule (ZMod 2) V)
    (hU : ∀ v ∈ U, E v ∈ W) :
    ∀ v ∈ subspaceCommutator evenRepresentation U A,
      E v ∈ subspaceCommutator σ W (A.map f) := by
  change subspaceCommutator evenRepresentation U A ≤
    (subspaceCommutator σ W (A.map f)).comap E.toLinearMap
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, v, hv, rfl⟩
  change E (evenRepresentation a v - v) ∈ subspaceCommutator σ W (A.map f)
  rw [map_sub, hE]
  exact Submodule.subset_span
    ⟨f a, Subgroup.mem_map_of_mem f ha, E v, hU v hv, rfl⟩

include hf hE

private theorem transport_fixedSpaceSpan_mem (A : Subgroup (Equiv.Perm (Fin 7)))
    {v : EvenWord} (hv : v ∈ fixedSpaceSpan evenRepresentation A) :
    E v ∈ fixedSpaceSpan σ (A.map f) := by
  rw [← fixedSpaceSpan_map_equivariant evenRepresentation σ f hf E hE A]
  exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩

theorem e2_mem_commutator_fixedSpaceSpan_transport :
    E e2 ∈ subspaceCommutator σ (fixedSpaceSpan σ (A1.map f)) (A1.map f) :=
  transport_commutator_mem σ f E hE A1 _ _
    (fun _ hv => transport_fixedSpaceSpan_mem σ f hf E hE A1 hv)
    e2 e2_mem_commutator_fixedSpaceSpan_A1

theorem e4_mem_double_commutator_fixedSpaceSpan_transport :
    E e4 ∈ subspaceCommutator σ
      (subspaceCommutator σ (fixedSpaceSpan σ (A2.map f)) (A2.map f)) (A2.map f) :=
  transport_commutator_mem σ f E hE A2 _ _
    (transport_commutator_mem σ f E hE A2 _ _
      (fun _ hv => transport_fixedSpaceSpan_mem σ f hf E hE A2 hv))
    e4 e4_mem_double_commutator_fixedSpaceSpan_A2

theorem commutator_fixedSpaceSpan_has_weight_two_transport :
    ∃ v ∈ subspaceCommutator σ (fixedSpaceSpan σ (A1.map f)) (A1.map f),
      v ≠ 0 ∧ weight (E.symm v).val = 2 := by
  refine ⟨E e2, e2_mem_commutator_fixedSpaceSpan_transport σ f hf E hE, ?_, ?_⟩
  · intro h
    exact representative_nonzero.1 (E.injective (h.trans E.map_zero.symm))
  · rw [E.symm_apply_apply]
    exact representative_weights.1

theorem double_commutator_fixedSpaceSpan_ne_bot_transport :
    subspaceCommutator σ
      (subspaceCommutator σ (fixedSpaceSpan σ (A2.map f)) (A2.map f)) (A2.map f) ≠ ⊥ := by
  intro h
  have hm := e4_mem_double_commutator_fixedSpaceSpan_transport σ f hf E hE
  rw [h, Submodule.mem_bot] at hm
  exact representative_nonzero.2.1 (E.injective (hm.trans E.map_zero.symm))
end Transport

end BinarySevenCode
