module

public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.InvariantSubspaces
public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.PairConjugacy
public import Mathlib.FieldTheory.Finiteness

/-!
# Invariant subspaces for an actual marked regular-dihedral pair

The pair's retained permutation conjugacy transports its actual square action
to the native model. The conjugating map is the established quadratic isometry,
so dimension, singularity, and faithfulness pass back to the original action.
-/

public noncomputable section
open Equiv Subgroup
namespace Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
open ClassicalOrthogonal SquareModule BinaryD3Comparison

private theorem action_conj (p g : P8) (v : D) :
    (symmetricEquiv ((MulAut.conj p) g)).val ((symmetricEquiv p).val v) =
      (symmetricEquiv p).val ((symmetricEquiv g).val v) := by
  simp [MulAut.conj_apply, map_mul, map_inv]

private theorem action_form (p : P8) (v : D) :
    formD 3 F ((symmetricEquiv p).val v) = formD 3 F v :=
  (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mp
    (symmetricEquiv p).property v

private theorem map_invariant (X : Subgroup P8) (S : Submodule F D)
    (hS : ∀ g ∈ X, ∀ v ∈ S, (symmetricEquiv g).val v ∈ S) (p : P8) :
    ∀ g ∈ X.map (MulAut.conj p).toMonoidHom,
      ∀ v ∈ S.map (symmetricEquiv p).val.toLinearMap,
        (symmetricEquiv g).val v ∈ S.map (symmetricEquiv p).val.toLinearMap := by
  rintro _ ⟨g, hg, rfl⟩ _ ⟨v, hv, rfl⟩
  exact ⟨(symmetricEquiv g).val v, hS g hg v hv, (action_conj p g v).symm⟩

private theorem card_eight_of_finrank (S : Submodule F D)
    (hr : Module.finrank F S = 3) : Nat.card S = 8 := by
  rw [Module.natCard_eq_pow_finrank (K := F), hr]
  norm_num [F]

variable {X : Subgroup P8} (hX : MaximalTwo X)
    (A B : Subgroup P8) (hAX : A ≤ X) (hBX : B ≤ X)
    (hTA : twoGroup ≤ A) (hTB : twoGroup ≤ B)
    (eA : A ≃* Perm (Fin 4)) (eB : B ≃* Perm (Fin 4)) (hne : A ≠ B)

include hX hAX hBX hTA hTB eA eB hne

/-- Every proper nonzero invariant subspace of the actual marked square action
has eight elements and is totally singular. -/
theorem marked_pair_invariant_card_singular (S : Submodule F D)
    (hS : ∀ g ∈ X, ∀ v ∈ S, (symmetricEquiv g).val v ∈ S)
    (h0 : S ≠ ⊥) (h1 : S ≠ ⊤) :
    Nat.card S = 8 ∧ ∀ v ∈ S, formD 3 F v = 0 := by
  obtain ⟨p, hp⟩ := marked_pair_conjugate hX A B hAX hBX hTA hTB eA eB hne
  let e := (symmetricEquiv p).val
  let U := S.map e.toLinearMap
  have hU : ∀ g ∈ modelGroup, ∀ v ∈ U, nativeAction g v ∈ U := by
    intro g hg v hv
    rw [nativeAction_eq]
    exact map_invariant X S hS p g (hp.symm ▸ hg) v hv
  have hU0 : U ≠ ⊥ := by simpa [U] using h0
  have hU1 : U ≠ ⊤ := by simpa [U] using h1
  obtain ⟨hr, hq⟩ := invariant_subspace_finrank_three_singular U hU hU0 hU1
  refine ⟨card_eight_of_finrank S ((e.finrank_map_eq S).symm.trans hr), ?_⟩
  intro v hv
  exact (action_form p v).symm.trans (hq (e v) ⟨v, hv, rfl⟩)

/-- The actual marked square action has an invariant singular three-space. -/
theorem marked_pair_exists_invariant_singular_plane :
    ∃ S : Submodule F D, Module.finrank F S = 3 ∧ Nat.card S = 8 ∧
      (∀ g ∈ X, ∀ v ∈ S, (symmetricEquiv g).val v ∈ S) ∧
      (∀ v ∈ S, formD 3 F v = 0) := by
  obtain ⟨p, hp⟩ := marked_pair_conjugate hX A B hAX hBX hTA hTB eA eB hne
  obtain ⟨U, hr, hU, hq⟩ := exists_model_invariant_singular_plane
  let e := (symmetricEquiv p).val
  let S := U.map e.symm.toLinearMap
  have hrS : Module.finrank F S = 3 := (e.symm.finrank_map_eq U).trans hr
  refine ⟨S, hrS, card_eight_of_finrank S hrS, ?_, ?_⟩
  · rintro g hg _ ⟨v, hv, rfl⟩
    have hcg : (MulAut.conj p) g ∈ modelGroup := by
      rw [← hp]
      exact ⟨g, hg, rfl⟩
    refine ⟨(symmetricEquiv ((MulAut.conj p) g)).val v, hU _ hcg v hv, ?_⟩
    apply e.injective
    change e (e.symm ((symmetricEquiv ((MulAut.conj p) g)).val v)) =
      e ((symmetricEquiv g).val (e.symm v))
    simpa only [e, LinearEquiv.apply_symm_apply] using action_conj p g (e.symm v)
  · rintro _ ⟨v, hv, rfl⟩
    have he := action_form p (e.symm v)
    change formD 3 F (e (e.symm v)) = formD 3 F (e.symm v) at he
    rw [e.apply_symm_apply] at he
    exact he.symm.trans (hq v hv)

/-- Restriction to any proper nonzero invariant subspace remains faithful. -/
theorem marked_pair_invariant_faithful (S : Submodule F D)
    (hS : ∀ g ∈ X, ∀ v ∈ S, (symmetricEquiv g).val v ∈ S)
    (h0 : S ≠ ⊥) (h1 : S ≠ ⊤) (g : P8) (hg : g ∈ X)
    (hfix : ∀ v ∈ S, (symmetricEquiv g).val v = v) : g = 1 := by
  obtain ⟨p, hp⟩ := marked_pair_conjugate hX A B hAX hBX hTA hTB eA eB hne
  let e := (symmetricEquiv p).val
  let U := S.map e.toLinearMap
  have hU : ∀ k ∈ modelGroup, ∀ v ∈ U, nativeAction k v ∈ U := by
    intro k hk v hv
    rw [nativeAction_eq]
    exact map_invariant X S hS p k (hp.symm ▸ hk) v hv
  have hU0 : U ≠ ⊥ := by simpa [U] using h0
  have hU1 : U ≠ ⊤ := by simpa [U] using h1
  have hcg : (MulAut.conj p) g ∈ modelGroup := by
    rw [← hp]
    exact ⟨g, hg, rfl⟩
  have hfixU : ∀ v ∈ U, nativeAction ((MulAut.conj p) g) v = v := by
    rintro _ ⟨v, hv, rfl⟩
    rw [nativeAction_eq]
    change (symmetricEquiv ((MulAut.conj p) g)).val ((symmetricEquiv p).val v) =
      (symmetricEquiv p).val v
    rw [action_conj, hfix v hv]
  have heq := invariant_subspace_faithful U hU hU0 hU1 _ hcg hfixU
  exact (MulAut.conj p).injective (heq.trans (map_one (MulAut.conj p)).symm)

end Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
