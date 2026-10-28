module

public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.InvariantSubspaceTransport
public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.UnfaithfulRecognition
import all Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.UnfaithfulRecognition

/-! Invariant square geometry on the actual action with kernel. The literal
Sylow conjugacy and local quotient maps yield the marked native pair; the
quadratic isometry then transports all conclusions back to the given action. -/

public noncomputable section
open Equiv Subgroup
namespace Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
open ClassicalOrthogonal SquareModule BinaryD3Comparison

private theorem action_conjugate (c g : P8) (v : D) :
    (symmetricEquiv ((MulAut.conj c) g)).val ((symmetricEquiv c).val v) =
      (symmetricEquiv c).val ((symmetricEquiv g).val v) := by
  simp [MulAut.conj_apply, map_mul, map_inv]

private theorem action_preserves_form (c : P8) (v : D) :
    formD 3 F ((symmetricEquiv c).val v) = formD 3 F v :=
  (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mp (symmetricEquiv c).property v

/-- Classification, existence, and restriction faithfulness for the original
square action, retaining its actual kernel and original local subgroups. -/
theorem unfaithful_pair_invariant_geometry
    {G : Type*} [Group G] [Finite G]
    (f : G →* P8) (S : Sylow 2 G) (c : P8)
    (hS : (S : Subgroup G).map ((MulAut.conj c).toMonoidHom.comp f) = twoGroup)
    (hker : f.ker ≤ (S : Subgroup G))
    (A B : Subgroup G) (hSA : (S : Subgroup G) ≤ A) (hSB : (S : Subgroup G) ≤ B)
    (qA : A →* Perm (Fin 4)) (hqA : Function.Surjective qA)
    (hkA : qA.ker = (f.comp A.subtype).ker)
    (qB : B →* Perm (Fin 4)) (hqB : Function.Surjective qB)
    (hkB : qB.ker = (f.comp B.subtype).ker) (hne : A ≠ B) :
    (∀ V : Submodule F D,
      (∀ g ∈ f.range, ∀ v ∈ V, (symmetricEquiv g).val v ∈ V) →
      V ≠ ⊥ → V ≠ ⊤ → Nat.card V = 8 ∧ ∀ v ∈ V, formD 3 F v = 0) ∧
    ∃ V : Submodule F D, Nat.card V = 8 ∧
      (∀ g ∈ f.range, ∀ v ∈ V, (symmetricEquiv g).val v ∈ V) ∧
      (∀ v ∈ V, formD 3 F v = 0) ∧
      (∀ g ∈ f.range, (∀ v ∈ V, (symmetricEquiv g).val v = v) → g = 1) := by
  let f' := (MulAut.conj c).toMonoidHom.comp f
  have hk' : f'.ker = f.ker :=
    MonoidHom.ker_comp_of_injective f (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
  have hker' : f'.ker ≤ (S : Subgroup G) := by rw [hk']; exact hker
  have hkA' : qA.ker = (f'.comp A.subtype).ker := by
    rw [show f'.comp A.subtype = (MulAut.conj c).toMonoidHom.comp (f.comp A.subtype) from rfl,
      MonoidHom.ker_comp_of_injective _ _ (MulAut.conj c).injective]
    exact hkA
  have hkB' : qB.ker = (f'.comp B.subtype).ker := by
    rw [show f'.comp B.subtype = (MulAut.conj c).toMonoidHom.comp (f.comp B.subtype) from rfl,
      MonoidHom.ker_comp_of_injective _ _ (MulAut.conj c).injective]
    exact hkB
  let T : Sylow 2 f'.range := S.mapSurjective f'.rangeRestrict_surjective
  have hT : (T : Subgroup f'.range).map f'.range.subtype = twoGroup := by
    change ((S : Subgroup G).map f'.rangeRestrict).map f'.range.subtype = twoGroup
    rw [map_map]
    exact hS
  have hX := maximalTwo_of_sylow f'.range T hT
  have hne' : A.map f' ≠ B.map f' := fun he => hne
    (map_injective_of_ker_le f' (hker'.trans hSA) (hker'.trans hSB) he)
  let eA := localImageEquiv f' A qA hqA hkA'
  let eB := localImageEquiv f' B qB hqB hkB'
  have hTA : twoGroup ≤ A.map f' := hS ▸ map_mono hSA
  have hTB : twoGroup ≤ B.map f' := hS ▸ map_mono hSB
  let e := (symmetricEquiv c).val
  have map_invariant (V : Submodule F D)
      (hV : ∀ g ∈ f.range, ∀ v ∈ V, (symmetricEquiv g).val v ∈ V) :
      ∀ g ∈ f'.range, ∀ v ∈ V.map e.toLinearMap,
        (symmetricEquiv g).val v ∈ V.map e.toLinearMap := by
    rintro _ ⟨y, rfl⟩ _ ⟨v, hv, rfl⟩
    exact ⟨(symmetricEquiv (f y)).val v, hV _ ⟨y, rfl⟩ v hv,
      (action_conjugate c (f y) v).symm⟩
  refine ⟨?_, ?_⟩
  · intro V hV h0 h1
    obtain ⟨hc, hq⟩ := marked_pair_invariant_card_singular hX (A.map f') (B.map f')
      (map_le_range _ _) (map_le_range _ _) hTA hTB eA eB hne'
      (V.map e.toLinearMap) (map_invariant V hV) (by simpa using h0) (by simpa using h1)
    refine ⟨?_, ?_⟩
    · exact (Nat.card_congr (e.submoduleMap V).toEquiv).trans hc
    · intro v hv
      exact (action_preserves_form c v).symm.trans (hq (e v) ⟨v, hv, rfl⟩)
  · obtain ⟨W, hr, hc, hW, hq⟩ := marked_pair_exists_invariant_singular_plane hX
      (A.map f') (B.map f') (map_le_range _ _) (map_le_range _ _) hTA hTB eA eB hne'
    have h0 : W ≠ ⊥ := by
      intro he
      rw [he, finrank_bot] at hr
      omega
    have h1 : W ≠ ⊤ := by
      intro he
      rw [he, finrank_top] at hr
      norm_num [D, VectorD, Index, Module.finrank_fintype_fun_eq_card] at hr
    let V := W.map e.symm.toLinearMap
    refine ⟨V, ?_, ?_, ?_, ?_⟩
    · exact (Nat.card_congr (e.symm.submoduleMap W).toEquiv).symm.trans hc
    · rintro g ⟨y, rfl⟩ _ ⟨v, hv, rfl⟩
      refine ⟨(symmetricEquiv (f' y)).val v, hW _ ⟨y, rfl⟩ v hv, ?_⟩
      apply e.injective
      change e (e.symm ((symmetricEquiv (f' y)).val v)) =
        e ((symmetricEquiv (f y)).val (e.symm v))
      simpa only [e, f', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        LinearEquiv.apply_symm_apply] using action_conjugate c (f y) (e.symm v)
    · rintro _ ⟨v, hv, rfl⟩
      have he := action_preserves_form c (e.symm v)
      change formD 3 F (e (e.symm v)) = formD 3 F (e.symm v) at he
      rw [e.apply_symm_apply] at he
      exact he.symm.trans (hq v hv)
    · rintro g ⟨y, rfl⟩ hfix
      have hf : ∀ v ∈ W, (symmetricEquiv (f' y)).val v = v := by
        intro v hv
        have hh := hfix (e.symm v) ⟨v, hv, rfl⟩
        have ha := action_conjugate c (f y) (e.symm v)
        change (symmetricEquiv (f' y)).val (e (e.symm v)) =
          e ((symmetricEquiv (f y)).val (e.symm v)) at ha
        rw [e.apply_symm_apply, hh, e.apply_symm_apply] at ha
        exact ha
      have hy := marked_pair_invariant_faithful hX (A.map f') (B.map f')
        (map_le_range _ _) (map_le_range _ _) hTA hTB eA eB hne' W hW h0 h1
        (f' y) ⟨y, rfl⟩ hf
      exact (MulAut.conj c).injective (hy.trans (map_one (MulAut.conj c)).symm)

end Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
