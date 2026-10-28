module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DecompositionConsequences
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.OrthogonalPair.Carrier
public import Theory.Representation.BinaryOffender.CubicMovedRank
public import Theory.Representation.CyclicFixedRank

/-!
# Rank-two cubics in the ordinary internal factors

Every ordinary factor in the genuine internal decomposition of G.9.2
contains a cubic moving exactly a plane of the full binary module. In the
symmetric-three case, faithfulness gives the lower bound and the prescribed
two-dimensional moved space gives the upper bound. For the natural split
orthogonal four-space, the diagonal cubic in its two dihedral factors fixes
four of the sixteen vectors, hence moves a plane. Distinct internal factors
fix the other summands, so restriction to the factor's own moved space does
not alter the displacement rank.

This supplies the ordinary-factor cubic used in the five-core argument of
Aschbacher--Smith G.9.4, printed pp.354--355 (combined manuscript, 1 March
2004), using the marked natural action from G.9.2. The orthogonal coordinates
come from the licensed ATLAS port through the imported carrier module.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.FiveCore
open NilpotentRigidity ClassicalOrthogonal.BinaryD2

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
private theorem range_le_moved (ρ : Representation (ZMod 2) G V)
    (K : Subgroup G) (g : K) : LinearMap.range (ρ g - LinearMap.id) ≤ movedSpace ρ K := by
  rintro _ ⟨v, rfl⟩
  exact Representation.Coinvariants.sub_mem_ker (ρ := ρ.comp K.subtype) g v

private theorem symmetric_three_cubic (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (K : Subgroup G)
    (e : K ≃* Equiv.Perm (Fin 3))
    (hd : Module.finrank (ZMod 2) (movedSpace ρ K) = 2) :
    ∃ g : K, (g : G)^3 = 1 ∧
      Module.finrank (ZMod 2) (LinearMap.range (ρ (g : G) - LinearMap.id)) = 2 := by
  obtain ⟨c, hc, hc1⟩ : ∃ c : Equiv.Perm (Fin 3), c ^ 3 = 1 ∧ c ≠ 1 := by
    decide +kernel
  let g := e.symm c
  have hg3 : g ^ 3 = 1 := by simp only [g, ← map_pow, hc, map_one]
  have hg1 : g ≠ 1 := by
    intro h
    apply hc1
    have he := congrArg e h
    simpa only [g, e.apply_symm_apply, map_one] using he
  have hga3 : (g : G) ^ 3 = 1 := congrArg Subtype.val hg3
  have hga1 : (g : G) ≠ 1 := fun h => hg1 (Subtype.ext h)
  refine ⟨g, hga3, le_antisymm ?_ ?_⟩
  · simpa only [hd] using Submodule.finrank_mono (range_le_moved ρ K g)
  · have ho : orderOf (g : G) = 3 := orderOf_eq_prime hga3 hga1
    have hb := Representation.BinaryOffender.two_le_finrank_subspaceCommutator_of_card_three
      ρ (zpowers (g : G)) hf (by rw [Nat.card_zpowers, ho])
    rwa [Representation.CyclicFixedRank.commutator_eq_range] at hb

omit [FiniteDimensional (ZMod 2) V] in
private theorem internal_range (ρ : Representation (ZMod 2) G V)
    {H : Subgroup G} {r : ℕ} (d : InternalDecomposition ρ H r)
    (i : Fin r) (g : d.factor i) :
    LinearMap.range (ρ (g : G) - LinearMap.id) =
      LinearMap.range ((ρ (g : G) - LinearMap.id).comp (movedSpace ρ (d.factor i)).subtype) := by
  classical
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    obtain ⟨w, rfl⟩ := d.spaceEquiv.surjective v
    refine ⟨w i, ?_⟩
    change (ρ (g : G) - LinearMap.id : Module.End (ZMod 2) V) (w i : V) =
      (ρ (g : G) - LinearMap.id : Module.End (ZMod 2) V) (d.spaceEquiv w)
    conv_rhs => rw [← Finset.univ_sum_single w, map_sum, map_sum]
    rw [Finset.sum_eq_single i]
    · rw [d.space_inclusion]
    · intro j _ hji
      rw [d.space_inclusion]
      change ρ g (w j) - (w j : V) = 0
      rw [d.cross_fix (Ne.symm hji) g (w j), sub_self]
    · simp
  · exact LinearMap.range_comp_le_range _ _

private def diagonal : Pair := (DihedralGroup.r 1, DihedralGroup.r 1)

private def diagonalDisplacement : Module.End (ZMod 2) Space :=
  (pairHom diagonal).val.toLinearMap - LinearMap.id

private theorem diagonal_cube : diagonal ^ 3 = 1 := by decide +kernel

private theorem diagonal_rank : Module.finrank (ZMod 2) diagonalDisplacement.range = 2 := by
  have hc : Nat.card {x : Space // (pairHom diagonal).val x = x} = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  let e : diagonalDisplacement.ker ≃ {x : Space // (pairHom diagonal).val x = x} :=
    Equiv.subtypeEquivRight (fun x => by
      change (pairHom diagonal).val x - x = 0 ↔ (pairHom diagonal).val x = x
      exact sub_eq_zero)
  have hker : Nat.card diagonalDisplacement.ker = 4 := (Nat.card_congr e).trans hc
  have hp := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := diagonalDisplacement.ker)
  rw [Nat.card_zmod, hker] at hp
  have hk : Module.finrank (ZMod 2) diagonalDisplacement.ker = 2 :=
    Nat.pow_right_injective (by decide : 2 ≤ 2) hp.symm
  have hh := diagonalDisplacement.finrank_range_add_finrank_ker
  have hspace : Module.finrank (ZMod 2) Space = 4 := by
    simp [Space, ClassicalOrthogonal.VectorD, ClassicalOrthogonal.Index,
      Module.finrank_fintype_fun_eq_card]
  omega

omit [FiniteDimensional (ZMod 2) V] in
private theorem omega_four_cubic (ρ : Representation (ZMod 2) G V)
    {H : Subgroup G} {r : ℕ} (d : InternalDecomposition ρ H r)
    (i : Fin r) (hn : IsNaturalOmegaFour ρ (d.factor i) (movedSpace ρ (d.factor i))) :
    ∃ g : d.factor i, (g : G)^3 = 1 ∧
      Module.finrank (ZMod 2) (LinearMap.range (ρ (g : G) - LinearMap.id)) = 2 := by
  obtain ⟨e, f, ha⟩ := hn
  let g := e.symm (pairEquiv diagonal)
  have hg3 : g ^ 3 = 1 := by simp only [g, ← map_pow, diagonal_cube, map_one]
  refine ⟨g, congrArg Subtype.val hg3, ?_⟩
  let U := movedSpace ρ (d.factor i)
  have hmap : (ρ (g : G) - LinearMap.id).comp U.subtype =
      U.subtype.comp (f.symm.toLinearMap.comp (diagonalDisplacement.comp f.toLinearMap)) := by
    ext v
    change ρ g v - (v : V) =
      (f.symm ((pairHom diagonal).val (f v) - f v) : V)
    rw [map_sub, Submodule.coe_sub, f.symm_apply_apply]
    congr 1
    simpa only [g, e.apply_symm_apply, pairEquiv_apply] using ha g v
  rw [internal_range ρ d i g, hmap, LinearMap.range_comp, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top _ f.range,
    Submodule.finrank_map_subtype_eq, LinearEquiv.finrank_map_eq, diagonal_rank]

/-- Each ordinary internal factor supplies a cubic of displacement rank two
on the original full module. No extra model-action premise is needed. -/
theorem ordinary_factor_rank_two_cubic (ρ : Representation (ZMod 2) G V)
    (hfaith : Function.Injective ρ) {H : Subgroup G} {r : ℕ}
    (d : InternalDecomposition ρ H r) (i : Fin r)
    (ho : IsOrdinaryFactor ρ (d.factor i)) :
    ∃ g : d.factor i, (g : G)^3 = 1 ∧
      Module.finrank (ZMod 2) (LinearMap.range (ρ (g : G) - LinearMap.id)) = 2 := by
  rcases ho with ⟨⟨e⟩, hd⟩ | ⟨hn, _⟩
  · exact symmetric_three_cubic ρ hfaith (d.factor i) e hd
  · exact omega_four_cubic ρ d i hn

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.FiveCore
