module

public import Theory.SpecificGroups.PSL3Three.FourNormalizer.Automorphisms

/-!
# Full automorphism normalizers of four-subgroups in PSL₃(3)

For the diagonal four, its normalizer in the full automorphism group is
exactly the centralizer of inverse transpose. Indeed every automorphism is
inner or inner times inverse transpose, and its inner factor normalizes the
four precisely when its conjugator is monomial, hence graph-fixed. The
proved graph-centralizer product gives C₂ × S₄ and order 48. Simultaneous
diagonalization then transports the count through literal inner-subgroup maps.

Source: Aschbacher--Smith, quasithin manuscript, Lemma 2.5.8(5), pp.556--557.
-/

public section
set_option backward.isDefEq.respectTransparency false
namespace Matrix.PSL3Three.FourGeometry
open Subgroup Matrix.PSL3.OuterSolvable
open GraphWitnesses.EightCentralizers GraphWitnesses.EightCentralizers.GraphModel
local notation "τ" => graph (ZMod 3)
private noncomputable abbrev D : Subgroup PSL := diagonalFour.map equiv.toMonoidHom

private theorem normalizer_D : normalizer (D : Set PSL) = (τ).fixedSubgroup := by
  rw [← map_equiv_normalizer_eq, normalizer_diagonalFour, graph_fixed_eq_monomial]
  change monomialSL.map equiv.toMonoidHom = monomialSL.map project
  congr 1
  ext x
  exact equiv_apply x

private theorem graph_fixes (x : PSL) (hx : x ∈ D) : τ x = x := by
  obtain ⟨s, ⟨i, rfl⟩, rfl⟩ := hx
  have h : ∀ i : Fin 4, graphSL (ZMod 3) (diagonalElement i) = diagonalElement i := by decide
  change τ (equiv (diagonalElement i)) = equiv (diagonalElement i)
  rw [equiv_apply]
  change project (graphSL (ZMod 3) (diagonalElement i)) = project (diagonalElement i)
  rw [h]

private theorem graph_map : D.map (τ).toMonoidHom = D := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change τ x ∈ D
    rw [graph_fixes x hx]
    exact hx
  · intro x hx
    exact ⟨x, hx, graph_fixes x hx⟩

private theorem inner_normalizes_iff (A : Subgroup PSL) (a : MulAut PSL) :
    a ∈ normalizer (A.map (MulAut.conj : PSL →* MulAut PSL) : Set (MulAut PSL)) ↔
      A.map a.toMonoidHom = A := by
  rw [mem_normalizer_iff_map_conj_eq]
  have he : (MulAut.conj a : MulAut PSL →* MulAut PSL).comp MulAut.conj =
      MulAut.conj.comp a.toMonoidHom := by
    ext x y
    simp
  rw [Subgroup.map_map, he, ← Subgroup.map_map]
  exact (Subgroup.map_injective (f := (MulAut.conj : PSL →* MulAut PSL))
    (MulAut.conj_injective_of_center_eq_bot psl_center_eq_bot)).eq_iff

private theorem commute_conj_graph_iff (x : PSL) :
    Commute (MulAut.conj x) τ ↔ τ x = x := by
  constructor
  · intro h
    apply MulAut.conj_injective_of_center_eq_bot psl_center_eq_bot
    have he : MulAut.conj (τ x) = τ * MulAut.conj x * τ⁻¹ := by ext y; simp
    rw [he, ← h.eq, mul_inv_cancel_right]
  · intro hx
    show MulAut.conj x * τ = τ * MulAut.conj x
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hx]

private theorem normalizer_inner_D :
    normalizer (D.map (MulAut.conj : PSL →* MulAut PSL) : Set (MulAut PSL)) =
      graphCentralizer := by
  ext a
  rw [inner_normalizes_iff]
  change D.map a.toMonoidHom = D ↔ a ∈ centralizer ({τ} : Set (MulAut PSL))
  rw [mem_centralizer_singleton_iff]
  obtain ⟨x, rfl | rfl⟩ := automorphism_inner_or_inner_graph a
  · change D.map (MulAut.conj x : PSL →* PSL) = D ↔ _
    rw [← mem_normalizer_iff_map_conj_eq, normalizer_D, MulAut.mem_fixedSubgroup]
    exact (commute_conj_graph_iff x).symm
  · have he : D.map (MulAut.conj x * τ).toMonoidHom = D.map (MulAut.conj x).toMonoidHom := by
      change D.map ((MulAut.conj x).toMonoidHom.comp (τ).toMonoidHom) = _
      rw [← Subgroup.map_map, graph_map]
    rw [he]
    change D.map (MulAut.conj x : PSL →* PSL) = D ↔ _
    rw [← mem_normalizer_iff_map_conj_eq, normalizer_D, MulAut.mem_fixedSubgroup]
    constructor
    · intro hx
      simpa only [mul_assoc] using congrArg (fun b : MulAut PSL => b * τ)
        ((commute_conj_graph_iff x).mpr hx).eq
    · intro hc
      apply (commute_conj_graph_iff x).mp
      exact mul_right_cancel (by simpa only [mul_assoc] using hc)

private theorem card_diagonal_fullNormalizer :
    Nat.card (normalizer (D.map (MulAut.conj : PSL →* MulAut PSL) : Set (MulAut PSL))) = 48 := by
  rw [normalizer_inner_D, Nat.card_congr graphCentralizerEquiv.toEquiv,
    Nat.card_prod, graphPowers_card]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

end Matrix.PSL3Three.FourGeometry

namespace Matrix.PSL3Three
open Subgroup FourGeometry

/-- The full automorphism normalizer of each actual inner four has order 48. -/
theorem card_four_fullNormalizer (F : Subgroup PSL)
    (hF : IsElementaryAbelian 2 F) (hc : Nat.card F = 4) :
    Nat.card (normalizer (F.map (MulAut.conj : PSL →* MulAut PSL) : Set (MulAut PSL))) = 48 := by
  let : IsElementaryAbelian 2 F := hF
  let A := F.map equiv.symm.toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map equiv.symm.toMonoidHom
  obtain ⟨g, hg⟩ := exists_conj_diagonalFour A
    (by rw [Subgroup.card_map_of_injective equiv.symm.injective, hc])
  let e : PSL ≃* PSL := (equiv.symm.trans (MulAut.conj g)).trans equiv
  have he : F.map e.toMonoidHom = diagonalFour.map equiv.toMonoidHom := by
    change F.map (equiv.toMonoidHom.comp
      ((MulAut.conj g).toMonoidHom.comp equiv.symm.toMonoidHom)) = _
    rw [← Subgroup.map_map, ← Subgroup.map_map, hg]
  have hi : (F.map (MulAut.conj : PSL →* MulAut PSL)).map (MulAut.congr e).toMonoidHom =
      (diagonalFour.map equiv.toMonoidHom).map (MulAut.conj : PSL →* MulAut PSL) := by
    rw [Subgroup.map_map]
    have hcomp : (MulAut.congr e).toMonoidHom.comp (MulAut.conj : PSL →* MulAut PSL) =
        (MulAut.conj : PSL →* MulAut PSL).comp e.toMonoidHom := by
      ext x y
      simp
    rw [hcomp, ← Subgroup.map_map, he]
  have hn := map_equiv_normalizer_eq (F.map (MulAut.conj : PSL →* MulAut PSL)) (MulAut.congr e)
  rw [hi] at hn
  have hh := congrArg (fun H : Subgroup (MulAut PSL) => Nat.card H) hn
  rw [Subgroup.card_map_of_injective (MulAut.congr e).injective] at hh
  exact hh.trans card_diagonal_fullNormalizer

/-- The full normalizer count on any carrier identified with the actual PSL₃(3). -/
theorem card_four_fullNormalizer_of_equiv {K : Type*} [Group K]
    (e : K ≃* PSL) (F : Subgroup K)
    (hF : IsElementaryAbelian 2 F) (hc : Nat.card F = 4) :
    Nat.card (normalizer (F.map (MulAut.conj : K →* MulAut K) : Set (MulAut K))) = 48 := by
  let : IsElementaryAbelian 2 F := hF
  have hi : (F.map (MulAut.conj : K →* MulAut K)).map (MulAut.congr e).toMonoidHom =
      (F.map e.toMonoidHom).map (MulAut.conj : PSL →* MulAut PSL) := by
    rw [Subgroup.map_map]
    have hcomp : (MulAut.congr e).toMonoidHom.comp (MulAut.conj : K →* MulAut K) =
        (MulAut.conj : PSL →* MulAut PSL).comp e.toMonoidHom := by
      ext x y
      simp
    rw [hcomp, Subgroup.map_map]
  have hn := map_equiv_normalizer_eq (F.map (MulAut.conj : K →* MulAut K)) (MulAut.congr e)
  rw [hi] at hn
  have hh := congrArg (fun H : Subgroup (MulAut PSL) => Nat.card H) hn
  rw [Subgroup.card_map_of_injective (MulAut.congr e).injective] at hh
  exact hh.trans (card_four_fullNormalizer (F.map e.toMonoidHom)
    (IsElementaryAbelian.map e.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective e.injective, hc]))

end Matrix.PSL3Three
