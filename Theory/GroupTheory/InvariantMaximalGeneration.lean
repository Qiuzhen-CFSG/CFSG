module

public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Generation from a maximal invariant subgroup modulo a centre

Let `G = E B`, with E perfect and normal, and let Z be a normal subgroup
centralizing E. If `K Z` is maximal among B-invariant subgroups of E and its
normalizer is contained in `Z K B`, then K B and any conjugate outside this
exceptional subgroup generate G. The proof saturates their intersection with
E by Z, applies invariant maximality, and removes Z using perfectness.

This is the subgroup-lattice argument in GLS2, Theorem 25.14, Step 2.
It does not require K B to be a maximal subgroup of G.
-/

@[expose] public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- Maximality in the lattice of A-invariant subgroups of E, with relative
properness recorded explicitly. -/
def IsMaximalInvariantIn (D E A : Subgroup G) : Prop :=
  D < E ∧ A ≤ normalizer (D : Set G) ∧
    ∀ M : Subgroup G, D ≤ M → M ≤ E → A ≤ normalizer (M : Set G) →
      M = D ∨ M = E

/-- A central supplement contributes nothing to the derived subgroup. -/
theorem commutator_eq_of_central_supplement {E J Z : Subgroup G}
    (hgen : J ⊔ Z = E) (hZ : Z ≤ centralizer (E : Set G)) :
    ⁅E, E⁆ = ⁅J, J⁆ := by
  have hJE : J ≤ E := hgen ▸ le_sup_left
  have hZJ : Z ≤ centralizer (J : Set G) := hZ.trans (centralizer_le hJE)
  calc
    ⁅E, E⁆ = ⁅E, J⁆ := (commutator_eq_of_centralizing_sup
      ((sup_comm Z J).trans hgen) hZ (hJE.trans E.le_normalizer)).symm
    _ = ⁅J, E⁆ := commutator_comm _ _
    _ = ⁅J, J⁆ := (commutator_eq_of_centralizing_sup
      ((sup_comm Z J).trans hgen) hZJ J.le_normalizer).symm

/-- The derived subgroup of a perfect-by-abelian subgroup is its perfect
normal factor. The normality here is only relative to the join. -/
theorem commutator_sup_eq_of_perfect_of_commutative {K B : Subgroup G}
    [Group.IsPerfect K] [IsMulCommutative B]
    (hBK : B ≤ normalizer (K : Set G)) : ⁅K ⊔ B, K ⊔ B⁆ = K := by
  let Y := K ⊔ B
  have hYK : Y ≤ normalizer (K : Set G) := sup_le K.le_normalizer hBK
  have hKB : ⁅K, B⁆ ≤ K := le_normalizer_iff_commutator_le_left.mp hBK
  have hBB : ⁅B, B⁆ ≤ K := by
    rw [commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr inferInstance)]
    exact bot_le
  have hYB : ⁅Y, B⁆ ≤ K := by
    have hpre : Y ≤ commutatorPreimage Y B K :=
      sup_le (le_commutatorPreimage le_sup_left hKB)
        (le_commutatorPreimage le_sup_right hBB)
    exact (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le Y B K hYK)
  have hKY : ⁅K, Y⁆ ≤ K := le_normalizer_iff_commutator_le_left.mp hYK
  have hpre : Y ≤ commutatorPreimage Y Y K :=
    sup_le (le_commutatorPreimage le_sup_left hKY)
      (le_commutatorPreimage le_sup_right ((commutator_comm B Y).trans_le hYB))
  apply le_antisymm
    ((commutator_mono hpre le_rfl).trans (commutator_commutatorPreimage_le Y Y K hYK))
  exact (commutator_eq_self (H := K)).symm.le.trans
    (commutator_mono le_sup_left le_sup_left)

/-- Normalizing a subgroup normalizes its derived subgroup. -/
theorem normalizer_le_normalizer_derived (Y : Subgroup G) :
    normalizer (Y : Set G) ≤ normalizer (⁅Y, Y⁆ : Subgroup G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp hg]

/-- The generation step uses invariant maximality inside E, rather than
maximality of the whole subgroup K B. -/
theorem conjugate_sup_eq_top_of_maximalInvariant [Finite G]
    {E K Z B : Subgroup G} [E.Normal] [Z.Normal] [Group.IsPerfect E]
    (hKE : K ≤ E) (hZE : Z ≤ E) (hZ : Z ≤ centralizer (E : Set G))
    (hgen : E ⊔ B = ⊤)
    (hmax : IsMaximalInvariantIn (K ⊔ Z) E B)
    (hN : normalizer (K ⊔ Z : Subgroup G) ≤ Z ⊔ (K ⊔ B))
    {x : G} (hx : x ∉ Z ⊔ (K ⊔ B)) :
    (K ⊔ B) ⊔ (K ⊔ B).map (MulAut.conj x⁻¹).toMonoidHom = ⊤ := by
  let Y := K ⊔ B
  let H := Y ⊔ Y.map (MulAut.conj x⁻¹).toMonoidHom
  let J := H ⊓ E
  let M := J ⊔ Z
  have hBH : B ≤ H := le_sup_right.trans le_sup_left
  have hKJ : K ≤ J := le_inf (le_sup_left.trans le_sup_left) hKE
  have hME : M ≤ E := sup_le inf_le_right hZE
  have hBM : B ≤ normalizer (M : Set G) := by
    have hBJ : B ≤ normalizer (J : Set G) :=
      (le_inf (hBH.trans H.le_normalizer) (le_normalizer_of_normal)).trans
        inf_normalizer_le_normalizer_inf
    exact (le_inf hBJ le_normalizer_of_normal).trans
      (normalizer_inf_normalizer_le_normalizer_sup J Z)
  have hDM : K ⊔ Z ≤ M := sup_le_sup_right hKJ Z
  rcases hmax.2.2 M hDM hME hBM with hMD | hMEq
  · have hKxJ : K.map (MulAut.conj x⁻¹).toMonoidHom ≤ J := by
      refine le_inf ((map_mono le_sup_left).trans le_sup_right) ?_
      exact (map_mono hKE).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp (show x⁻¹ ∈ normalizer (E : Set G) from
          le_normalizer_of_normal (mem_top _)))
    have hZmap : Z.map (MulAut.conj x⁻¹).toMonoidHom = Z :=
      mem_normalizer_iff_map_conj_eq.mp
        (show x⁻¹ ∈ normalizer (Z : Set G) from le_normalizer_of_normal (mem_top _))
    have hmap : (K ⊔ Z).map (MulAut.conj x⁻¹).toMonoidHom ≤ K ⊔ Z := by
      rw [map_sup, hZmap]
      exact sup_le ((hKxJ.trans le_sup_left).trans_eq hMD) le_sup_right
    have heq : (K ⊔ Z).map (MulAut.conj x⁻¹).toMonoidHom = K ⊔ Z :=
      eq_of_le_of_card_ge hmap (by
        rw [card_map_of_injective (MulAut.conj x⁻¹).injective])
    have hxi : x⁻¹ ∈ normalizer ((K ⊔ Z : Subgroup G) : Set G) :=
      mem_normalizer_iff_map_conj_eq.mpr heq
    have hxN : x ∈ normalizer ((K ⊔ Z : Subgroup G) : Set G) := by
      simpa only [inv_inv] using
        (normalizer ((K ⊔ Z : Subgroup G) : Set G)).inv_mem hxi
    exact (hx (hN hxN)).elim
  · have hEJ : E ≤ J := by
      have hc := commutator_eq_of_central_supplement hMEq hZ
      rw [commutator_eq_self] at hc
      exact hc.le.trans J.commutator_le_self
    apply top_unique
    rw [← hgen]
    exact sup_le (hEJ.trans inf_le_left) hBH

end Subgroup

end
