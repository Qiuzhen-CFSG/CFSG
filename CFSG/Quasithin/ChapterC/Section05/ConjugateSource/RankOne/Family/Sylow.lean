module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.QuotientAction
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.Normalizer
public import Theory.GroupTheory.SylowIndexTwoExtension

/-!
# The rank-one Sylow replacement in C.5.6(6)

The actual quotient family gives the index-two core stabilizer in
M₁=N_M(Φ(D)). The subgroup T₁=N_T(U) has half the order of the ambient
Sylow subgroup. Sylow extension inside M₁ therefore produces T₀ with
[T₀:T₁]=2. Its other coset normalizes T₁, squares into T₁, and still moves
U noncentrally. No splitting of the natural cover is used.

Source: Aschbacher–Smith C.5.6(6), printed pp.157–158.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R L : Subgroup G} {F : Type*} [Field F]

omit [Finite G] in
/-- The preceding block stabilizer normalizes the literal Frattini subgroup. -/
theorem block_normalizer_le_phi_normalizer (R L : Subgroup G) :
    normalizer (R : Set G) ⊓ normalizer (L : Set G) ≤ normalizer (Phi R L : Set G) := by
  have hnC : normalizer (L : Set G) ≤ normalizer (centralizer (L : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (L : Set G))).mp inferInstance
  have hnD : normalizer (R : Set G) ⊓ normalizer (L : Set G) ≤ normalizer (D R L : Set G) :=
    (le_inf (inf_le_left.trans (Stellmacher.normalizer_le_normalizer_baumann R))
      (inf_le_right.trans hnC)).trans inf_normalizer_le_normalizer_inf
  exact hnD.trans (normalizer_le_normalizer_characteristic_image (D R L) (frattini (D R L)))

/-- Every element of M₁ outside the core stabilizer is another valid
noncommuting conjugator for the original module U. -/
theorem Setup.noncentral_of_core_moved (h : Setup R L F) {x y : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (hy : y ∈ normalizer (R : Set G)) (hyN : y ∈ normalizer (Phi R L : Set G))
    (hyQ : y ∉ normalizer (Q R L : Set G)) :
    ¬ (U L).map (MulAut.conj y⁻¹).toMonoidHom ≤ centralizer (U L : Set G) := by
  let e := MulAut.conj y⁻¹
  let e₀ := MulAut.conj x⁻¹
  have hSe : (S R).map e.toMonoidHom = S R := h.stable hy
  have hNe : (Phi R L).map e.toMonoidHom = Phi R L :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (Phi R L : Set G)).inv_mem hyN)
  have hN₀ : (Phi R L).map e₀.toMonoidHom = Phi R L := h.frattini_invariant hx hnc
  have hmove : (Q R L).map e.toMonoidHom ≠ Q R L := by
    intro he
    have hi : y⁻¹ ∈ normalizer (Q R L : Set G) := mem_normalizer_iff_map_conj_eq.mpr he
    exact hyQ (by simpa only [inv_inv] using (normalizer (Q R L : Set G)).inv_mem hi)
  have hswap := (h.quotient_pair_preserved hx hnc e hSe hNe).resolve_left hmove
  have hScomp : (S R).map (e * e₀).toMonoidHom = S R := by
    change (S R).map (e.toMonoidHom.comp e₀.toMonoidHom) = S R
    rw [← map_map, h.stable hx, hSe]
  have hNcomp : (Phi R L).map (e * e₀).toMonoidHom = Phi R L := by
    change (Phi R L).map (e.toMonoidHom.comp e₀.toMonoidHom) = Phi R L
    rw [← map_map, hN₀, hNe]
  have hother : ((Q R L).map e₀.toMonoidHom).map e.toMonoidHom = Q R L := by
    have hh := h.quotient_pair_preserved hx hnc (e * e₀) hScomp hNcomp
    change (Q R L).map (e.toMonoidHom.comp e₀.toMonoidHom) = Q R L ∨
      (Q R L).map (e.toMonoidHom.comp e₀.toMonoidHom) = (Q R L).map e₀.toMonoidHom at hh
    rw [← map_map] at hh
    rcases hh with hh | hh
    · exact hh
    · have he := map_injective e.injective (hh.trans hswap.symm)
      exact (hnc (((map_mono (f := e₀.toMonoidHom) h.module_le_core).trans_eq he).trans
        (h.core ▸ inf_le_right))).elim
  have hD : (D R L).map e.toMonoidHom ≤ Q R L := by
    have hd : D R L ≤ (Q R L).map e₀.toMonoidHom :=
      le_sup_right.trans_eq (h.opposite_eq_conjugate hx hnc)
    exact (map_mono hd).trans_eq hother
  intro hcomm
  have hU : (U L).map e.toMonoidHom ≤ Q R L := by
    rw [h.core]
    exact le_inf (h.conjugate_le hy) hcomm
  have hQle : (Q R L).map e.toMonoidHom ≤ Q R L := by
    conv_lhs => rw [(h.factorization hx hnc).core, Subgroup.map_sup]
    exact sup_le hU hD
  exact hmove (eq_of_le_of_card_ge hQle (card_map_of_injective e.injective).ge)

/-- A Sylow subgroup of M cannot normalize the first block: the actual
M₁-core stabilizer has even relative index. This rules out s=1. -/
theorem Setup.sylow_not_normalizes_block (h : Setup R L F) (M : Subgroup G)
    (hMR : M ≤ normalizer (R : Set G)) (T : Sylow 2 M) {x : G} (hx : x ∈ M)
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    ¬ (T : Subgroup M).map M.subtype ≤ normalizer (L : Set G) := by
  let A := M ⊓ normalizer (Phi R L : Set G)
  let B := A ⊓ normalizer (Q R L : Set G)
  have hi : B.relIndex A = 2 := by
    rw [inf_relIndex_left]
    exact h.frattini_stabilizer_index M hMR hx hnc
  have hiM : (B.subgroupOf M).relIndex (A.subgroupOf M) = 2 := by
    rw [relIndex_subgroupOf (show A ≤ M from inf_le_left), hi]
  intro hTL
  apply sylow_not_le_index_two_section T (A.subgroupOf M) (B.subgroupOf M)
    (subgroupOf_mono M inf_le_left) hiM
  intro t ht
  have htM : (t : G) ∈ M := t.property
  have htL := hTL (mem_map_of_mem M.subtype ht)
  exact ⟨⟨htM, block_normalizer_le_phi_normalizer R L ⟨hMR htM, htL⟩⟩,
    h.block_normalizer_le_core_normalizer M hMR ⟨htM, htL⟩⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
