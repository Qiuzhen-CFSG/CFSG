module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.MarkedPlane
public import CFSG.Quasithin.Chapter13.Section02.A5Local.ThompsonOdd

/-!
# The original Thompson image in symmetric-five coordinates

The actual local actor is onto S₅. J(T) fixes V₂ pointwise and its image is
normalized by the Sylow image. The original maximal-elementary offender
supplies an odd permutation, so the plane-fixer calculation identifies its
image with the disjoint-transposition group. One coordinate change marks
this group, the original V₂, and the whole Sylow image simultaneously.

The final theorem applies the marking to the literal contrary core-free
join H∨O²(N_L(T∩L)). The earlier Baumann-normalizer, solvability and
[Z,L₁]=1 premises remain explicit.
Source: Aschbacher–Smith 13.2.11(2)–(3) and13.2.12, pp.881–882.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]
open BinaryPermutation.FivePairFixedSpaces

theorem source_thompson_and_plane_marking
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    let K := L ⊔ (T : Subgroup G)
    let S := T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)
    ∃ g : Perm, (S : Subgroup K).map d.localActor =
      (normalizer (pairClosure : Set Perm)).map (MulAut.conj g).toMonoidHom ∧
      d.flag.preimage V₂ = (fixedSubgroup (first * second)).map (actionHom g) ∧
      (elementaryAbelianMaxJ (S : Subgroup K)).map d.localActor =
        pairClosure.map (MulAut.conj g).toMonoidHom := by
  let K := L ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)
  have hfull := source_centerfree_localActor_surjective d hH hB hZ hs hz
  let P := S.mapSurjective hfull
  have hcard : Nat.card (d.flag.preimage V₂) = 4 :=
    (d.flag.preimage_card V₂ d.flag.two_le_V).trans d.flag.two_card
  have hinv : ∀ p ∈ (P : Subgroup Perm), ∀ x ∈ d.flag.preimage V₂,
      actionHom p x ∈ d.flag.preimage V₂ := by
    rintro p ⟨t, ht, rfl⟩ x hx
    change d.flag.module.map (Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5) (d.flag.normalizerAction ⟨t,_⟩) x.toAdd)) ∈ V₂
    rw [← d.flag.normalizer_equivariant]
    exact (mem_normalizer_iff.mp (d.flag.two_invariant ht) _).mp hx
  have hn : (P : Subgroup Perm) ≤ normalizer
      ((elementaryAbelianMaxJ (S : Subgroup K)).map d.localActor : Set Perm) := by
    apply (map_mono (f := d.localActor) ?_).trans
      ((elementaryAbelianMaxJ (S : Subgroup K)).le_normalizer_map d.localActor)
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (elementaryAbelianMaxJ (S : Subgroup K)).map (MulAut.conj t).toMonoidHom = _
    rw [← elementaryAbelianMaxJ_map_equiv]
    congr 1
    exact mem_normalizer_iff_map_conj_eq.mp ((S : Subgroup K).le_normalizer ht)
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup K)).map K.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective K.subtype K.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le le_sup_right
  have hplane : V₂ ≤ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    rw [← source_alpha_eq_flag_plane d hH hB hZ hs hz,
      source_alpha_eq_local_fixed_plane d hH hB hZ hs hz]
    exact inf_le_right
  have hfix : ∀ a ∈ (elementaryAbelianMaxJ (S : Subgroup K)).map d.localActor,
      ∀ x ∈ d.flag.preimage V₂, actionHom a x = x := by
    rintro a ⟨t, ht, rfl⟩ x hx
    apply d.flag.module.injective
    change d.flag.module.map (Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5) (d.flag.normalizerAction ⟨t,_⟩) x.toAdd)) = _
    rw [← d.flag.normalizer_equivariant]
    apply mul_inv_eq_iff_eq_mul.mpr
    apply mem_centralizer_iff.mp (hplane hx) t
    rw [← hJmap]
    exact mem_map_of_mem K.subtype ht
  have hmoves : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) := by
    intro hj
    have hVE : V ≤ ChapterB.thompsonAlpha (T : Subgroup G) := by
      rw [source_alpha_eq_local_fixed_plane d hH hB hZ hs hz]
      exact le_inf le_rfl (le_centralizer_iff.mp hj)
    have hc := Nat.card_le_card_of_injective (inclusion (d.third_le.trans hVE))
      (inclusion_injective (d.third_le.trans hVE))
    rw [d.third_card, source_alpha_card_four d hH hB hZ hs hz] at hc
    omega
  exact BinaryPermutation.FiveSylowPlane.exists_plane_and_normal_odd_marking
    P (d.flag.preimage V₂) ((elementaryAbelianMaxJ (S : Subgroup K)).map d.localActor)
    hcard hinv hn hfix (d.local_thompson_image_not_le_alternating hmoves)

theorem source_coreFree_borel_join_thompson_marking
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hL₁Z : borelResidual T L ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 = ⊥) :
    let K := L ⊔ (T : Subgroup G)
    let S := T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)
    ∃ g : Perm, (S : Subgroup K).map d.localActor =
      (normalizer (pairClosure : Set Perm)).map (MulAut.conj g).toMonoidHom ∧
      d.flag.preimage V₂ = (fixedSubgroup (first * second)).map (actionHom g) ∧
      (elementaryAbelianMaxJ (S : Subgroup K)).map d.localActor =
        pairClosure.map (MulAut.conj g).toMonoidHom :=
  source_thompson_and_plane_marking d hH hB hZ hs
    (source_center_eq_bot_of_borel_join_core_eq_bot d hH hL₁Z hcore)

end CFSG.Quasithin.Chapter13.Section02.A5Outside
