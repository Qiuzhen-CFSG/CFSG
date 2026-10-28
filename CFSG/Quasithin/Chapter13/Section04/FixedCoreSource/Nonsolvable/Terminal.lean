module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.OffenderIntersection
public import Theory.Representation.BinaryPermutation.SixCommonFixedSpace

/-!
# The terminal natural-module contradiction in original 13.4.1

Cyclic preimages in the actual eight-element action image have corank two
in A = Vʸ. The ambient centralizer bound therefore puts every nonidentity
image element's fixed space inside the common fixed space. The natural S₆
calculation rules this out. The final application uses the original
five-dimensional CoreMarking, its actual conjugation maps, and a separate
marking of the natural second local module W = V_H.

The source construction of K, H₂, H₀ and V₀, the unique escape in 13.4.12,
the reciprocal-containment and graph arguments in 13.4.15–17, and the moving
natural action of image order eight remain explicit obligations of
qt-d-1341-nonsolvable-source. These are conditional terminal theorems, not
a proof of the full nonsolvable branch. Earlier structural, fusion and
fixed-line kernel inputs come from qt-d-1222-source, qt-d-1332-source and
qt-d-1341-local-amalgam-source. Final ambient recognition remains with
qt-d-1341-fixed-core-source.

Source: Aschbacher–Smith, final argument of 13.4.1, printed p.915.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
universe u
variable {G : Type u} [Group G]

private theorem cyclic_preimage_corank (A : Subgroup G)
    (φ : A →* Equiv.Perm (Fin 6)) (hcard : Nat.card φ.range = 8)
    [IsElementaryAbelian 2 φ.range]
    (b : Equiv.Perm (Fin 6)) (hb : b ∈ φ.range) (hb1 : b ≠ 1) :
    ChapterE.subgroupCorank A (((zpowers b).comap φ).map A.subtype) = 2 := by
  have hb2 : Nat.card (zpowers b) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian b hb) hb1
  have hB : zpowers b ≤ φ.range := zpowers_le.mpr hb
  have hmul : Nat.card (zpowers b) * (zpowers b).relIndex φ.range = 8 := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv]
    exact ((zpowers b).subgroupOf φ.range).card_mul_index.trans hcard
  have hi : (zpowers b).relIndex φ.range = 4 := by rw [hb2] at hmul; omega
  unfold ChapterE.subgroupCorank
  have he : A = (⊤ : Subgroup A).map A.subtype := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  conv_lhs => arg 2; arg 2; rw [he]
  rw [relIndex_map_map_of_injective _ _ A.subtype_injective,
    relIndex_top_right, index_comap, hi]
  decide

/-- The final rank-three contradiction, transported through the actual
conjugation action on W. The actor image has order eight; every cyclic
preimage has corank two in A, so its W-centralizer is fixed by all of A. -/
theorem false_of_natural_image_and_fixed_subgroups
    (A W : Subgroup G) [IsElementaryAbelian 2 A]
    (hAW : A ≤ normalizer (W : Set G))
    (φ : A →* Equiv.Perm (Fin 6))
    (e : W ≃* Multiplicative (natural (Fin 6)))
    (he : ∀ (a : A) (w : W),
      (e (W.normalizerMonoidHom ⟨a.val, hAW a.property⟩ w)).toAdd =
        naturalRepresentation (Fin 6) (φ a) (e w).toAdd)
    (hcard : Nat.card φ.range = 8)
    (hfamily : ∀ B : Subgroup G, B ≤ A → ChapterE.subgroupCorank A B ≤ 2 →
      W ⊓ centralizer (B : Set G) ≤ centralizer (A : Set G)) : False := by
  let : IsElementaryAbelian 2 φ.range :=
    IsElementaryAbelian.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  apply natural_six_no_rank_three_common_fixed φ.range hcard.ge
  intro b hb hb1 v hv
  let B := ((zpowers b).comap φ).map A.subtype
  have hBA : B ≤ A := map_subtype_le _
  have hcor : ChapterE.subgroupCorank A B ≤ 2 :=
    (cyclic_preimage_corank A φ hcard b hb hb1).le
  let w : W := e.symm (Multiplicative.ofAdd v)
  have hw : (e w).toAdd = v := e.apply_symm_apply _
  have hwB : w.val ∈ centralizer (B : Set G) := by
    apply mem_centralizer_iff.mpr
    intro c hc
    obtain ⟨a, ha, rfl⟩ := hc
    have hh := he a w
    have hvb : naturalRepresentation (Fin 6) (φ a) v = v := hv ⟨φ a, ha⟩
    rw [hw, hvb] at hh
    have hconj := congrArg Subtype.val
      (e.injective (Multiplicative.toAdd.injective (hh.trans hw.symm)))
    exact mul_inv_eq_iff_eq_mul.mp hconj
  have hwA := hfamily B hBA hcor ⟨w.property, hwB⟩
  intro a
  obtain ⟨c, hc⟩ := a.property
  have hf : W.normalizerMonoidHom ⟨c.val, hAW c.property⟩ w = w := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hwA c.val c.property)
  have hh := he c w
  rw [hf, hw, hc] at hh
  exact hh.symm


open Chapter12.Section02
variable [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The terminal source application for the same five-dimensional marked V,
its actual returning conjugate, and the natural second local module W.
The unresolved geometry and image construction are explicit premises. -/
theorem false_of_marked_natural_terminal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz1 : z ≠ 1) (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (hkernel : ∀ B : Subgroup G, B ≤ normalizer (V : Set G) →
      ⁅V, B⁆ ≤ V ⊓ centralizer (L : Set G) → ⁅V, B⁆ = ⊥)
    (W : Subgroup G) (hpoints : ∀ w ∈ W, w ≠ 1 → IsConj m.constant.val w)
    (y : G) (hAW : V.conjBy y ≤ normalizer (W : Set G))
    (hmove : ¬ W ≤ centralizer (V.conjBy y : Set G))
    (φ : V.conjBy y →* Equiv.Perm (Fin 6))
    (e : W ≃* Multiplicative (natural (Fin 6)))
    (he : ∀ (a : V.conjBy y) (w : W),
      (e (W.normalizerMonoidHom ⟨a.val, hAW a.property⟩ w)).toAdd =
        naturalRepresentation (Fin 6) (φ a) (e w).toAdd)
    (hcard : Nat.card φ.range = 8) : False := by
  let := D.elementary
  let : IsElementaryAbelian 2 (V.conjBy y) := IsElementaryAbelian.map _
  have hr := m.three_le_globalR_of_unique_escape h structural z hz1 hzT hzout hunique
  have hu := m.terminal_intersection_centralizes h structural hfusion hkernel W hpoints y hAW
  have hf := CoreMarking.terminal_corank_and_fixed_subgroups hr W y hu hmove
  exact false_of_natural_image_and_fixed_subgroups (V.conjBy y) W hAW φ e he hcard
    (fun B hB hcor => (hf.2 B hB hcor).trans inf_le_right)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
