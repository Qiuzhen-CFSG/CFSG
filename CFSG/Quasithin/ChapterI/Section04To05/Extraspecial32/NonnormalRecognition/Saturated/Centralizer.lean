module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Saturated.Closure
public import CFSG.Quasithin.ChapterI.Section06To08.StrongEmbedding
public import BenderSuzuki.SE.StrongEmbeddingConjugacy

/-!
# The escaping centralizer in the saturated branch

If M = N_G(E) were proper, it would not be strongly embedded: its involutions
inside and outside E cannot be conjugate in M. Strong closure and TI put the
normalizer of a Sylow two-subgroup of M inside M. The strong-embedding
criterion therefore supplies an involution j outside E whose ambient
centralizer J is not contained in M.

Inside J the literal fixed subgroup U = C_E(j) inherits elementary
abelianness, TI and strong closure, and its normalizer is M ∩ J whenever
U is nontrivial. The fixed-group cardinality and two-group property of
M ∩ J are separate local action calculations.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), proof of Lemma 2.8(1), printed pp.35–36.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterI.Section06To08
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {z g : G}

theorem normalizer_sylow_le (h : Hypotheses z) (d : IntersectionData z g)
    (hs : FusionSaturated z g) (T : Sylow 2 (normalizer (coreIntersection z g : Set G))) :
    normalizer (((T : Subgroup (normalizer (coreIntersection z g : Set G))).map
      (normalizer (coreIntersection z g : Set G)).subtype : Subgroup G) : Set G) ≤
        normalizer (coreIntersection z g : Set G) := by
  let E := coreIntersection z g
  let M := normalizer (E : Set G)
  have hzE : z ∈ E := ((hs z).mpr ⟨h.involution_mem_coreInG, IsConj.refl z⟩).1
  have hz1 : z ≠ 1 := by intro he; simpa [he] using h.involution
  have hEp : IsPGroup 2 (E.subgroupOf M) := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe E.le_normalizer).toEquiv, d.card]
    norm_num)
  have hzT : z ∈ (T : Subgroup M).map M.subtype :=
    ⟨⟨z, E.le_normalizer hzE⟩, hEp.le_sylow_of_normal T hzE, rfl⟩
  intro a ha
  have haT := (ha z).mp hzT
  have haM : a * z * a⁻¹ ∈ M := map_subtype_le _ haT
  have haE := mem_intersection_of_conjugate_in_normalizer h d hs haM
    (isConj_iff.mpr ⟨a, rfl⟩)
  exact (intersection_isTI h d hs).mem_normalizer_of_conj_mem hzE hz1 haE

theorem not_stronglyEmbedded (h : Hypotheses z) (d : IntersectionData z g)
    (hs : FusionSaturated z g) :
    ¬ BenderSuzuki.IsStronglyEmbedded (normalizer (coreIntersection z g : Set G)) := by
  intro hse
  have hzE := ((hs z).mpr ⟨h.involution_mem_coreInG, IsConj.refl z⟩).1
  have hz1 : z ≠ 1 := by intro he; simpa [he] using h.involution
  obtain ⟨t, htM, ht, htE⟩ := exists_involution_outside_intersection h d
  have hzI : BenderSuzuki.PFAppendixIII.IsInvolution z :=
    ⟨hz1, by simpa only [h.involution] using pow_orderOf_eq_one z⟩
  have htI : BenderSuzuki.PFAppendixIII.IsInvolution t :=
    ⟨by intro he; simp [he] at ht, by simpa only [ht] using pow_orderOf_eq_one t⟩
  obtain ⟨m, hm, he⟩ := hse.involutions_conjugate_in
    ((coreIntersection z g).le_normalizer hzE) hzI htM htI
  apply htE
  have hh := ((normalizer (coreIntersection z g : Set G)).inv_mem hm z).mp hzE
  change m⁻¹ * z * m = t at he
  simp only [inv_inv] at hh
  exact he ▸ hh

theorem exists_escaping_involution_centralizer (h : Hypotheses z)
    (d : IntersectionData z g) (hs : FusionSaturated z g)
    (hproper : normalizer (coreIntersection z g : Set G) ≠ ⊤) :
    ∃ j : G, j ∈ normalizer (coreIntersection z g : Set G) ∧
      orderOf j = 2 ∧ j ∉ coreIntersection z g ∧
      ¬ Centralizer j ≤ normalizer (coreIntersection z g : Set G) := by
  classical
  let E := coreIntersection z g
  let M := normalizer (E : Set G)
  let T : Sylow 2 M := default
  have heven : Even (Nat.card M) := by rw [normalizer_card d]; decide
  have hfail : ¬ (∀ i : G, i ∈ (T : Subgroup M).map M.subtype →
      BenderSuzuki.PFAppendixIII.IsInvolution i → Centralizer i ≤ M) := by
    intro hall
    exact not_stronglyEmbedded h d hs
      (stronglyEmbedded_of_sylow_normalizer_and_centralizers M T hproper heven
        (normalizer_sylow_le h d hs T) hall)
  push Not at hfail
  obtain ⟨j, hjT, hjI, hjC⟩ := hfail
  refine ⟨j, map_subtype_le _ hjT, orderOf_eq_prime hjI.2 hjI.1, ?_, hjC⟩
  intro hjE
  exact hjC (centralizer_le_normalizer_of_mem_intersection h d hs hjE hjI.1)

/-- The literal fixed subgroup in the escaping involution centralizer. -/
def centralizerIntersection (z g j : G) : Subgroup (Centralizer j) :=
  (coreIntersection z g).subgroupOf (Centralizer j)

theorem centralizerIntersection_normalizer (h : Hypotheses z)
    (d : IntersectionData z g) (hs : FusionSaturated z g) (j : G)
    (hne : centralizerIntersection z g j ≠ ⊥) :
    normalizer (centralizerIntersection z g j : Set (Centralizer j)) =
      (normalizer (coreIntersection z g : Set G)).subgroupOf (Centralizer j) := by
  apply le_antisymm
  · obtain ⟨u, hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    intro a ha
    change (a : G) ∈ normalizer (coreIntersection z g : Set G)
    apply (intersection_isTI h d hs).mem_normalizer_of_conj_mem u.property
      (fun he => hu (Subtype.ext (Subtype.ext he)))
    exact (ha u.val).mp u.property
  · intro a ha x
    change (x : G) ∈ coreIntersection z g ↔
      (a : G) * (x : G) * (a : G)⁻¹ ∈ coreIntersection z g
    exact ha x

theorem centralizerIntersection_isTI (h : Hypotheses z)
    (d : IntersectionData z g) (hs : FusionSaturated z g) (j : G)
    (hne : centralizerIntersection z g j ≠ ⊥) :
    IsTISubgroup (centralizerIntersection z g j) := by
  apply (isTISubgroup_iff _).mpr
  intro a ha x hx hax
  by_contra hx1
  apply ha
  rw [centralizerIntersection_normalizer h d hs j hne]
  exact (intersection_isTI h d hs).mem_normalizer_of_conj_mem hx
    (fun he => hx1 (Subtype.ext he)) hax

theorem centralizerIntersection_stronglyClosed (h : Hypotheses z)
    (d : IntersectionData z g) (hs : FusionSaturated z g) (j : G)
    (hne : centralizerIntersection z g j ≠ ⊥) :
    IsStronglyClosedSet (centralizerIntersection z g j : Set (Centralizer j))
      (normalizer (centralizerIntersection z g j : Set (Centralizer j))) ⊤ := by
  refine ⟨(centralizerIntersection z g j).le_normalizer, ?_⟩
  intro x hx a _ hax
  rw [centralizerIntersection_normalizer h d hs j hne] at hax
  exact (stronglyClosed_intersection_normalizer h d hs).2 (x : G) hx (a : G) (mem_top _) hax

omit [Finite G] in
theorem centralizerIntersection_elementary (d : IntersectionData z g) (j : G) :
    IsElementaryAbelian 2 (centralizerIntersection z g j) := by
  let _ := d.elementary
  change IsElementaryAbelian 2 ((coreIntersection z g).subgroupOf (Centralizer j))
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := coreIntersection z g) _ x.property

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition

end
