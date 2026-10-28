module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.NormalizerAction
public import CFSG.Quasithin.Chapter13.Section05.LocalGeometry.NonabelianClosure
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.Quasithin.Rank
public import CFSG.Quasithin.Defs

/-!
# The actual starred actors in 13.5.20

Restriction of H → H/O₂(H) to Y has a two-group kernel. It therefore
preserves Y/O₂(Y), as well as two-perfectness. Nonabelian U_H and the
index-two seed give |V*|=2, so normalization of V before quotienting
becomes centralization of V* afterwards. Finally, odd rank decreases
through the two-core quotient, using the full source SQTK input.

These are transport lemmas for the earlier source facts about Y, with
Y=L₀ in the covered branch and Y=L₁ otherwise. They do not assume any
Fitting centralization or action-model recognition.
Source: Aschbacher–Smith, combined manuscript, 13.5.20, p.923 (PDF p.940).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08.Source
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting
variable {G : Type*} [Group G] [Finite G]

/-- Quotienting by H's two-core preserves the local two-core quotient. -/
theorem star_cubic_quotient (H Y : Subgroup G) (hYH : Y ≤ H)
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 3) :
    Nat.card (starImage H Y ⧸ pCore 2 (starImage H Y)) = 3 := by
  let B := Y.subgroupOf H
  let e : Y ≃* B := (subgroupOfEquivOfLe hYH).symm
  let q := QuotientGroup.mk' (pCore 2 H)
  let f : B →* starImage H Y := q.subgroupMap B
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.subgroupMap B).ker
    rw [ker_subgroupMap]
    have hq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    exact hq.comap_subtype
  have hB : Nat.card (B ⧸ pCore 2 B) = 3 := by
    rw [← Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
    exact hc
  exact (Nat.card_congr (f.pCoreQuotientEquiv (q.subgroupMap_surjective B) hk).symm.toEquiv).trans hB

omit [Finite G] in
/-- Two-perfectness passes to the literal star image. -/
theorem star_twoPerfect (H Y : Subgroup G) (hYH : Y ≤ H) (hY : IsPPerfect 2 Y) :
    IsPPerfect 2 (starImage H Y) := by
  exact (hY.of_surjective (subgroupOfEquivOfLe hYH).symm.toMonoidHom
    (subgroupOfEquivOfLe hYH).symm.surjective).of_surjective
    ((QuotientGroup.mk' (pCore 2 H)).subgroupMap (Y.subgroupOf H))
    ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective (Y.subgroupOf H))

private theorem normalizer_centralizes_card_two {Q : Type*} [Group Q]
    (A : Subgroup Q) (hc : Nat.card A = 2) : normalizer (A : Set Q) ≤ centralizer (A : Set Q) := by
  let N := normalizer (A : Set Q)
  have hh : Nat.card (A.subgroupOf N) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe A.le_normalizer).toEquiv).trans hc
  have hz := central_of_normal_card_two (A.subgroupOf N) hh
  intro n hn a ha
  exact congrArg Subtype.val
    (mem_center_iff.mp (hz (show (⟨a, A.le_normalizer ha⟩ : N) ∈ A.subgroupOf N from ha)) ⟨n, hn⟩).symm

/-- Y normalizes V before quotienting, and its order-two star therefore
centralizes Y*. The order comes from nonabelian U_H, not an assumed actor. -/
theorem star_centralizes_V (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (hindex : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (Y : Subgroup G) (hn : Y ≤ normalizer (D.V : Set G)) :
    starImage D.H Y ≤ centralizer (starImage D.H D.V : Set (Hstar D.H)) := by
  apply le_trans _ (normalizer_centralizes_card_two _ (LocalGeometry.star_V_card_two h hindex hu))
  have hn' : Y.subgroupOf D.H ≤ normalizer (D.V.subgroupOf D.H : Set D.H) := by
    rw [← subgroupOf_normalizer_eq h.V_le_H]
    exact comap_mono hn
  exact (map_mono hn').trans
    ((D.V.subgroupOf D.H).le_normalizer_map (QuotientGroup.mk' (pCore 2 D.H)))

/-- The full SQTK input supplies the rank bound after the actual two-core
quotient; no arbitrary-quotient rank monotonicity is used. -/
theorem star_threeRank_le (K : GroupClass) (H : Subgroup G) (hH : IsSQTK K H) :
    primeRank 3 (Hstar H) ≤ 2 :=
  (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 H) pCore_isPGroup).trans
    (hH.stronglyQuasithin 3 Nat.prime_three (by decide))

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting

end
