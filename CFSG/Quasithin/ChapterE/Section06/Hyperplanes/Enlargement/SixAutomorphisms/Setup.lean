module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.Contracts

/-!
# The nonidentity intersection in the further enlargement

An escaping hyperplane forces r = 1 and m > 2. E.6.17 then gives dim V ≥ 6,
whereas A ∩ Uᵍ has corank at most three. This proves that its centralizer is
a proper local overgroup to which the component-enlargement argument applies.
The component X and its escaping block remain inside this centralizer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.17 and the
further-enlargement paragraph on printed p.254 (PDF p.265).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms
open ComponentBalance
variable {G : Type*} [Group G] [Finite G] {M V U A L X : Subgroup G}

/-- Intersecting the corank-two subspace with a conjugate hyperplane costs at most three. -/
theorem intersection_corank_le_three [IsElementaryAbelian 2 V]
    (hU : IsHyperplane V U) (hc : subgroupCorank V A = 2)
    (g : G) (hg : g ∈ localNormalizer M V) :
    subgroupCorank V (intersection A U g) ≤ 3 := by
  have hi := corank_inf_le (V := V) A (U.map (MulAut.conj g).toMonoidHom)
  rw [hc, corank_conjugate V U g hg.2, hU.2] at hi
  exact hi

/-- E.6.17 supplies more than the dimension needed for a nonidentity intersection. -/
theorem intersection_ne_bot [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h15 : HypothesisE615 V)
    (h13 : ∀ B ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (B : Set G))
    (hU : IsHyperplane V U) (he : ¬ centralizer (U : Set G) ≤ M)
    (hc : subgroupCorank V A = 2) (g : G) (hg : g ∈ localNormalizer M V) :
    intersection A U g ≠ ⊥ := by
  have hr := (lemma_E_6_16_1 h h15 hU he).1
  have hd := (lemma_E_6_17 h h15 h13 hr).2
  have hi := intersection_corank_le_three hU hc g hg
  intro hbot
  rw [hbot, corank_bot] at hi
  omega

omit [Finite G] in
/-- The original six component lies in the larger centralizer. -/
theorem le_intersection_centralizer
    (hX : ProperSixEnlargement V U A L X) (g : G) :
    X ≤ centralizer (intersection A U g : Set G) :=
  hX.component.1.trans (Subgroup.centralizer_le inf_le_left)

omit [Finite G] in
/-- Its escaping block also witnesses escape of the larger centralizer. -/
theorem intersection_centralizer_escapes
    (hX : ProperSixEnlargement V U A L X) (he : ¬ L ≤ M) (g : G) :
    ¬ centralizer (intersection A U g : Set G) ≤ M :=
  fun hh => he ((hX.proper.le.trans (le_intersection_centralizer hX g)).trans hh)

omit [Finite G] in
/-- Relative normality gives the action of every element of V on the new component. -/
theorem NormalComponentExtension.normalized_by_V [IsElementaryAbelian 2 V]
    {g : G} {Y : Subgroup G} (hY : NormalComponentExtension U A X g Y)
    (hAV : A ≤ V) : V ≤ normalizer (Y : Set G) := by
  have hVC : V ≤ centralizer (intersection A U g : Set G) :=
    V.le_centralizer.trans (Subgroup.centralizer_le (inf_le_left.trans hAV))
  exact hVC.trans ((normal_subgroupOf_iff_le_normalizer hY.component.1).mp hY.normal)

omit [Finite G] in
/-- When D normalizes Y, the recorded automorphism subgroup is the full D-action. -/
theorem actionImage_eq_range {D Y : Subgroup G} (hn : D ≤ normalizer (Y : Set G)) :
    actionImage D Y = (Y.normalizerMonoidHom.comp (inclusion hn)).range := by
  ext a
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, hd⟩, rfl⟩
  · rintro ⟨d, rfl⟩
    exact ⟨inclusion hn d, d.property, rfl⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms
