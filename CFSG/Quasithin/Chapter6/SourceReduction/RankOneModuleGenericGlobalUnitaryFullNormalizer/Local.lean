module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryNativeLift.Source

/-!
# Reduced parabolics inside the full source normalizers

The reduced common Sylow lies in both original residuals. Its local Borels
are therefore unchanged. Write a reduced parabolic as its residual times
the opposite local Borel. An element normalizing the common Sylow has its
residual factor in the corresponding local Borel, hence lies in the opposite
parabolic as well. This identifies each intersection with the full common
normalizer, without identifying the original source Sylow with the reduced one.

Source: Aschbacher–Smith 5.3.1(3–4), printed pp.658–659, and F.1.3(4–6).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryFullNormalizer
variable {G : Type*} [Group G]

private theorem parabolic_inf_normalizer_le_opposite
    (J : Fin 2 → Subgroup G) (R : Subgroup G)
    (hR : ∀ i, R ≤ J i)
    (hc : ∀ i, ChapterF.Source.borel (J (ChapterF.Source.other i)) R ≤ normalizer (J i : Set G))
    (i : Fin 2) :
    ChapterF.Source.parabolic J R i ⊓ normalizer (R : Set G) ≤
      ChapterF.Source.parabolic J R (ChapterF.Source.other i) := by
  intro x hx
  have hxP := hx.1
  change x ∈ J i ⊔ R ⊔ ChapterF.Source.borel (J (ChapterF.Source.other i)) R at hxP
  rw [sup_eq_left.mpr (hR i)] at hxP
  have hxprod : x ∈ (J i : Set G) * (ChapterF.Source.borel (J (ChapterF.Source.other i)) R : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (hc i)]
    exact hxP
  obtain ⟨l,hl,b,hb,rfl⟩ := hxprod
  have hbN : b ∈ normalizer (R : Set G) := by
    have hh := hb.2
    rw [inf_eq_left.mpr (hR _)] at hh
    exact hh
  have hlN : l ∈ normalizer (R : Set G) :=
    ((normalizer (R : Set G)).mul_mem_cancel_right hbN).mp hx.2
  apply (ChapterF.Source.parabolic J R (ChapterF.Source.other i)).mul_mem
  · have hi : ChapterF.Source.other (ChapterF.Source.other i) = i := by
      fin_cases i <;> rfl
    apply (show ChapterF.Source.borel (J (ChapterF.Source.other (ChapterF.Source.other i))) R ≤
      ChapterF.Source.parabolic J R (ChapterF.Source.other i) from le_sup_right)
    rw [hi]
    refine ⟨hl, ?_⟩
    change l ∈ normalizer ((R ⊓ J i : Subgroup G) : Set G)
    rw [inf_eq_left.mpr (hR i)]
    exact hlN
  · exact (show J (ChapterF.Source.other i) ≤
      ChapterF.Source.parabolic J R (ChapterF.Source.other i) from le_sup_left.trans le_sup_left) hb.1

end UnitaryFullNormalizer

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- Literal local products and intersections for the reduced endpoints.
The whole common-normalizer containment is supplied by the marked action. -/
theorem Preparation.reduced_normalizer_endpoint_data
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (cc : ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,residual H] (sourceS L H)))
    (hl : Chapter5.Section03GreenExtension.SourceLocalConditions
      (normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L))
    (hCD : (ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1 : Subgroup G) ≤
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G)) :
    let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L)
    let D := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
    (∀ i, P i ≤ normalizer (![L,residual H] i : Set G)) ∧
    (∀ i, P i ⊓ D = P 0 ⊓ P 1) ∧
    (∀ x ∈ normalizer (L : Set G), ∃ p ∈ P 0, ∃ z ∈ D, x = p*z) ∧
    (∀ x ∈ normalizer (residual H : Set G), ∃ p ∈ P 1, ∃ z ∈ D, x = p*z) := by
  let J : Fin 2 → Subgroup G := ![L,residual H]
  let R := (T : Subgroup G) ⊓ L
  let P := ChapterF.Source.parabolic J R
  let D := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  have hf := d.hypothesisF11 h hH.1.1.2
  have he := d.common_sylow_of_comparison h hH.1.1.2 hp cc
  have hs : ∀ i, sourceS L H ⊓ J i = R := by
    intro i
    fin_cases i
    · exact d.left_intersection
    · apply le_antisymm
      · exact (inf_le_inf_right _ (sourceS_le_sylow h.sylow_normalizes hH.1.1.2)).trans_eq he.symm
      · apply le_inf
        · change (T : Subgroup G) ⊓ L ≤ sourceS L H
          rw [← d.left_intersection]
          exact inf_le_left
        · change (T : Subgroup G) ⊓ L ≤ residual H
          rw [he]
          exact inf_le_right
  have hR : ∀ i, R ≤ J i := fun i => (hs i) ▸ inf_le_right
  have hb : ∀ i, ChapterF.Source.borel (J i) R = ChapterF.Source.borel (J i) (sourceS L H) := by
    intro i
    unfold ChapterF.Source.borel
    rw [inf_eq_left.mpr (hR i),hs i]
  have hcross : ∀ i, ChapterF.Source.borel (J (ChapterF.Source.other i)) R ≤ normalizer (J i : Set G) := by
    intro i
    rw [hb]
    exact hf.cross i
  have hPM (i : Fin 2) : P i ≤ normalizer (J i : Set G) :=
    sup_le (sup_le (J i).le_normalizer ((hR i).trans (J i).le_normalizer)) (hcross i)
  have hPD (i : Fin 2) : P i ⊓ D = P 0 ⊓ P 1 := by
    apply le_antisymm
    · have hh : P i ⊓ D ≤ P (ChapterF.Source.other i) := by
        rw [show D = normalizer (R : Set G) from hl.normalizer_eq_middle.symm]
        exact UnitaryFullNormalizer.parabolic_inf_normalizer_le_opposite J R hR hcross i
      fin_cases i
      · exact le_inf inf_le_left hh
      · exact le_inf hh inf_le_left
    · apply le_inf _ hCD
      fin_cases i
      · exact inf_le_left
      · exact inf_le_right
  refine ⟨hPM,hPD,?_,?_⟩
  · intro x hx
    obtain ⟨p,hp,z,hz,hx⟩ := hl.factor_left x hx
    exact ⟨p,(show L ≤ P 0 from le_sup_left.trans le_sup_left) hp,z,hz,hx⟩
  · intro x hx
    obtain ⟨p,hp,z,hz,hx⟩ := hl.factor_right x hx
    exact ⟨p,(show residual H ≤ P 1 from le_sup_left.trans le_sup_left) hp,z,hz,hx⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
