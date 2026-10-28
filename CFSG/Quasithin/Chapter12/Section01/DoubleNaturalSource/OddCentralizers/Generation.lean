module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.Inputs
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedSetup
public import CFSG.Quasithin.ChapterE.GenerationKnownSimple
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.KnownSimple
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.FixedSubgroup
public import Theory.NumberTheory.BinarySignedTorus

/-!
# Generation in the doubled-orbit branch

Weak closure and uniqueness control N_G(T). Attained E-generation and
E.3.35 exclude n(H) ≤ 1 for every actual outside H*. The original E.2.2
dispatcher then supplies its reflected Cartan subgroup. If n(H)>2, a prime
p>3 divides its cyclic torus; the corresponding characteristic Hall p-core
permutes with T. The finite action input centralizes W, and the ambient
odd-normalizer theorem contradicts the reflected normalizer escape.

Only those last two independent source inputs remain explicit. The proof
does not identify the Cartan field exponent with n(H): its attained upper
bound is sufficient. Source: Aschbacher--Smith, 12.1.9(2), p.793.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)

include D h in
/-- The actual Sylow normalizer is controlled by W₀ and uniqueness over C_T(W). -/
theorem doubledOrbit_sylow_normalizer_le_of_many
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hw : (1 : ℕ∞) < globalW (componentOrbit V (T : Subgroup G)) T) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  let := D.doubledOrbit_elementary h
  exact (normalizer_le_weakClosure_normalizer _ _ 0).trans
    (SourceContainment.normalizer_weakClosure_zero_le (D.doubledOrbit_E322 h)
      (lt_trans (by decide) hw) (D.doubledOrbit_centralizer_unique h))

/-- E.3.35 with the attained KnownSimple parameter gives the lower bound
needed before invoking the original E.2.2 Cartan theorem. -/
theorem doubledOrbit_generation_gt_one_of_many
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hw : (1 : ℕ∞) < globalW (componentOrbit V (T : Subgroup G)) T)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    letI := D.doubledOrbit_elementary h
    B.NonsingularCentralizers → 1 < generationParameter H := by
  let := D.doubledOrbit_elementary h
  intro hcentral
  by_contra hn
  have hn1 : generationParameter H ≤ 1 := by omega
  have hr := B.globalR_ge (D.doubledOrbit_normalizer_eq h B.orbit_eq) hcentral
  have hnlarge : 1 < n := by rcases B.degree with rfl | rfl <;> decide
  apply hH.1.2
  apply SourceContainment.le_of_sqtk_knownSimple (D.doubledOrbit_E322 h)
    (T.subtype hH.1.1.2) (Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1)
    (D.doubledOrbit_centralizer_unique h)
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (D.doubledOrbit_normalizer_eq h B.orbit_eq).le)
  · change (T : Subgroup G) ⊓ centralizer
        (componentOrbit V (T : Subgroup G) : Set G) ≤
      ((T : Subgroup G).subgroupOf H).map H.subtype
    rw [map_subgroupOf_eq_of_le hH.1.1.2]
    exact inf_le_left
  · apply lt_min
    · exact lt_of_le_of_lt (by exact_mod_cast hn1) hw
    · exact lt_of_lt_of_le (by exact_mod_cast (lt_of_le_of_lt hn1 hnlarge)) hr

omit [Finite G] in
private theorem maximal_eq_overlap
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) :
    minimalParabolicMax (T.subtype hH.1.1.2) hP = (normalizer (L : Set G)).subgroupOf H := by
  let J := minimalParabolicMax (T.subtype hH.1.1.2) hP
  have hJ := minimalParabolicMax_spec (T.subtype hH.1.1.2) hP
  have hTJ : (T : Subgroup G) ≤ J.map H.subtype := by
    have hh := map_mono (f := H.subtype) hJ.2
    change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ J.map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hJH : J.map H.subtype < H := by
    have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hJ.1.lt_top
    change J.map H.subtype < (⊤ : Subgroup H).map H.subtype at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hh
  have hJM : J ≤ (normalizer (L : Set G)).subgroupOf H := map_le_iff_le_comap.mp
    (Chapter3.HStar.proper_overgroup_le T hH hTJ hJH)
  have hn : (normalizer (L : Set G)).subgroupOf H ≠ ⊤ :=
    fun he => hH.1.2 (subgroupOf_eq_top.mp he)
  exact ((hJ.1.le_iff.mp hJM).resolve_left hn).symm

include D h in
/-- Genuine Cartan data on the original H; the field exponent only bounds n(H). -/
theorem doubledOrbit_cartan_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hw : (1 : ℕ∞) < globalW (componentOrbit V (T : Subgroup G)) T)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hn : 1 < generationParameter H) :
    ∃ (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) (f : ℕ),
      IsEGenerated f H ∧ generationParameter H ≤ f ∧
      ∃ d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f,
        minimalParabolicMax (T.subtype hH.1.1.2) hP = (normalizer (L : Set G)).subgroupOf H ∧
        ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup H), Odd p → A ≤ d.witness.cyclicGroup →
          IsPGroup p A → ¬ normalizer (A.map H.subtype : Set G) ≤ normalizer (L : Set G) := by
  have hP := minimalParabolic_subtype T H (Chapter3.HStar.minimalParabolic T
    D.sylow_normalizes_component hH (Or.inl (D.doubledOrbit_sylow_normalizer_le_of_many h hmany hw)))
  obtain ⟨f, hg, hb, d, hescape⟩ := MarkedModels.Inverted.source_intrinsic_escape_knownSimple
    (Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1) (T.subtype hH.1.1.2) hP hn
  have he := maximal_eq_overlap hH hP
  refine ⟨hP, f, hg, hb, d, he, ?_⟩
  intro p hp A ho hA hAp hN
  apply hescape p hp A ho hA hAp
  rw [he]
  intro x hx
  exact hN (A.le_normalizer_map H.subtype (mem_map.mpr ⟨x, hx, rfl⟩))

private theorem prime_gt_three {f : ℕ} (hf : 2 < f) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ 2 ^ f - 1 := by
  by_cases h3 : f = 3
  · subst f
    exact ⟨7, by decide, by decide, by decide⟩
  · exact Nat.BinarySignedTorus.exists_prime_gt_three_dvd_sub (by omega)

/-- Conditional source 12.1.9(2). Both remaining inputs concern actual
subgroup actions and normalizers, not the desired generation parameter. -/
theorem doubledOrbit_generation_eq_two_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hw : (1 : ℕ∞) < globalW (componentOrbit V (T : Subgroup G)) T)
    (hodd : OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)))
    (haction : LargePrimeSylowAction (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)) T)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    letI := D.doubledOrbit_elementary h
    B.NonsingularCentralizers → generationParameter H = 2 := by
  let := D.doubledOrbit_elementary h
  intro hcentral
  have hlo := D.doubledOrbit_generation_gt_one_of_many h hmany B hw hH hcentral
  suffices generationParameter H ≤ 2 by omega
  by_contra hn
  obtain ⟨hP, f, _, hb, d, hmax, hescape⟩ := D.doubledOrbit_cartan_of_many h hmany hw hH hlo
  obtain ⟨p, hp, hp3, hpd⟩ := prime_gt_three (show 2 < f by omega)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨A₀, hA₀⟩ := Sylow.exists_subgroup_card_pow_prime p
    (show p ^ 1 ∣ Nat.card d.witness.cyclicGroup by simpa [d.witness.card] using hpd)
  let A := A₀.map d.witness.cyclicGroup.subtype
  have hAc : Nat.card A = p := by
    rw [card_map_of_injective d.witness.cyclicGroup.subtype_injective]
    simpa only [pow_one] using hA₀
  have hAp : IsPGroup p A := IsPGroup.of_card (n := 1) (by simpa using hAc)
  have hAD : A ≤ d.witness.cyclicGroup := map_subtype_le _
  have hAY := hAD.trans d.witness.cyclic_le
  let := d.witness.abelian
  have hYA : d.witness.abelianGroup ≤ centralizer (A : Set H) :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hAY)
  have hAP : A ≤ d.witness.abelianGroup.pCoreIn p :=
    le_pCoreIn_of_normalizes hAp hAY (hYA.trans (Subgroup.centralizer_le_normalizer _))
  let P := d.witness.abelianGroup.pCoreIn p
  have hperm : (P : Set H) * (T.subtype hH.1.1.2 : Set H) =
      (T.subtype hH.1.1.2 : Set H) * (P : Set H) :=
    permutes_of_factorization d.frattini ((pCoreIn_le p _).trans d.normalizes)
      (inf_le_right.trans (normalizer_le_normalizer_characteristic_image _ (pCore p _)))
  have hPM : P.map H.subtype ≤ normalizer (L : Set G) :=
    map_le_iff_le_comap.mpr ((pCoreIn_le p _).trans (d.hall_le.trans hmax.le))
  have hpermG : (P.map H.subtype : Set G) * (T : Set G) =
      (T : Set G) * (P.map H.subtype : Set G) := by
    have hh := congrArg (Set.image H.subtype) hperm
    change H.subtype '' ((P : Set H) * ((T : Subgroup G).subgroupOf H : Set H)) =
      H.subtype '' (((T : Subgroup G).subgroupOf H : Set H) * (P : Set H)) at hh
    simpa only [Set.image_mul, ← Subgroup.coe_map, map_subgroupOf_eq_of_le hH.1.1.2,
      Sylow.coe_coe] using hh
  have hPC := haction p hp hp3 (P.map H.subtype) ((isPGroup_pCoreIn p _).map H.subtype) hPM hpermG
  have hoddp : Odd p := hp.odd_of_ne_two (by omega)
  have hAcG : Nat.card (A.map H.subtype) = p :=
    (card_map_of_injective H.subtype_injective).trans hAc
  apply hescape p inferInstance A hoddp hAD hAp
  apply hodd (A.map H.subtype)
  · exact (A.map H.subtype).one_lt_card_iff_ne_bot.mp (hAcG ▸ hp.one_lt)
  · exact hAcG ▸ hoddp
  · exact (map_mono hAP).trans hPM
  · exact (map_mono hAP).trans hPC

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
