module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.ReducedSource
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.Source
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralNormality
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The actual two-component orbit in 13.6.14

The local C-component defining Y_z lies in K T_v. Apply the proved A.3.8
source theorem to its two-core quotient, then lift the normalizer index and
the four-model list. In the noninvariant case every T_v-conjugate is K or
one chosen moving conjugate, so their join is exactly K₋. All quotient
models refer to K/O₂(K), with no quotient or orbit substituted by a label.

Source: Aschbacher--Smith, 1.2.1(3) and the first sentence of the proof of
13.6.14, printed pp.504 and929.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem local_ccomponent_orbit
    {D : Type u} [Group D] [Finite D]
    (hD : IsSQTK KnownSimple.IsKnownSimple D) (hO : pCore 2 D = ⊥)
    (B : Subgroup D) (hB : B.IsCComponent) :
    B.Normal ∨ (normalizer (B : Set D)).index = 2 ∧
      Chapter1.Section02.NonnormalCComponentModel B := by
  by_cases hn : B.Normal
  · exact Or.inl hn
  · right
    have hq := (ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hD hO hB).resolve_left hn
    exact ChapterA.SQTKStructure.NonnormalOuterSource.nonnormal_component_index_and_model
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hD hO B ⟨hB.subnormal,hq⟩ hn

/-- The noninvariant alternative is an actual pair with the full original
four-model list; no classification input is left explicit. -/
theorem noninvariant_component_pair_source (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G)) :
    (normalizer (K.subgroupOf (K ⊔ Tv T v) : Set ↥(K ⊔ Tv T v))).index = 2 ∧
      Chapter1.Section02.NonnormalCComponentModel (K ⧸ pCore 2 K) ∧
      ∃ t ∈ Tv T v, t ∉ normalizer (K : Set G) ∧ Kminus K T v = K ⊔ K.conjBy t := by
  have hHG : K ⊔ Tv T v ≤ Gv v := sup_le hK.1.1 inf_le_right
  have hH : IsSQTK KnownSimple.IsKnownSimple ↥(K ⊔ Tv T v) :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHG)).mp (hlocal.subgroup _)
  have hQ : IsSQTK KnownSimple.IsKnownSimple (↥(K ⊔ Tv T v) ⧸ pCore 2 ↥(K ⊔ Tv T v)) := by
    refine ⟨?_, hH.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hH.stronglyQuasithin p hp ho)
  have hnot : ¬ (K.subgroupOf (K ⊔ Tv T v)).Normal := by
    intro hN
    exact hn (le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer le_sup_left).mp hN))
  obtain ⟨hi, hm⟩ := (Chapter1.Section02.proposition_1_2_1_three_index_of_A_3_8
    (fun _ _ _ => local_ccomponent_orbit) hQ hK.1.2.1).resolve_left hnot
  let e := subgroupOfEquivOfLe (show K ≤ K ⊔ Tv T v from le_sup_left)
  let eqv := QuotientGroup.congr (pCore 2 (K.subgroupOf (K ⊔ Tv T v))) (pCore 2 K) e
    (pCore_map_iso 2 e)
  refine ⟨hi, hm.of_mulEquiv eqv.symm, ?_⟩
  obtain ⟨t, ht, htN⟩ := SetLike.not_le_iff_exists.mp hn
  refine ⟨t, ht, htN, ?_⟩
  have hTH : Tv T v ≤ K ⊔ Tv T v := le_sup_right
  let tH : ↥(K ⊔ Tv T v) := ⟨t, hTH ht⟩
  have htH : tH ∉ normalizer (K.subgroupOf (K ⊔ Tv T v) : Set ↥(K ⊔ Tv T v)) := by
    rw [← subgroupOf_normalizer_eq (show K ≤ K ⊔ Tv T v from le_sup_left)]
    exact htN
  have hconj (s : Tv T v) : K.conjBy (s : G) = K ∨ K.conjBy (s : G) = K.conjBy t := by
    by_cases hs : (s : G) ∈ normalizer (K : Set G)
    · exact Or.inl (mem_normalizer_iff_map_conj_eq.mp hs)
    · have hsH : (⟨s, hTH s.property⟩ : ↥(K ⊔ Tv T v)) ∉
          normalizer (K.subgroupOf (K ⊔ Tv T v) : Set ↥(K ⊔ Tv T v)) := by
        rw [← subgroupOf_normalizer_eq (show K ≤ K ⊔ Tv T v from le_sup_left)]
        exact hs
      have he : tH⁻¹ * (⟨s, hTH s.property⟩ : ↥(K ⊔ Tv T v)) ∈
          normalizer (K.subgroupOf (K ⊔ Tv T v) : Set ↥(K ⊔ Tv T v)) :=
        (mul_mem_iff_of_index_two hi).mpr (by simp [htH, hsH])
      rw [← subgroupOf_normalizer_eq (show K ≤ K ⊔ Tv T v from le_sup_left)] at he
      have heq : K.conjBy (t⁻¹ * (s : G)) = K := mem_normalizer_iff_map_conj_eq.mp he
      have hh := congrArg (fun B : Subgroup G => B.conjBy t) heq
      rw [conjBy_mul, conjBy_inv'] at hh
      exact Or.inr hh
  rw [Kminus, conjugateSpanBy_eq_iSup_conj]
  apply le_antisymm
  · apply iSup_le
    intro s
    change K.conjBy (s : G) ≤ K ⊔ K.conjBy t
    rcases hconj s with he | he <;> rw [he]
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le
      (by rw [← conjugateSpanBy_eq_iSup_conj]; exact le_conjugateSpanBy K (Tv T v))
      (le_iSup (fun s : Tv T v => K.conjBy (s : G)) ⟨t, ht⟩)

/-- The marked involution's actual centralizer supplies SQTK in the source
configuration. This is the pair used in the contrary case of 13.6.14. -/
theorem marked_noninvariant_component_pair_source
    {L V : Subgroup G} (s : A5Module.Marking L V) (T K : Subgroup G)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hK : K ∈ Yz L T (A5Module.markedZ s) (A5Module.markedV s))
    (hn : ¬ Tv T (A5Module.markedV s) ≤ normalizer (K : Set G)) :
    (normalizer (K.subgroupOf (K ⊔ Tv T (A5Module.markedV s)) :
      Set ↥(K ⊔ Tv T (A5Module.markedV s)))).index = 2 ∧
      Chapter1.Section02.NonnormalCComponentModel (K ⧸ pCore 2 K) ∧
      ∃ t ∈ Tv T (A5Module.markedV s), t ∉ normalizer (K : Set G) ∧
        Kminus K T (A5Module.markedV s) = K ⊔ K.conjBy t :=
  noninvariant_component_pair_source K L T _ _
    (hG.involution_centralizer_sqtk (ComponentReduction.InitialSieve.marked_orders s).2) hK hn

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
