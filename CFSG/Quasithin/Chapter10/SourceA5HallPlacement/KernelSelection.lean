module
public import CFSG.Quasithin.Chapter10.SourceA5HallGeneration
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.FixedSubgroup
public import CFSG.Quasithin.Chapter4.Section01.NormalizerUniqueness
/-!
# An actual elementary Hall kernel permuting with the original Sylow

The section centralizer of L₀ is normal in M. The intrinsic E.2.2 Hall
witness supplies the literal Frattini factorization of T inside H. Hence
any nontrivial kernel of its odd Hall action contains an elementary odd
prime subgroup preserved by the Hall normalizer and permuting with T.
The ambient image remains inside the actual H ∩ M and section centralizer.

This discharges the permutation requirement in source 4.4.13(2) for the
original 10.2.3 Hall kernel. Its normalizer escape and exclusion by 4.4.3
are separate source steps.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual Hall-kernel prime subgroup, with its original ambient inclusion. -/
theorem source_hall_sectionKernel_elementary
    {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hP : IsMinimalParabolicOver (T.subtype hTH) ⊤) {n : ℕ}
    (d : IntrinsicHallCartanData (T.subtype hTH) hP n)
    (hne : d.witness.abelianGroup ⊓
      (sectionCentralizer (localOrbit T L)).subgroupOf H ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup H), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ d.witness.abelianGroup ∧
      A.map H.subtype ≤ sectionCentralizer (localOrbit T L) ∧
      (A.map H.subtype : Set G) * (T : Set G) =
        (T : Set G) * (A.map H.subtype : Set G) := by
  let C := sectionCentralizer (localOrbit T L)
  have hCM : C ≤ normalizer (localOrbit T L : Set G) := ((le_sectionCentralizer_iff C _).mp le_rfl).1
  have hMC : normalizer (localOrbit T L : Set G) ≤ normalizer (C : Set G) := by
    have hh := sectionCentralizerIn_normalized (M := normalizer (localOrbit T L : Set G)) (X := localOrbit T L) le_rfl
    rwa [sectionCentralizerIn,inf_eq_right.mpr hCM] at hh
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_normalizer_componentOrbit L T).trans hMC
  have hTC' : ((T.subtype hTH : Sylow 2 H) : Subgroup H) ≤
      normalizer (C.subgroupOf H : Set H) :=
    (comap_mono hTC).trans (le_normalizer_comap H.subtype)
  obtain ⟨p,A,hp,ho,hA,hE,hAC,_,hperm⟩ :=
    exists_elementary_odd_invariant_permuting d.witness.abelian d.witness.odd hne
      hTC' d.frattini d.normalizes
  refine ⟨p,A,hp,ho,hA,hE,hAC.trans inf_le_left,
    map_le_iff_le_comap.mpr (hAC.trans inf_le_right),?_⟩
  have hh := congrArg (Set.image H.subtype) hperm
  rw [Set.image_mul,Set.image_mul] at hh
  change (A.map H.subtype : Set G) *
      (((T : Subgroup G).subgroupOf H).map H.subtype : Set G) =
    (((T : Subgroup G).subgroupOf H).map H.subtype : Set G) * (A.map H.subtype : Set G) at hh
  simpa only [map_subgroupOf_eq_of_le hTH,Sylow.coe_coe] using hh

/-- The original H-star member supplies its Hall witness and either faithful
orbit action or the actual elementary odd kernel required by the source. -/
theorem source_a5_hstar_hall_kernel_alternative
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) :
    let hP := source_a5_hstar_minimal_parabolic D e hn hH
    ∃ n : ℕ, IsEGenerated n H ∧ generationParameter H ≤ n ∧
      ∃ d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n,
        minimalParabolicMax (T.subtype hH.1.1.2) hP = D.maximalLocal.subgroupOf H ∧
        (d.witness.abelianGroup ⊓ (sectionCentralizer (localOrbit T L)).subgroupOf H = ⊥ ∨
          ∃ (p : ℕ) (A : Subgroup H), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
            IsElementaryAbelian p A ∧ A ≤ d.witness.abelianGroup ∧
            A.map H.subtype ≤ sectionCentralizer (localOrbit T L) ∧
            (A.map H.subtype : Set G) * (T : Set G) =
              (T : Set G) * (A.map H.subtype : Set G)) := by
  obtain ⟨n,hg,hb,d,hm,_⟩ := source_a5_hstar_cartan_data D e hn hH hlarge
  refine ⟨n,hg,hb,d,hm,?_⟩
  by_cases hk : d.witness.abelianGroup ⊓ (sectionCentralizer (localOrbit T L)).subgroupOf H = ⊥
  · exact Or.inl hk
  · exact Or.inr (source_hall_sectionKernel_elementary hH.1.1.2 _ d hk)
end CFSG.Quasithin.Chapter10
