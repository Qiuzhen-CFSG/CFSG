module

public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.ContainingQuotients
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.PrimePSL2
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits

/-!
# The nonnormal containing rows of the local Cartan sieve

Unique containment and Sylow invariance show that an unmoved seed can only
have a normal containing component. For a nonnormal container, source
1.2.1(3) gives index two and four genuine quotient models. The previously
proved Bender exclusion removes the even linear and Suzuki rows. The
proper odd-prime embedding theorem gives both exceptional congruences and
identifies the actual seed image in Y/O₂(Y) as A₅. J₁ remains explicit.

The models concern C/O₂(C), via its literal image in Y/O₂(Y); no solvable
core is substituted for this kernel. The remaining action exclusions of
these two rows belong to the local Cartan sieve assembly.

Source: Aschbacher–Smith A.3.12(8), 1.2.1(3), and 5.1.12(2),
printed pp.47–48,504,635.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

/-- A nonnormal containing component forces the original seed to be moved by T. -/
theorem nonnormal_container_seed_moved
    {T : Sylow 2 G} {K H Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hn : ¬ C.Normal) : K ≠ residual H := by
  intro he
  have hTY := hTH.trans hY.2
  have hKY := hKH.trans hY.2
  let S := T.subtype hTY
  have hl : K.subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTY hKY).mp ⟨hKY, hK⟩
  have hKC' : K.subgroupOf Y ≤ C := by
    change K.comap Y.subtype ≤ C
    have hh := comap_mono (f := Y.subtype) hKC
    simpa only [comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have hQ := Chapter1.Section02.uniqueness_local_quotient_sqtk hG hY.1
  obtain ⟨J, _, hu⟩ := Chapter1.Section02.lemma_1_2_4_containment_of_A_3_12
    (Chapter1.Section02.containment_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))) hQ S hl
  have hnorm : (S : Subgroup Y) ≤ normalizer (K.subgroupOf Y : Set Y) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro x
    have htK : (t : G) ∈ normalizer (K : Set G) := by
      rw [he]
      exact (hTH.trans (le_normalizer_residual H)) ht
    exact mem_normalizer_iff.mp htK (x : G)
  apply hn
  exact cComponent_normal_of_unique_of_orbit_two hC hKC'
    (fun E hE hKE => (hu E ⟨hE, hKE⟩).trans (hu C ⟨hC, hKC'⟩).symm) S hnorm
    (Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hC)

/-- The nonnormal containing quotient is J₁ or the exact exceptional odd-prime PSL₂ row. -/
theorem nonnormal_container_models
    {T : Sylow 2 G} {K H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hn : ¬ C.Normal) :
    (normalizer (C : Set Y)).index = 2 ∧
      (Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∨
        ∃ p : ℕ, Chapter1.Section02.A312ExceptionalPrime p ∧
          ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p ∧
          Chapter1.Section02.LocalModels.IsAlternating
            ((K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))) 5) := by
  obtain ⟨hi, hm⟩ := (Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
    (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hY.1) hC).resolve_left hn
  refine ⟨hi, ?_⟩
  have hnot := not_bender_container hG hKH hTH hK horbit hY hescape C hC hKC
  cases hm with
  | linear_even m hm he => exact (hnot (.linear m hm he)).elim
  | suzuki m hm he => exact (hnot (.suzuki m hm he)).elim
  | janko he => exact Or.inl he
  | linear_prime p hp ho he =>
    let S := T.subtype (hTH.trans hY.2)
    let q := QuotientGroup.mk' (pCore 2 Y)
    let := pCore_isNilpotent (p := 2) (G := Y)
    have hl : K.subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
      (Chapter1.mem_LIn_iff_subgroupOf (hTH.trans hY.2) (hKH.trans hY.2)).mp
        ⟨hKH.trans hY.2, hK⟩
    have hlq : (K.subgroupOf Y).map q ∈
        ChapterA.Section03.localCComponents (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y)) :
          Subgroup (Y ⧸ pCore 2 Y)) := by
      simpa only [Sylow.coe_mapSurjective] using
        Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hl
    have hlt := seed_image_lt_container hG hKH hTH hK horbit hY hescape C hC hKC
    obtain ⟨hprime, hsmall⟩ := ChapterA.Section03.SourceEmbeddings.proper_primePSL2_models
      (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))) hlq
      (hC.map_quotient _) hlt.le hlt.ne hp ho
      (he.of_mulEquiv (cComponentTwoCoreQuotientEquiv hC).symm)
    exact Or.inr ⟨p, hprime, he, hsmall⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
