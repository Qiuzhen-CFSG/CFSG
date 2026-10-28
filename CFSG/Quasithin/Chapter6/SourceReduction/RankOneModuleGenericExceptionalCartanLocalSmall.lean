module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalLieParabolic
public import Theory.SpecificGroups.PSL3Two.SolvableSylowOvergroups
public import Theory.SpecificGroups.G2.BinarySolvableSylowOvergroups
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.Tits.SolvableSylowOvergroups
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock

/-!+# Small containing quotients in the original local Cartan sieve

The seed remains proper in the literal quotient Y/O₂(Y). Restricting its
full Sylow to the containing component shows that a quotient with solvable
proper Sylow overgroups would identify the two images. This excludes the
binary linear-three models, the binary derived symplectic and G₂ models,
and the Tits group, without a cubic or a relative-normality assumption.

Together with the large-field parabolic argument, the complete rank-two
Theorem C catalogue reduces to genuine binary triality. This is a remaining
case, not an assertion that the source Cartan theorem has been proved.

Source: Aschbacher--Smith A.3.12 and 5.1.12--13, printed pp.47--48,635--636.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- A proper containing quotient cannot have solvable proper Sylow overgroups.
Both images use the original quotient of Y by its two-core. -/
theorem not_solvableSylow_container
    {T : Sylow 2 G} {K H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype) :
    ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) := by
  intro hs
  let S := T.subtype (hTH.trans hY.2)
  let q := QuotientGroup.mk' (pCore 2 Y)
  let := pCore_isNilpotent (p := 2) (G := Y)
  have hl : K.subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf (hTH.trans hY.2) (hKH.trans hY.2)).mp
      ⟨hKH.trans hY.2,hK⟩
  have hlq : (K.subgroupOf Y).map q ∈ ChapterA.Section03.localCComponents
      (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y)) : Subgroup (Y ⧸ pCore 2 Y)) := by
    simpa only [Sylow.coe_mapSurjective] using
      Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hl
  have hlt := seed_image_lt_container hG hKH hTH hK horbit hY hescape C hC hKC
  exact hlt.ne (ChapterA.Section03.SourceEmbeddings.eq_of_solvable_sylow_overgroups
    (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))) hlq
    (hC.map_quotient _) hlt.le
    (SolvableSylowOvergroups.of_equiv (cComponentTwoCoreQuotientEquiv hC).symm hs))

/-- The small binary endpoints are excluded on the original seed, including
a moved seed. The derived models are not replaced by their full groups. -/
theorem not_small_binary_container
    {T : Sylow 2 G} {K H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype) :
    ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 2 ∨
      IsSL (C ⧸ pCore 2 C) 3 2 ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* Tits.ParrottGroup)) := by
  intro hm
  apply not_solvableSylow_container hG hKH hTH hK horbit hY hescape C hC hKC
  rcases hm with hm | hm | hm | hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact SolvableSylowOvergroups.of_equiv e
      (Matrix.PSL3Two.solvableSylowOvergroups_projective_of_card_two hF)
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact SolvableSylowOvergroups.of_equiv e
      (Matrix.PSL3Two.solvableSylowOvergroups_specialLinear_of_card_two hF)
  · obtain ⟨e⟩ := hm
    exact SolvableSylowOvergroups.of_equiv
      (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
      AlternatingSix.ProperSylowOvergroups.isSolvable
  · obtain ⟨e⟩ := hm
    exact SolvableSylowOvergroups.of_equiv e Atlas.G2.BinaryDerived.solvableSylowOvergroups
  · obtain ⟨e⟩ := hm
    exact SolvableSylowOvergroups.of_equiv e Tits.ProperSylowOvergroups.solvableSylowOvergroups

/-- The whole characteristic-two rank-two catalogue leaves only binary
triality in the original escaping branch. -/
theorem rankTwo_container_binaryTriality
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : RankTwoTheoremC (C ⧸ pCore 2 C)) :
    Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) := by
  have hs := not_small_binary_container h.qtke hKH hH.1.1.2 hK horbit hY hescape C hC hKC
  cases hm with
  | linear k hk hm =>
    by_cases hk2 : 1 < k
    · exact (not_classical_rankTwo_container h hH hgen c hKH hK horbit hY hescape
        C hC hKC hk2 (.inl hm)).elim
    · have he : k = 1 := by omega
      subst k
      exact (hs (.inl (by simpa only [pow_one] using hm))).elim
  | symplectic k hk hm =>
    exact (not_classical_rankTwo_container h hH hgen c hKH hK horbit hY hescape
      C hC hKC (by omega) (.inr (.inr hm))).elim
  | g2 k hk hm =>
    exact (not_g2_container h hH hgen c hKH hK horbit hY hescape C hC hKC (by omega) hm).elim
  | triality k hk hm =>
    by_cases hk2 : 1 < k
    · exact (not_triality_container h hH hgen c hKH hK horbit hY hescape C hC hKC hk2 hm).elim
    · have he : k = 1 := by omega
      subst k
      simpa only [pow_one] using hm
  | ree m hm he =>
    obtain ⟨b,⟨e⟩⟩ := he
    exact (not_ree_container h hH hgen c hKH hK horbit hY hescape C hC hKC
      ⟨m,hm,⟨e.trans b.modelEquiv⟩⟩).elim
  | symplectic_derived hm => exact (hs (.inr (.inr (.inl hm)))).elim
  | g2_derived hm => exact (hs (.inr (.inr (.inr (.inl hm))))).elim
  | tits hm => exact (hs (.inr (.inr (.inr (.inr hm))))).elim

/-- Both linear-three forms and the full special-unitary-three cover are
excluded at every positive binary exponent. -/
theorem not_binary_ternary_container
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n m : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : 0 < m) :
    ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
      IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m)) := by
  rintro (he | he | he)
  · by_cases hm2 : 1 < m
    · exact not_classical_rankTwo_container h hH hgen c hKH hK horbit hY hescape C hC hKC hm2 (.inl he)
    · have hm1 : m = 1 := by omega
      exact not_small_binary_container h.qtke hKH hH.1.1.2 hK horbit hY hescape C hC hKC
        (.inl (by simpa only [hm1,pow_one] using he))
  · by_cases hm2 : 1 < m
    · exact not_classical_rankTwo_container h hH hgen c hKH hK horbit hY hescape C hC hKC hm2 (.inr (.inl he))
    · have hm1 : m = 1 := by omega
      exact not_small_binary_container h.qtke hKH hH.1.1.2 hK horbit hY hescape C hC hKC
        (.inr (.inl (by simpa only [hm1,pow_one] using he)))
  · exact not_binary_su3_container h.qtke hKH hH.1.1.2 hK horbit hY hescape C hC hKC m hm he

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
