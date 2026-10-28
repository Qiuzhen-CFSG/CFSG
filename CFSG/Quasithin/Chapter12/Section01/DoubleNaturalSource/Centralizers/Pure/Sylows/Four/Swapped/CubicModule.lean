module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Swapped.NormalModule
public import CFSG.Quasithin.Chapter3.Section02.QrcInput
public import CFSG.Quasithin.Chapter3.Section01.SourceNumericalComplete
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard.Cardinality
public import Theory.Representation.BinaryOffender.TwoSectionBudget

/-!
# The actual cubic module of the remaining swapped component

The containing overgroup H normalizes J(T), so J(T) lies in O₂(H).
That core lies in T and is normalized by K₀T, hence lies in O₂(K₀T).
The genuine Fundamental Setup module therefore centralizes J(T).
Since W <= J(T), the original centralizer identity puts this module in
O₂(LT). The same Fundamental Setup and the original multiple-overgroup
hypothesis supply the qrc configuration and its proved cubic ratio bound.
This gives an actual elementary cubic actor and its two-section budget.

The statement retains the original marked pure point, contrary ambient
Sylow assumption, fixed-subgroup premise and literal swapped quotient.
No irreducible-section or odd-PSL₂ exclusion is assumed or claimed.
Constructing the required sections, excluding the nonabelian case and
finishing ambient Sylow, core, fusion and closure remain with
qt-d-double-natural-pure-fusion. The original fixed-subgroup premise
remains with qt-rank-two-ms93 and final qt-d-double-natural-centralizers.
Source: Aschbacher--Smith 12.1.4, printed pp.790--791; the original
qrc bound 3.1.8 and Fundamental Setup 3.2.1--6, pp.576--581.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 Chapter1.XiEmbedding
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The remaining swapped component supplies an actual cubic actor on its
FSU module, which lies in the original LT core and centralizes J(T). -/
theorem doubleNatural_four_pure_cubic_module_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥ →
      let X := PureFourXi.residual T L
      ∃ (P : Sylow 2 G) (A : Sylow 3 X) (K : Subgroup G)
        (F : FundamentalSetup KnownSimple.IsKnownSimple T K),
        let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
        SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X
          ((A : Subgroup X).map X.subtype) H K ∧
        conjugateSpanBy X H = componentOrbit K (T : Subgroup G) ∧
        X < componentOrbit K (T : Subgroup G) ∧
        (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient K) 2 p ∧
          (p % 8 = 3 ∨ p % 8 = 5) ∧ (p % 24 = 11 ∨ p % 24 = 13)) ∧
        elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (F.moduleSubgroup : Set G) ∧
        F.moduleSubgroup ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
        letI := F.module_elementary
        let ρ := ChapterD.UniqueFactor.imageRepresentation (localJoin T K)
          F.moduleSubgroup F.join_normalizes_module
        cubicRatio ρ ≤ 2 ∧ HasCubicTwoSectionBudget ρ := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf hne
  obtain ⟨P,hlt,hPC,hPM,hPN,hiT,hH,hHN,hout,A,K,hs,he,hstrict,hodd,hfull,hcore,
      hmoveY,hmoveH,hcomm,hA5,hmax,hfaith,⟨F⟩,hrest⟩ :=
    D.doubleNatural_four_pure_core_interval_of_many_of_omega_fixed
      h hmany B S w hw hp hfix hf hne
  let X := PureFourXi.residual T L
  let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
  let Y := componentOrbit K (T : Subgroup G)
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans le_sup_right
  have hYH : Y ≤ H := SwappedSylow.orbit_le_overgroup hs.toSwappedInput
  have hQHT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH)
  have hJH : J ≤ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le (sSup_le fun _ hA => hA.1))
      ((sSup_le fun _ hA => hA.1).trans hTH) hHN
  have hQHJ : H.pCoreIn 2 ≤ (localJoin T K).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) (hQHT.trans le_sup_right)
      ((sup_le hYH hTH).trans (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))
  have hJF : J ≤ centralizer (F.moduleSubgroup : Set G) :=
    hJH.trans (hQHJ.trans F.core_centralizes_module)
  have hWF : componentOrbit V (T : Subgroup G) ≤ centralizer (F.moduleSubgroup : Set G) :=
    (S.four_orbit_le_thompson D.sylow_normalizes_component
      (D.doubledOrbit_E322 h).le_sylow).trans hJF
  have hFQ : F.moduleSubgroup ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [←D.doubledOrbit_sylow_centralizer h]
    exact le_inf F.module_le_sylow (le_centralizer_iff.mp hWF)
  let := F.module_elementary
  let ρ := ChapterD.UniqueFactor.imageRepresentation (localJoin T K)
    F.moduleSubgroup F.join_normalizes_module
  have h127 := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T hmax
  obtain ⟨hM,hJM,hu⟩ := F.lemma_3_2_3_uniqueness h127
  obtain ⟨I,hI⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (Chapter3.hasMaximalOutside_of_many T hmany F.maximalLocal hM
      (le_sup_right.trans hJM))
  have hc : cubicRatio ρ ≤ 2 :=
    (F.qrcHypotheses h127 hI).source_cubicRatio_le_two h.simpleQTKE hM hu F.module_ne_bot
  exact ⟨P,A,K,F,hs,he,hstrict,hodd,hJF,hFQ,hc,hasCubicTwoSectionBudget_of_le_two ρ hc⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
