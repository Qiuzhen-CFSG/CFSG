module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.Baumann
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.PairedPoint
public import Theory.GroupTheory.MaximalTwoLocalTransport

/-!
# Independent Baumann and fusion inputs in the universal A₅ argument

Original 5.1.7 gives the Baumann normalizer bound on each genuine Context.
The number of maximal two-local overgroups is unchanged under Sylow
conjugacy, so the single standing guard supplies that bound after every
Sylow rechoice. The original flag index and characteristic Baumann subgroup
then make C_T(v) Sylow in C_G(v). Separation of the two marked classes gives
both literal fusion callbacks and full L-control of fusion on V.

The final theorem applies the bound to the original universal paired-point
terminal argument. The paired nonblock/equal-core and F.6.18 exclusions,
nonsolvable generation bound, and single-factor endgame remain with
qt-d-1367-assembly. The earlier Context/13.3.2, C.1.32 and 5.2.3 producers
retain their premises; qt-d-1361-source owns final classification assembly.
This proves the independent 13.2.5 input and its fusion consequences, not
unconditional 13.2.7 or 13.6.7.

Source: Aschbacher--Smith 13.2.5--7, printed pp.879--880, and the
13.2.12 paired point amalgam on pp.881--883.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open A5Module ComponentSelection ComponentElimination.SourceContainment.RankTwo.LocalApplication
open ComponentElimination.SourceSmallModels.OriginalAssembly.C132
open Section05.A5Source Section02.A5Outside
open TerminalContradiction.Components.SuzukiIsolation
open ChapterC Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The genuine guard at T supplies the independent bound at every reselected
Sylow S and its original A₅ Context. -/
theorem universal_baumann_normalizer_of_many
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
        normalizer (ChapterB.baumann (S : Subgroup G) : Set G) ≤ normalizer (I : Set G) := by
  intro S I W W₁ W₂ W₃ e
  apply OriginalCentralization.baumann_normalizer_of_many e
  rwa [maximalTwoLocalOvergroups_ncard_sylow S T]

/-- Original 13.2.6(1) on the actual marked nonsingular point: the Sylow
subgroup of its full centralizer has exactly C_T(v) as ambient image. -/
theorem point_centralizer_sylow_of_many
    {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV d.flag.flag.module))
      (Gv (markedV d.flag.flag.module)) := by
  have hS := baumann_le_Tv_of_alternatives T V V₂ (markedV d.flag.flag.module)
    (map_mem d.flag.flag.module _) d.flag.flag.vector_mem (baumann_alternatives d)
  have hSJ := baumann_and_thompson_centralizer (T : Subgroup G) _ hS
  have hMV : Mv (normalizer (L : Set G)) (markedV d.flag.flag.module) ≤
      normalizer (V : Set G) :=
    inf_elementCentralizer_le_normalizer_of_trivial_intersections
      d.trivial_intersections (map_mem d.flag.flag.module _) (markedV_ne_one d.flag.flag.module)
  have hcontrol := baumann_normalizer_control (T : Subgroup G) (normalizer (L : Set G)) V
    (markedV d.flag.flag.module) (OriginalCentralization.baumann_normalizer_of_many d hmany)
    hMV d.module_normalizer
  let B : Subgroup (Tv (T : Subgroup G) (markedV d.flag.flag.module)) := ChapterB.baumann ⊤
  let : B.Characteristic := ChapterB.baumann_characteristic
  have hB : B.map (Tv (T : Subgroup G) (markedV d.flag.flag.module)).subtype =
      ChapterB.baumann (Tv (T : Subgroup G) (markedV d.flag.flag.module)) := by
    simpa only [B, ChapterB.baumann, ChapterB.thompsonAlpha,
      ← MonoidHom.range_eq_map, range_subtype] using
      baumann_map_injective (Tv (T : Subgroup G) (markedV d.flag.flag.module)).subtype
        (Tv (T : Subgroup G) (markedV d.flag.flag.module)).subtype_injective ⊤
  apply exists_sylow_centralizer T (normalizer (L : Set G)) _ B
  · rw [hcontrol.2]
    exact d.flag.flag_localIndex
  · rw [hB, ← hSJ.1]
    exact OriginalCentralization.baumann_normalizer_of_many d hmany

/-- Original 13.2.6 fusion follows before 13.2.7, using only the original
Context and the multiple-overgroup guard. -/
theorem fusion_of_many
    {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ControlsFusionOfZ d.flag.flag.module ∧ FusionPreservesForm d.flag.flag.module := by
  have hS := baumann_le_Tv_of_alternatives T V V₂ (markedV d.flag.flag.module)
    (map_mem d.flag.flag.module _) d.flag.flag.vector_mem (baumann_alternatives d)
  exact fusion d hS (OriginalCentralization.baumann_normalizer_of_many d hmany)

/-- The full original L-control of fusion on V, with the actual conjugators
in L and without the later nonsingular-centralizer containment. -/
theorem controls_fusion_of_many
    {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∀ x ∈ V, x ≠ 1 → ∀ g : G, MulAut.conj g x ∈ V →
      ∃ l : L, MulAut.conj (l : G) x = MulAut.conj g x := by
  have hS := baumann_le_Tv_of_alternatives T V V₂ (markedV d.flag.flag.module)
    (map_mem d.flag.flag.module _) d.flag.flag.vector_mem (baumann_alternatives d)
  exact d.flag.flag.module.controls_fusion_of_nonconjugate
    (marked_not_conjugate d hS (OriginalCentralization.baumann_normalizer_of_many d hmany))

/-- The universal terminal application now discharges the independent Baumann
bound at every original Context, transporting the actual guard from T. -/
theorem terminal_model_of_original_baumann_source
    {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
    (hc : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (rankTwo : ∀ (J : Type u) [Group J] [Finite J] (B R : Subgroup J),
      SmallMSPair KnownSimple.IsKnownSimple B R → RankTwoAlternatives B R)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hpairPoint : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G)
      (e : Context S I W W₁ W₂ W₃),
      ∀ (H : Subgroup G) (hH : H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G))),
        ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) →
        Group.IsSolvable H →
        (H ⊔ borelResidual S I).pCoreIn 2 = ⊥ →
        ∀ P₁ : Subgroup G, OriginalCentralization.IsOriginalPairedPointGroup e hH P₁ →
          P₁ ≤ H → P₁ ≤ Gv (A5Module.markedV e.flag.flag.module) →
          ChapterB.baumann (S : Subgroup G) ≤ P₁ →
          ¬ P₁ ≤ normalizer (I : Set G) →
          let P₂ := Lv I (A5Module.markedV e.flag.flag.module) ⊔ ChapterB.baumann (S : Subgroup G)
          let J := P₁ ⊔ P₂
          P₁ ⊓ P₂ = ChapterB.baumann (S : Subgroup G) →
          J ≤ Gv (A5Module.markedV e.flag.flag.module) →
          Chapter1.IsSylowIn 2 (ChapterB.baumann (S : Subgroup G)) J →
          IsSQTK KnownSimple.IsKnownSimple J →
          ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) → False)
    (hsingle : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) →
        let J := H ⊔ borelResidual S I
        let P := (borelResidual S I ⊔ (S : Subgroup G)).subgroupOf J
        let Q := H.subgroupOf J
        let q := QuotientGroup.mk' (pPrimeCore 3 J)
        IsSQTK KnownSimple.IsKnownSimple J →
        ChapterF.IsGoldschmidtTriple P Q →
        ChapterF.IsGoldschmidtTriple (P.map q) (Q.map q) →
        P.map q ⊓ Q.map q = ((S : Subgroup G).subgroupOf J).map q →
        pCore 2 (J ⧸ pPrimeCore 3 J) = ⊥ → False)
    (hparameter : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) →
        ¬ Group.IsSolvable H →
        (pResidual 2 H).map H.subtype ∈ MainForward.faithfulLocalComponents S →
        (pResidual 2 H).map H.subtype ∈ Chapter1.LStar G (S : Subgroup G) →
        Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃*
          alternatingGroup (Fin 5)) →
        centralizer ((omegaOrbit S H).subgroupOf H : Set H) = pCore 2 H →
        1 < ChapterE.generationParameter H) :
    ClassificationModels.IsQTKEModel G := by
  exact terminal_model_of_original_paired_point_triple d hc hmany h1332 hcontexts
    rankTwo h523 (universal_baumann_normalizer_of_many T hmany)
    hpairPoint hsingle hparameter

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
