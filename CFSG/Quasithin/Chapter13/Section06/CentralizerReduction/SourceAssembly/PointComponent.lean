module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointComponent
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.PointQuotient

/-!
# The original outside-core component in the terminal argument

After every Sylow rechoice, identify the same point join's two-residual
as an ordinary component and its O₃′ image as the quotient's generalized
Fitting subgroup. Both local residual maps onto A₄ now have proved central
two-group kernels. All original quotient maps, the core branch and the
multiple-overgroup guard remain in the universal argument.

The residual block lift, FF comparison, nonsolvable generation bound and
single-factor endgame remain with qt-d-1367-assembly. Original Context,
13.3.2, C.1.32 and 5.2.3 retain their producers; qt-d-1361-source owns final
discharge. This is a conditional source reduction, not full 13.2.7/13.6.7.

Source: Aschbacher--Smith 13.2.12, printed pp.882--883.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open A5Module ComponentSelection ComponentElimination.SourceContainment.RankTwo.LocalApplication
open ComponentElimination.SourceSmallModels.OriginalAssembly.C132
open Section05.A5Source Section02.A5Outside
open TerminalContradiction.Components.SuzukiIsolation
open ChapterC Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Apply the original ordinary component and central residual covers
throughout the universal terminal argument. -/
theorem terminal_model_of_original_point_component_source
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
        ¬ ChapterC.IsAlternatingBlock I 5 →
        ∀ P₁ : Subgroup G, OriginalCentralization.IsOriginalPairedPointGroup e hH P₁ →
          ¬ ChapterC.IsAlternatingBlock (pResidual 2 P₁) 3 →
          P₁ ≤ H → P₁ ≤ Gv (A5Module.markedV e.flag.flag.module) →
          ChapterB.baumann (S : Subgroup G) ≤ P₁ →
          ¬ P₁ ≤ normalizer (I : Set G) →
          let P₂ := Lv I (A5Module.markedV e.flag.flag.module) ⊔ ChapterB.baumann (S : Subgroup G)
          let J := P₁ ⊔ P₂
          P₁ ⊓ P₂ = ChapterB.baumann (S : Subgroup G) →
          J ≤ Gv (A5Module.markedV e.flag.flag.module) →
          Chapter1.IsSylowIn 2 (ChapterB.baumann (S : Subgroup G)) J →
          IsSQTK KnownSimple.IsKnownSimple J →
          ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) →
          P₁.pCoreIn 2 ≠ P₂.pCoreIn 2 →
          let q := QuotientGroup.mk' (pPrimeCore 3 J)
          ChapterF.IsGoldschmidtTriple ((P₁.subgroupOf J).map q) ((P₂.subgroupOf J).map q) →
          (P₁.subgroupOf J).map q ⊓ (P₂.subgroupOf J).map q =
            ((ChapterB.baumann (S : Subgroup G)).subgroupOf J).map q →
          pCore 2 (J ⧸ pPrimeCore 3 J) = ⊥ →
          (¬ Nonempty ((((P₁.subgroupOf J).map q ⊓ (P₂.subgroupOf J).map q) : Subgroup _) ≃*
            Multiplicative (ZMod 2))) →
          pPrimeCore 2 J = ⊥ →
          (∃ R : Sylow 2 (J ⧸ pPrimeCore 3 J),
            (P₁.subgroupOf J).map q ⊓ (P₂.subgroupOf J).map q = (R : Subgroup _) ∧
            ¬ Nonempty (R ≃* FSource.C 2) ∧
            (FSource.SourceAlternative ((P₁.subgroupOf J).map q) ((P₂.subgroupOf J).map q) R ∨
              FSource.SourceAlternative ((P₂.subgroupOf J).map q) ((P₁.subgroupOf J).map q) R)) →
          let a := markedZ e.flag.flag.module * markedV e.flag.flag.module
          ((a ∈ J.pCoreIn 2 ∧ J ∈ Chapter1.He G ∧
              ∃ x : J, (x : G) = a ∧
                ∃ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
                  letI := hr.normal
                  letI := hr.elementary
                  let U := conjugateSpanBy (zpowers x) ⊤
                  let f := QuotientGroup.mk' (centralizer (U : Set J))
                  let A := P₁.subgroupOf J
                  let B := P₂.subgroupOf J
                  IsFFModule (ChapterB.InternalThompsonAction.action U) ∧
                  Group.IsSolvable (centralizer (U : Set J)) ∧
                  (f.subgroupMap A).ker = (pCore 2 J).subgroupOf A ∧
                  (f.subgroupMap B).ker = (pCore 2 J).subgroupOf B ∧
                  ∃ eA : A.map f ≃* A.map q, ∃ eB : B.map f ≃* B.map q,
                    (∀ b : A, eA (f.subgroupMap A b) = q.subgroupMap A b) ∧
                    (∀ b : B, eB (f.subgroupMap B b) = q.subgroupMap B b)) ∨
            (a ∉ J.pCoreIn 2 ∧ ¬ Group.IsSolvable (J ⧸ pPrimeCore 3 J) ∧
              ∃ x : J, (x : G) = a ∧ ∃ K : Subgroup J,
                IsComponent J K ∧ K ≠ ⊥ ∧ ⁅K,zpowers x⁆ = K ∧
                orderOf (q x) = 2 ∧
                q x ∈ omegaOneCenterAmbient ((P₁.subgroupOf J).map q ⊓ (P₂.subgroupOf J).map q) ∧
                (¬ (P₁.subgroupOf J).map q ≤ centralizer ({q x} : Set _)) ∧
                (¬ (P₂.subgroupOf J).map q ≤ centralizer ({q x} : Set _)) ∧
                generalizedFitting ((P₁.subgroupOf J).map q) = pCore 2 ((P₁.subgroupOf J).map q) ∧
                generalizedFitting ((P₂.subgroupOf J).map q) = pCore 2 ((P₂.subgroupOf J).map q) ∧
                (Nonempty ((P₁.subgroupOf J).map q ≃* Equiv.Perm (Fin 4)) ∨
                  Nonempty ((P₁.subgroupOf J).map q ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) ∧
                (Nonempty ((P₂.subgroupOf J).map q ≃* Equiv.Perm (Fin 4)) ∨
                  Nonempty ((P₂.subgroupOf J).map q ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) ∧
                (∀ M ∈ ({P₁.subgroupOf J,P₂.subgroupOf J} : Set (Subgroup J)),
                  ∃ f : pResidual 2 M →* alternatingGroup (Fin 4), Function.Surjective f ∧
                    f.ker = ((pCore 2 J).subgroupOf M).subgroupOf (pResidual 2 M) ∧
                    IsPGroup 2 f.ker ∧ f.ker ≤ center (pResidual 2 M)) ∧
                IsComponent J (pResidual 2 J) ∧
                (pResidual 2 J).map q = pResidual 2 (J ⧸ pPrimeCore 3 J) ∧
                pResidual 2 (J ⧸ pPrimeCore 3 J) = generalizedFitting (J ⧸ pPrimeCore 3 J) ∧
                pResidual 2 J ≤ centralizer (pCore 2 J : Set J))) → False)
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
  apply terminal_model_of_original_point_quotient_source d hc hmany h1332 hcontexts
    rankTwo h523 ?_ hsingle hparameter
  intro S I W W₁ W₂ W₃ e H hH hZ hs hcore hb
    P₁ horiginal hthree hPH hPG hBP hout P₂ J hinter hJv hSyl hSQ hg
    hne q hquot hi hqcore hncyc ho hrows a hbranch
  apply hpairPoint S I W W₁ W₂ W₃ e H hH hZ hs hcore hb P₁ horiginal hthree
    hPH hPG hBP hout hinter hJv hSyl hSQ hg hne hquot hi hqcore hncyc ho hrows
  rcases hbranch with hinside | ⟨ha,hns,x,hx,K,hK,hKne,hKmove,ho,hm,
      hmA,hmB,hgoodA,hgoodB,hmodelA,hmodelB,_⟩
  · exact Or.inl hinside
  · have hB := universal_baumann_normalizer_of_many T hmany S I W W₁ W₂ W₃ e
    have hz := OriginalCentralization.center_eq_bot_of_borel_join_core_eq_bot e hH hZ hcore
    have hcomponent := OriginalCentralization.point_join_residual_component_of_complement_not_mem_core
      e hH hB hZ hs hz horiginal hBP hJv hinter hSQ hg hquot hi ha
    have hres := OriginalCentralization.point_residual_central_covers_of_complement_not_mem_core
      e hH hB hZ hs hz horiginal hBP hJv hinter hSQ hg hquot hi ha
    exact Or.inr ⟨ha,hns,x,hx,K,hK,hKne,hKmove,ho,hm,
      hmA,hmB,hgoodA,hgoodB,hmodelA,hmodelB,hres,hcomponent⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
