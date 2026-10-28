module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointPrimeComparison
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.PointOffender

/-!
# Residual generation and the original quotient comparison

The universal paired-point consumer now receives the actual two-residual
containment in the offender subgroup, its two-group quotient, and the
trivial prime-to-three core of the faithful action. The resulting surjection
from the original F.6 quotient commutes with both original projections and
has the literal solvable centralizer image as kernel.

Every corrected B.5 and F.6 alternative is retained, together with the
multiple-overgroup guard after each Sylow rechoice. The nonsolvable model
comparison, generation-parameter bound and single-factor endgame remain
necessary for original 13.2.7 and13.6.7. Earlier-source premises are still
explicit and must be discharged by their original producers.

Source: Aschbacher--Smith 13.2.12, printed p.882; B.5.3--6 and F.6.8--18.
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
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual original projections, residual containment and solvable kernel
are available in the universal paired-point comparison after every rechoice. -/
theorem terminal_model_of_original_point_prime_comparison_source
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
          (¬ (Nonempty ((J ⧸ pPrimeCore 3 J) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
            ∃ N : Subgroup (J ⧸ pPrimeCore 3 J), ∃ _ : N.Normal,
              IsExtraspecial 3 N ∧ Nat.card N = 27 ∧ Monoid.exponent N = 3 ∧
              Nonempty (((J ⧸ pPrimeCore 3 J) ⧸ N) ≃* FSource.E4))) →
          (¬ Group.IsSolvable (J ⧸ pPrimeCore 3 J)) →
          (¬ Group.IsSolvable J) →
          let a := markedZ e.flag.flag.module * markedV e.flag.flag.module
          (a ∈ J.pCoreIn 2 ∧ J ∈ Chapter1.He G ∧
              ∃ x : J, (x : G) = a ∧
                ∃ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
                  letI := hr.normal
                  letI := hr.elementary
                  let U := conjugateSpanBy (zpowers x) ⊤
                  let f := QuotientGroup.mk' (centralizer (U : Set J))
                  let A := P₁.subgroupOf J
                  let B := P₂.subgroupOf J
                  4 < Nat.card U ∧
                  (let K := (Lv I (markedV e.flag.flag.module)).subgroupOf J
                   (K.map f).Normal → ⁅U,K⁆ = U ∧
                     4 < Nat.card (Representation.BinaryOffender.subspaceCommutator
                       (ChapterB.InternalThompsonAction.action U) ⊤ (K.map f))) ∧
                  (¬ IsMulCommutative (pResidual 2 (J ⧸ centralizer (U : Set J)))) ∧
                  (¬ Group.IsSolvable (J ⧸ centralizer (U : Set J))) ∧
                  (∀ R : Sylow 2 (J ⧸ centralizer (U : Set J)), Nat.card R ≤ 128) ∧
                  (let ρ := ChapterB.InternalThompsonAction.action U
                   let N := offenderSubgroup ρ
                   letI := offenderSubgroup_normal ρ
                   pResidual 2 (J ⧸ centralizer (U : Set J)) ≤ N ∧
                     IsPGroup 2 ((J ⧸ centralizer (U : Set J)) ⧸ N)) ∧
                  (pPrimeCore 3 (J ⧸ centralizer (U : Set J)) = ⊥ ∧
                   pPrimeCore 3 J ≤ centralizer (U : Set J) ∧
                   ∃ g : (J ⧸ pPrimeCore 3 J) →* (J ⧸ centralizer (U : Set J)),
                     Function.Surjective g ∧ (∀ j : J, g (q j) = f j) ∧
                     g.ker = (centralizer (U : Set J)).map q ∧ Group.IsSolvable g.ker) ∧
                  (let ρ := ChapterB.InternalThompsonAction.action U
                   let N := offenderSubgroup ρ
                   let σ := ρ.comp N.subtype
                   Nonempty (QuasisimpleComparison.BoundedBranch σ) ∨
                   Nonempty (ChapterB.SourceInduction.SourceTwoFactorCase σ) ∨
                   Nonempty (ChapterB.OuterSixThreeShape N)) ∧
                  IsFFModule (ChapterB.InternalThompsonAction.action U) ∧
                  Group.IsSolvable (centralizer (U : Set J)) ∧
                  (f.subgroupMap A).ker = (pCore 2 J).subgroupOf A ∧
                  (f.subgroupMap B).ker = (pCore 2 J).subgroupOf B ∧
                  ∃ eA : A.map f ≃* A.map q, ∃ eB : B.map f ≃* B.map q,
                    (∀ b : A, eA (f.subgroupMap A b) = q.subgroupMap A b) ∧
                    (∀ b : B, eB (f.subgroupMap B b) = q.subgroupMap B b)) → False)
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
  apply terminal_model_of_original_point_offender_source d hc hmany h1332 hcontexts
    rankTwo h523 ?_ hsingle hparameter
  intro S I W W₁ W₂ W₃ e H hH hZ hs hcore hb
    P₁ horiginal hthree hPH hPG hBP hout P₂ J hinter hJv hSyl hSQ hg
    hne q hquot hi hqcore hncyc ho hrows hnotrow hnq hnJ a hbranch
  have hB := universal_baumann_normalizer_of_many T hmany S I W W₁ W₂ W₃ e
  have hz := OriginalCentralization.center_eq_bot_of_borel_join_core_eq_bot e hH hZ hcore
  rcases hbranch with ⟨ha,hHe,x,hx,hr,hlarge,hsupport,hres,hnaction,hsmall,hremaining,hff,hdata⟩
  let := hr.normal
  let := hr.elementary
  have hgen := OriginalCentralization.point_action_residual_le_offender
    e hH hB hZ hs hz horiginal hBP hPG hinter hg x hx hr
  have hbridge := OriginalCentralization.point_action_prime_comparison
    e hH hB hZ hs hz horiginal hBP hPG hinter hSQ hg x hx hr hff
  apply hpairPoint S I W W₁ W₂ W₃ e H hH hZ hs hcore hb P₁ horiginal hthree
    hPH hPG hBP hout hinter hJv hSyl hSQ hg hne hquot hi hqcore hncyc ho hrows hnotrow hnq hnJ
  exact ⟨ha,hHe,x,hx,hr,hlarge,hsupport,hres,hnaction,hsmall,hgen,hbridge,hremaining,hff,hdata⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
