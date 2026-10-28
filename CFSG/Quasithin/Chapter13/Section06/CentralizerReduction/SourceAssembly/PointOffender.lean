module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointHyperplane
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Nonsolvable
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.PointSolvable

/-!
# Complete B.5 alternatives on the original paired-point span

After the solvable F.6 row is excluded, every corrected surviving F.6 row
makes the original point join nonsolvable. The proved solvable kernel of its
faithful span action then makes that action quotient nonsolvable as well.
Complete B.5 applies to its actual normal offender subgroup; the marked
second residual and its moved support exclude the symmetric-three case.
The common Sylow comparison transports the F.6 order bound to the action,
which bounds every field parameter in the quasisimple B.5 alternative.

Sylow averaging excludes the hyperplane case on this same action.
The universal callback receives the three remaining B.5 alternatives,
including their literal module clauses, after every Sylow rechoice. The
multiple-overgroup guard and both distinct ambient quotient maps are retained.
The nonsolvable comparison, generation bound, single-factor endgame, and
earlier-source discharges remain obligations of the full assembly.

Source: Aschbacher--Smith 13.2.12, printed p.882; B.5.3--6 and F.6.18.
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

/-- The original universal comparison receives nonsolvability and the three
remaining corrected B.5 alternatives on its literal offender action. -/
theorem terminal_model_of_original_point_offender_source
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
  apply terminal_model_of_original_point_solvable_exclusion_source d hc hmany h1332 hcontexts
    rankTwo h523 ?_ hsingle hparameter
  intro S I W W₁ W₂ W₃ e H hH hZ hs hcore hb
    P₁ horiginal hthree hPH hPG hBP hout P₂ J hinter hJv hSyl hSQ hg
    hne q hquot hi hqcore hncyc ho hrows hnotrow a hbranch
  have hB := universal_baumann_normalizer_of_many T hmany S I W W₁ W₂ W₃ e
  have hz := OriginalCentralization.center_eq_bot_of_borel_join_core_eq_bot e hH hZ hcore
  have hnq : ¬ Group.IsSolvable (J ⧸ pPrimeCore 3 J) := by
    obtain ⟨R,_,hnR,hR⟩ := hrows
    rcases hR with hR | hR
    · exact FSource.source_alternative_nonsolvable hR hnR hnotrow
    · exact FSource.source_alternative_nonsolvable hR hnR hnotrow
  have hnJ : ¬ Group.IsSolvable J := by
    intro hsol
    let := hsol
    exact hnq (Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _))
  rcases hbranch with ⟨ha,hHe,x,hx,hr,hlarge,hsupport,hres,hff,hdata⟩
  let := hr.normal
  let := hr.elementary
  have hnaction : ¬ Group.IsSolvable (J ⧸ centralizer (conjugateSpanBy (zpowers x) ⊤ : Set J)) := by
    intro hsol
    exact hnJ ((Group.isSolvable_iff_subgroup_quotient _).mpr ⟨hdata.1,hsol⟩)
  have hrows' : ∃ R : Sylow 2 (J ⧸ pPrimeCore 3 J),
      FSource.SourceAlternative ((P₁.subgroupOf J).map q) ((P₂.subgroupOf J).map q) R ∨
      FSource.SourceAlternative ((P₂.subgroupOf J).map q) ((P₁.subgroupOf J).map q) R := by
    obtain ⟨R,_,_,hR⟩ := hrows
    exact ⟨R,hR⟩
  have hsmall := OriginalCentralization.point_action_sylow_card_le
    e hH hB hZ hs hz horiginal hPG hinter hg hrows' x hx hr
  have hclass := OriginalCentralization.point_offender_bounded_source_alternatives
    e hH hB hZ hs hz horiginal hPG hinter hSQ hg hne hrows' x hx hr hff
  have hnh := OriginalCentralization.point_offender_not_hyperplane
    e hH hB hZ hs hz (le_sup_right.trans le_sup_right) hJv x hx hr
  have hremaining := hclass.imp id (fun h => h.imp id (fun h => h.resolve_right hnh))
  apply hpairPoint S I W W₁ W₂ W₃ e H hH hZ hs hcore hb P₁ horiginal hthree
    hPH hPG hBP hout hinter hJv hSyl hSQ hg hne hquot hi hqcore hncyc ho hrows hnotrow hnq hnJ
  exact ⟨ha,hHe,x,hx,hr,hlarge,hsupport,hres,hnaction,hsmall,hremaining,hff,hdata⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
