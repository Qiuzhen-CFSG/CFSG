module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeQuinticSolvableLocal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicOrbit

/-!
# Quintic source filters for the chosen Chapter 12 module

The proved source selection supplies the same zero-core prime pair. The
chosen-module Input supplies quasithinness of its generated subgroup;
the quintic local calculation supplies normality in the whole Borel and
the exclusions on the actual starred left quotient. The small Ree type
clauses already contradict the nonsolvable right parabolic. No extra model or
Sylow-in-the-generated-group assumption is required.

The remaining quintic opposite-solvability theorem must select an exhaustive
DGS alternative and contradict the retained nonsolvable right endpoint.
This application does not assert that missing selection or p ≠ 5.
Source: Aschbacher–Smith 5.2.2 and 12.2.2, printed pp.647–648 and 795;
DGS Part II, 6.1 and 12.9–13.1.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- Source selection, inherited quasithinness and the new quintic exclusions
all concern one original pair and its full Borel. -/
theorem rankOne_cartan_quintic_source_filters
    {T : Sylow 2 G} {L V H A B D : Subgroup G} {n : ℕ}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H 5 D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (generated L H D R).pCoreIn 2 = ⊥ ∧
      let S := Global.sourceS L H
      let P := ChapterF.Source.starredParabolic ![D ⊔ S,R] S 0
      let Q := ChapterF.Source.parabolic ![D ⊔ S,R] S 1
      ChapterF.Source.HypothesisF11 ![D ⊔ S,R] S ∧
      IsQuasithin (ChapterF.Source.generated ![D ⊔ S,R] S) ∧
      (S.subgroupOf (ChapterF.Source.commonBorel ![D ⊔ S,R] S)).Normal ∧
      ¬ Group.IsSolvable (ChapterF.Source.parabolic ![D ⊔ S,R] S 1) ∧
      ¬ (ClassicalGroup.IsPSL (Q ⧸ pCore 2 Q) 2 2 ∨
        Nonempty ((Q ⧸ pCore 2 Q) ≃*
          BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
      (∀ f : ℕ, 0 < f →
        ¬ ClassicalGroup.IsPSL (P ⧸ pCore 2 P) 2 (2 ^ f) ∧
        ¬ ClassicalGroup.IsPSU (P ⧸ pCore 2 P) 3 (2 ^ f) ∧
        ¬ ChapterF.Source.IsSU (P ⧸ pCore 2 P) 3 (2 ^ f)) ∧
      (∀ m : ℕ, Nonempty ((P ⧸ pCore 2 P) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) → m = 0) := by
  let hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨R,d,hs,hz,hf⟩ := C.rankOne_cartan_source_prime_pair_zero_core
    h hmany hn hpsl hH hgen hthree c hd
  refine ⟨R,d,hs,hz,hf,hi.qtke.quasithin.subgroup _,
    hf.quintic_normal_borel le_sup_right,d.right_parabolic_not_solvable hz,
    d.quintic_not_small_ree_type_quotients hi hH c hd hz,?_⟩
  exact d.quintic_starred_quotient_filters hi hH c hd hz

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
