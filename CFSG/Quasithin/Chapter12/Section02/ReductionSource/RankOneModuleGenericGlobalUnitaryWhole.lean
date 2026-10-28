module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryWhole
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySplit

/-!
# The whole unitary overcomponent core and left-core normalizer

The same original overcomponent has O₂(J) = K ∩ O₂(J), with its entire
natural or dual action and order q³, including the degree-two extension.
The index of K in J is q³-1, so the common Sylow is also the full Sylow
of J. Original uniqueness places N_J(O₂(L)) in N_G(L). Its terminal
derived subgroup lies in L; the rank-one Borel bound makes this literal
normalizer solvable.

The remaining second-parabolic argument must contradict that solvability
from the actual core action and marked left core. No nonsolvable normalizer
or ambient recognition is assumed. All preceding quotient and Sylow maps remain.
Source: Aschbacher–Smith 5.2.8, printed pp.652–653 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original remainder has its entire natural core, full common Sylow,
and a solvable left-core normalizer, with all earlier markings retained. -/
theorem rankOne_global_unitary_normalizer_or_whole_core
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (he : (Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (amalgam m hm).reverse)) ∨
      (Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm).reverse))) :
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∨
      ∃ (J : Subgroup G) (hKJ : residual H ≤ J),
        J ∈ Chapter1.LStar G (T : Subgroup G) ∧ residual H < J ∧
        ¬ J ≤ normalizer ((residual H).pCoreIn 2 : Set G) ∧
        ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2 ∧
        IsElementaryAbelian 2 (residual H ⊓ J.pCoreIn 2 : Subgroup G) ∧
        Nat.card (residual H ⊓ J.pCoreIn 2 : Subgroup G) = (2^m)^3 ∧
        Nat.card (J.pCoreIn 2) ≤ 2*(2^m)^3 ∧
        IsQuasisimple (J ⧸ pCore 2 J) ∧
        Global.UnitaryEmbedding.RemainingModels
          ((J ⧸ pCore 2 J) ⧸ center (J ⧸ pCore 2 J)) ∧
        ClassicalGroup.IsPSL
          ((J ⧸ pCore 2 J) ⧸ center (J ⧸ pCore 2 J)) 3 (2^m) ∧
        Chapter1.Section02.LocalModels.IsSL (J ⧸ pCore 2 J) 3 (2^m) ∧
        Nat.card (frattini (pCore 2 J)) ≤ 2 ∧
        (∃ hc : HasCharacteristicTwo J, Global.UnitaryCover.NaturalCoreSection hc m) ∧
        IsElementaryAbelian 2 (J.pCoreIn 2) ∧ frattini (pCore 2 J) = ⊥ ∧
        Nat.card (⁅J.pCoreIn 2,J⁆ : Subgroup G) = (2^m)^3 ∧
        ⁅J.pCoreIn 2,J⁆ = residual H ⊓ J.pCoreIn 2 ∧
        ⁅J.pCoreIn 2,residual H⁆ = residual H ⊓ J.pCoreIn 2 ∧
        (∃ hc : HasCharacteristicTwo J, Global.UnitarySplit.SplitCoreAction hc m) ∧
        J.pCoreIn 2 = residual H ⊓ J.pCoreIn 2 ∧
        J.pCoreIn 2 ≤ (residual H).pCoreIn 2 ∧
        Nat.card (J.pCoreIn 2) = (2^m)^3 ∧
        (∃ hc : HasCharacteristicTwo J, Global.UnitaryCover.NaturalCoreAction hc m) ∧
        (residual H).relIndex J = (2^m)^3-1 ∧
        (T : Subgroup G) ⊓ J = (T : Subgroup G) ⊓ L ∧
        L.pCoreIn 2 ≤ J ∧
        normalizer (L.pCoreIn 2 : Set G) = normalizer (L : Set G) ∧
        (let Y := J ⊓ normalizer (L.pCoreIn 2 : Set G)
         J.pCoreIn 2 ≤ Y ∧
           (∃ P : Sylow 2 Y, (P : Subgroup Y).map Y.subtype = (T : Subgroup G) ⊓ L) ∧
           (solvableResidual Y).map Y.subtype ≤ L) ∧
        Group.IsSolvable (J ⊓ normalizer (L.pCoreIn 2 : Set G) : Subgroup G) ∧
        ((Nonempty (RankTwoAmalgam.Iso
            (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (amalgam m hm)) ∨
          Nonempty (RankTwoAmalgam.Iso
            (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (amalgam m hm).reverse)) →
          Nat.card (J.pCoreIn 2) = (2^m)^3 ∧
          ∃ hc : HasCharacteristicTwo J, Global.UnitaryCover.NaturalCoreAction hc m) ∧
        (let f := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion hKJ)
         f.ker = (J.pCoreIn 2).subgroupOf (residual H) ∧
           (pCore 2 (residual H)).map f = f.range.pCoreIn 2 ∧
           IsElementaryAbelian 2 (pCore 2 f.range) ∧
           Nat.card (pCore 2 f.range) = (2^m)^2 ∧
           ClassicalGroup.IsPSL (f.range ⧸ pCore 2 f.range) 2 (2^m) ∧
           (m = 2 → ¬ (Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M22) ∨
             Chapter1.Section02.LocalModels.IsM22Cover (J ⧸ pCore 2 J) ∨
             Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M23))) ∧
           ChapterC.IsL2EvenBlock f.range m ∧
           pCore 2 f.range = ChapterC.blockU f.range ∧ center f.range = ⊥ ∧
           IsSQTK KnownSimple.IsKnownSimple (J ⧸ pCore 2 J) ∧
           (⊤ : Subgroup (J ⧸ pCore 2 J)).IsCComponent ∧ f.range ≠ ⊤ ∧
           ∃ S : Sylow 2 J, (S : Subgroup J) = (T : Subgroup G).subgroupOf J ∧
             (let Sb := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
              f.range ∈ ChapterA.Section03.localCComponents Sb ∧
                (Sb : Subgroup (J ⧸ pCore 2 J)) ≤ normalizer (f.range : Set _))) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  rcases D.rankOne_global_unitary_normalizer_or_moved_core h hmany hn hpsl
      hH d hp m hm he with hlocal |
      ⟨J,hKJ,hJ,hlt,hnorm,hnot,hN,hNc,hRc,hq,hmodels,hlinear,hfull,hphi,hact,
        helem,hphiz,hcard,hJmove,hKmove,hsplit,hord,hf⟩
  · exact .inl hlocal
  · have heq := d.unitary_overcomponent_core_eq_intersection hi hH hp m hm he hJ.1 hlt hnot
    obtain ⟨hle,hwhole,hwholeact⟩ :=
      d.unitary_overcomponent_whole_natural_core hi hH hp m hm he hJ.1 hlt hnot
    have hindex := d.unitary_overcomponent_index hi hH hp m hm he hJ.1 hlt hnot
    have hsylow := d.unitary_overcomponent_full_common_sylow hi hH hp m hm he hJ.1 hlt hnot
    obtain ⟨hUJ,hNU,hNY⟩ :=
      d.unitary_overcomponent_left_core_normalizer hi hH hp m hm he hJ.1 hlt hnot
    have hsol := d.unitary_overcomponent_left_core_normalizer_solvable
      hi hH hp m hm he hJ.1 hlt hnot
    exact .inr ⟨J,hKJ,hJ,hlt,hnorm,hnot,hN,hNc,hRc,hq,hmodels,hlinear,hfull,hphi,hact,
      helem,hphiz,hcard,hJmove,hKmove,hsplit,heq,hle,hwhole,hwholeact,hindex,hsylow,
      hUJ,hNU,hNY,hsol,hord,hf⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
