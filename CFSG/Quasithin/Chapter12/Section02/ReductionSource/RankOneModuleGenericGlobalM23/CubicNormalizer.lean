module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalM23.Semilinear
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.CubicNormalizerConjugacy
/-!
# Source cubic-normalizer recognition at the literal Chapter 12 consumer

Specialize the original prepared nonmaximal linear comparison with the
whole reduced module. The source cubic-centralizer quotient has elementary
four-group involution centralizers. The actual scalar cubic, selected as
Sylow in the original quotient centralizer preimage, has full ambient
normalizer equal to its normalizer in M. The original quotient map marks
this local complement as ΓL₂(4).

Source: Aschbacher–Smith 5.2.15, printed pp.654–655. Compatible linear
completion and ambient M₂₃ recognition remain separate obligations.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open Representation.SL2FourNatural.SemilinearNormalizer
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual cubic-centralizer quotient has one involution class and E₄ centralizers. -/
theorem rankOne_global_linear_nonmaximal_cubic_quotient_centralizers
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (E : Type) [Field E] [Finite E] [CharP E 2]
    {m : ℕ} (hm : 0 < m) (hE : Nat.card E = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    (c : G) (hc : orderOf c = 3) :
    (∀ a b : QuasithinM23.cubicCentralizerQuotient c,
      orderOf a = 2 → orderOf b = 2 → IsConj a b) ∧
    (∀ t : QuasithinM23.cubicCentralizerQuotient c, orderOf t = 2 →
      Nat.card (centralizer ({t} : Set (QuasithinM23.cubicCentralizerQuotient c))) = 4 ∧
        IsElementaryAbelian 2 (centralizer ({t} : Set (QuasithinM23.cubicCentralizerQuotient c)))) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.linear_nonmaximal_cubic_quotient_centralizers hi hH hp E hm hE he hnonmax c hc

/-- The full ambient normalizer of the original scalar cubic is the marked local ΓL₂(4). -/
theorem rankOne_global_linear_nonmaximal_scalar_cubic_ambient_normalizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (E : Type) [Field E] [Finite E] [CharP E 2]
    {m : ℕ} (hm : 0 < m) (hE : Nat.card E = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    let M := normalizer (L : Set G)
    let π := QuotientGroup.mk' (pCore 2 M)
    let Lbar := (L.subgroupOf M).map π
    ∃ e : (M ⧸ pCore 2 M) ≃* Gamma,
      (L.subgroupOf M).map (e.toMonoidHom.comp π) = special.range ∧
      ∃ C : Subgroup M, C.map (e.toMonoidHom.comp π) = scalar.range ∧ Nat.card C = 3 ∧
        (∃ P : Sylow 3 ((centralizer (Lbar : Set (M ⧸ pCore 2 M))).comap π),
          (P : Subgroup ((centralizer (Lbar : Set (M ⧸ pCore 2 M))).comap π)).map
            ((centralizer (Lbar : Set (M ⧸ pCore 2 M))).comap π).subtype = C) ∧
        (pCore 2 M).IsComplement' (Subgroup.normalizer (C : Set M)) ∧
        (∃ eN : Subgroup.normalizer (C : Set M) ≃* Gamma,
          ∀ x : Subgroup.normalizer (C : Set M), eN x = e (π x)) ∧
        Subgroup.normalizer (C.map M.subtype : Set G) =
          (Subgroup.normalizer (C : Set M)).map M.subtype ∧
        Nonempty (Subgroup.normalizer (C.map M.subtype : Set G) ≃* Gamma) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.linear_nonmaximal_scalar_cubic_ambient_normalizer hi hH hp E hm hE he hnonmax


/-- Source 5.2.15 for any Sylow cubic in the prescribed original preimage. -/
theorem rankOne_global_linear_nonmaximal_cubic_normalizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (E : Type) [Field E] [Finite E] [CharP E 2]
    {m : ℕ} (hm : 0 < m) (hE : Nat.card E = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    (P : Sylow 3 ((centralizer (((L.subgroupOf (normalizer (L : Set G))).map
      (QuotientGroup.mk' (pCore 2 (normalizer (L : Set G))))) :
        Set ((normalizer (L : Set G)) ⧸ pCore 2 (normalizer (L : Set G))))).comap
          (QuotientGroup.mk' (pCore 2 (normalizer (L : Set G)))))) :
    let M := normalizer (L : Set G)
    let π := QuotientGroup.mk' (pCore 2 M)
    let D := (centralizer ((L.subgroupOf M).map π : Set (M ⧸ pCore 2 M))).comap π
    let C := (P : Subgroup D).map D.subtype
    Subgroup.normalizer (C.map M.subtype : Set G) =
      (Subgroup.normalizer (C : Set M)).map M.subtype ∧
      Nonempty (Subgroup.normalizer (C.map M.subtype : Set G) ≃* Gamma) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.linear_nonmaximal_cubic_normalizer hi hH hp E hm hE he hnonmax P

/-- The actual cubic normalizer needed in the source linear-completion argument. -/
theorem rankOne_global_linear_nonmaximal_cubic_normalizer_of_mem_left
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (E : Type) [Field E] [Finite E] [CharP E 2]
    {m : ℕ} (hm : 0 < m) (hE : Nat.card E = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    (c : G) (hc : orderOf c = 3) (hcM : c ∈ normalizer (L : Set G)) :
    Nonempty (Subgroup.normalizer (zpowers c : Set G) ≃* Gamma) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.linear_nonmaximal_cubic_normalizer_of_mem_left hi hH hp E hm hE he hnonmax c hc hcM

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
