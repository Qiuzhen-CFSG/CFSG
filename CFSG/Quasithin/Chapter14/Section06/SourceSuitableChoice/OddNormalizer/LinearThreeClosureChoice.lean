module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Normalizer.Parabolic.LinearThree
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice

/-!
# Suitable involutions from the cubic exchanged closure

The PSL₃(2) exchanged component now supplies the literal parabolic core
normalizer, weak closure, and N_Mc(N_T(H₁)) = T. The established Fitting
containment and exchanged support geometry therefore construct a suitable
involution in the original first support. Both movement conditions use
conjugation by t⁻¹, and the original ambient Sylow conclusions are retained.

The second theorem also applies the source model sieve and the previously
completed PSL₂(4) row, closing every cubic exchanged component without an
extra model, normalizer, support or fixed-vector premise. The invariant
higher-linear and quintic closure branches remain with this theorem-family
owner. Earlier primitive and exchanged-factor inputs retain their existing
producers, and qt-e-suitable-existence owns final suitable-choice assembly.

Source: Aschbacher--Smith 14.6.14(3), 14.6.16--17, pp.1033,1035--1036.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter1
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))


include hG hempty hM hunique hmany hcard e hab hH

/-- The original PSL₃(2) component supplies a suitable involution in U_H,1.
All support, Fitting, fixed-vector and normalizer premises are discharged. -/
theorem source_exists_suitable_linear_three_component
    (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H 3)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (L : Subgroup G) (hL : L ≤ Mc) (hcomp : (L.subgroupOf Mc).IsCComponent)
    (hq : IsQuasisimple (XiQuotient L))
    (hm : StrictExchangedModel (T : Subgroup G) Mc (residualClosure H Mc) L 3)
    (hlayer : StrictClosureLayer Mc (residualClosure H Mc))
    (hb : ClassicalGroup.IsPSL ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 3 2) :
    let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    ∃ u ∈ firstSupport a H1, u ^ 2 = 1 ∧ u ≠ 1 ∧
      suitableQuotientCentralizer h u = S ∧
      ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G) ∧
      (∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer h u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G)) ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
        (H ⊓ centralizer ({u} : Set G)) ∧
      normalizer (((T : Subgroup G) ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G) = S ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
        (centralizer ({u} : Set G)) ∧
      ¬∃ S' : Sylow 2 G, (S' : Subgroup G) ≤ centralizer ({u} : Set G) := by
  obtain ⟨hWU,hZW,hKW,hSW,hi,hsep,hff⟩ := source_exchanged_support_premises
    hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 d
  have hK := source_residual_le_fittingPreimage
    hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 hprim d
  have hn := (source_normalizer_linear_three_component
    hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d L hL hcomp hq hm hlayer hb).2
  exact source_exists_suitable_of_fixed_free_support
    hG T hempty hM hunique hmany hcard e hab H hH (residual H) (firstSupport a H1)
      ((T : Subgroup G) ⊓ normalizer (H1 : Set G)) hK hWU hZW hKW hSW inf_le_left hi hn hsep hff

/-- The actual suitable-involution application for every cubic exchanged
component, with the model selected from the maximal-prime source setup. -/
theorem source_exists_suitable_cubic_exchanged_component
    (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H 3)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M 3)
    (L : Subgroup G) (hL : L ≤ Mc) (hcomp : (L.subgroupOf Mc).IsCComponent)
    (hq : IsQuasisimple (XiQuotient L))
    (hm : StrictExchangedModel (T : Subgroup G) Mc (residualClosure H Mc) L 3)
    (hlayer : StrictClosureLayer Mc (residualClosure H Mc)) :
    let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    ∃ u ∈ firstSupport a H1, u ^ 2 = 1 ∧ u ≠ 1 ∧
      suitableQuotientCentralizer h u = S ∧
      ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G) ∧
      (∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer h u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G)) ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
        (H ⊓ centralizer ({u} : Set G)) ∧
      normalizer (((T : Subgroup G) ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G) = S ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
        (centralizer ({u} : Set G)) ∧
      ¬∃ S' : Sylow 2 G, (S' : Subgroup G) ≤ centralizer ({u} : Set G) := by
  obtain ⟨hWU,hZW,hKW,hSW,hi,hsep,hff⟩ := source_exchanged_support_premises
    hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 d
  have hK := source_residual_le_fittingPreimage
    hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 hprim d
  have hn := (source_normalizer_cubic_exchanged_component
    hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d hmax L hL hcomp hq hm hlayer).2
  exact source_exists_suitable_of_fixed_free_support
    hG T hempty hM hunique hmany hcard e hab H hH (residual H) (firstSupport a H1)
      ((T : Subgroup G) ⊓ normalizer (H1 : Set G)) hK hWU hZW hKW hSW inf_le_left hi hn hsep hff


end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
