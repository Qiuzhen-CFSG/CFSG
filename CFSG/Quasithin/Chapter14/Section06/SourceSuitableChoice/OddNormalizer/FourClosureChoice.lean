module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Normalizer.Parabolic.Four
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice

/-!
# Suitable involutions in the symmetric-five wreath branch

The literal Mc/O₂(Mc) model gives the original core normalizer and weak
closure, hence N_Mc(N_T(H₁)) = T. Combining this with the established
Fitting containment and exchanged support geometry constructs the actual
suitable involution in U_H,1, preserving inverse conjugation by t⁻¹.

The second theorem supplies the full wreath isomorphism from the actual
PSL₂(4) component row; no normalizer, suitability, or full-action premise
is left in that application. The model and layer comparison are already
produced by StrictSource and FourSource. The other strict-closure rows and
final 14.6.14--16 assembly remain with qt-e-suitable-odd-normalizer; the
primitive and original exchanged-factor inputs retain qt-e-quintic-recognition
and qt-e-14612-singleton. Final suitable-choice assembly belongs to
qt-e-suitable-existence.

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

/-- The actual support construction in the literal S₅ wreath branch.
Every Fitting, support, fixed-vector and normalizer premise is discharged. -/
theorem source_exists_suitable_four_closure_case
    (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H 3)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (eW : (Mc ⧸ pCore 2 Mc) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))) :
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
  have hn := (source_normalizer_four_closure_case
    hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d eW).2
  exact source_exists_suitable_of_fixed_free_support
    hG T hempty hM hunique hmany hcard e hab H hH (residual H) (firstSupport a H1)
      ((T : Subgroup G) ⊓ normalizer (H1 : Set G)) hK hWU hZW hKW hSW inf_le_left hi hn hsep hff

/-- The PSL₂(4) component row now supplies the actual suitable involution.
The full wreath action is proved by the original exchanged-factor order. -/
theorem source_exists_suitable_four_component
    (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H 3)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (L : Subgroup G) (hL : L ≤ Mc) (hcomp : (L.subgroupOf Mc).IsCComponent)
    (hq : IsQuasisimple (XiQuotient L))
    (hm : StrictExchangedModel (T : Subgroup G) Mc (residualClosure H Mc) L 3)
    (hlayer : StrictClosureLayer Mc (residualClosure H Mc))
    (hb : ClassicalGroup.IsPSL ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 2 4) :
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
  obtain ⟨⟨eW⟩,_⟩ := source_four_closure_alternative
    hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d
    L hL hcomp hq hm hlayer hb
  exact source_exists_suitable_four_closure_case
    hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d eW

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
