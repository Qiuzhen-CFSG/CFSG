module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.SourceMarking
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.SourceDiagram
public import Theory.Representation.BinaryConjugationSection.Join

/-!
# Excluding both component-pair alternatives from the original supports

Join each actual natural section with its dual over the same central
kernel. The original component quotient and parabolic exchange supply the
outer actors. SourceMarking then constructs the common U/Z action, both
component embeddings, the simultaneous automorphism marking, support
stabilizers, whole-group permutation and fixed supplement. Applying the
checked critical-endpoint and Sylow argument excludes both exchanged and
normal component pairs.

Only the genuine 14.6.20--23 component models and full natural/dual support
identities, separation and cross-centralization remain explicit. They belong
to qt-e-suitable-component-supports; natural constituents on subquotients do
not supply these hypotheses. Original 14.6.18 remains with qt-e-14625-source.
The original 14.6.24 assembly remains with qt-e-suitable-component-marking,
and final suitable choice with qt-e-suitable-existence. This theorem does
not claim unconditional completion of 14.6.24.

Source: Aschbacher--Smith 14.6.21--24, printed pp.1038--1041.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryLinearThree.NaturalDual
variable {G : Type*} [Group G] [Finite G]

/-- The four original natural/dual supports exclude both terminal component-pair
alternatives, with every marking and outer-actor premise discharged. -/
theorem source_no_paired_components_of_natural_sections
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (K Kplus : Subgroup G) (hKM : K ≤ Mc) (hKplusM : Kplus ≤ Mc)
    (hK : (K.subgroupOf Mc).IsCComponent) (hKplus : (Kplus.subgroupOf Mc).IsCComponent)
    (hall : ∀ J : Subgroup Mc, J.IsCComponent → J = K.subgroupOf Mc ∨ J = Kplus.subgroupOf Mc)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (eKplus : (Kplus ⧸ pCore 2 Kplus) ≃* BinaryLinearThree.Group)
    (A B Aplus Bplus : Subgroup G)
    (d : BinaryConjugationSection K A (centralInvolutions T)
      (BinaryLinearThree.W.comp (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))))
    (ddual : BinaryConjugationSection K B (centralInvolutions T)
      (BinaryLinearThree.W.dual.comp (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))))
    (dplus : BinaryConjugationSection Kplus Aplus (centralInvolutions T)
      (BinaryLinearThree.W.comp (eKplus.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Kplus)))))
    (dplusDual : BinaryConjugationSection Kplus Bplus (centralInvolutions T)
      (BinaryLinearThree.W.dual.comp (eKplus.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Kplus)))))
    (hsupport : ⁅conjugateSpanBy (localModule T M) Mc,K⁆ = A ⊔ B)
    (hsupportPlus : ⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆ = Aplus ⊔ Bplus)
    (hAB : A ⊓ B ≤ centralInvolutions T)
    (hABplus : Aplus ⊓ Bplus ≤ centralInvolutions T)
    (hcross : ⁅⁅conjugateSpanBy (localModule T M) Mc,K⁆,Kplus⁆ = ⊥)
    (hcrossRev : ⁅⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆,K⁆ = ⊥)
    (hsep : ⁅conjugateSpanBy (localModule T M) Mc,K⁆ ⊓
      ⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆ ≤ centralInvolutions T) : False := by
  let U := conjugateSpanBy (localModule T M) Mc
  have hSU : ⁅U,K⁆ ≤ U :=
    le_normalizer_iff_commutator_le_left.mp (hKM.trans (le_normalizer_conjugateSpanBy _ _))
  have hS'U : ⁅U,Kplus⁆ ≤ U :=
    le_normalizer_iff_commutator_le_left.mp (hKplusM.trans (le_normalizer_conjugateSpanBy _ _))
  have hAU : A ≤ U := le_sup_left.trans (hsupport.symm.le.trans hSU)
  have hBU : B ≤ U := le_sup_right.trans (hsupport.symm.le.trans hSU)
  have hAplusU : Aplus ≤ U := le_sup_left.trans (hsupportPlus.symm.le.trans hS'U)
  have hBplusU : Bplus ≤ U := le_sup_right.trans (hsupportPlus.symm.le.trans hS'U)
  obtain ⟨c,_,_,_⟩ := d.exists_join_section ddual
    (hAU.trans ((le_centralizer_iff_isMulCommutative.mpr hab).trans (centralizer_le hBU))) hAB
  obtain ⟨cplus,_,_,_⟩ := dplus.exists_join_section dplusDual
    (hAplusU.trans ((le_centralizer_iff_isMulCommutative.mpr hab).trans (centralizer_le hBplusU))) hABplus
  have cK : BinaryConjugationSection K ⁅U,K⁆ (centralInvolutions T)
      (action.comp (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))) := by
    rw [hsupport]
    exact c
  have cKplus : BinaryConjugationSection Kplus ⁅U,Kplus⁆ (centralInvolutions T)
      (action.comp (eKplus.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Kplus)))) := by
    rw [hsupportPlus]
    exact cplus
  obtain ⟨s,hs⟩ := source_component_outer_actor
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK eK
  obtain ⟨t,ht⟩ := source_component_outer_actor
    hG T hempty hM hunique hmany hcard e hab hsolv Kplus hKplusM hKplus eKplus
  exact source_no_paired_components_of_original_sections
    hG T hempty hM hunique hmany hcard e hab hsolv K Kplus hKM hKplusM hK hKplus hall
    eK eKplus cK cKplus hcross hcrossRev hsep s hs t ht
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
