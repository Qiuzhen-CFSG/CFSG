module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.CrossSupports
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.SourceSections

/-!
# The paired-component consumer needs only full natural supports

Join the literal natural and dual sections over the same central subgroup.
The full-support identities make the other component normalize each joined
support. The original action quotient and perfect lifting then prove both
cross-centralizations and separation. The existing source critical-pair
consumer discharges the marking geometry and gives the contradiction.

The original component catalogue, four actual section markings and the two
full-support equalities remain explicit. Constituent seed spans do not supply
the equalities. Their construction and the normal PSL2(4) exclusion remain
with qt-e-suitable-component-supports; original14.6.18 remains hsolv, for
qt-e-14625-source. No unconditional completion of14.6.22--24 is claimed.

Source: Aschbacher--Smith14.6.22(2)--24, printed pp.1038--1041.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryLinearThree.NaturalDual
variable {G : Type*} [Group G] [Finite G]

/-- The literal waiting consumer, with cross-centralization and support
separation derived from the full natural/dual support identities. -/
theorem source_no_paired_components_of_full_supports
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
    (hne : K ≠ Kplus)
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
    : False := by
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
  obtain ⟨hcross,hcrossRev,hsep⟩ := source_pair_geometry_of_natural_dual_supports
    hG T hempty hM hunique hmany hcard e hab hsolv Mc
    (terminal_outside hG T hempty hM hunique hmany hcard e)
    K Kplus hKM hKplusM hK hKplus hne eK eKplus cK cKplus
  exact ComponentCriticalPair.TwoComponents.source_no_paired_components_of_natural_sections
    hG T hempty hM hunique hmany hcard e hab hsolv K Kplus hKM hKplusM hK hKplus hall
    eK eKplus A B Aplus Bplus d ddual dplus dplusDual hsupport hsupportPlus hAB hABplus
    hcross hcrossRev hsep.le

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
