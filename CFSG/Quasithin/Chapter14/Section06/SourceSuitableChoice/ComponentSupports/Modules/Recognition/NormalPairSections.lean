module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.NormalSeeds
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.NormalPairs

/-!
# The distinct normal-pair contradiction from natural constituent types

NormalSeeds constructs both original natural/dual seed pairs and their full
ambient orbit spans. The natural-type hypothesis on every original irreducible
section then supplies cross-centralization through the existing nonsplit
extension argument. Hence each seed pair is invariant under all of Mc and is
the full component support.

The actual residual product exhausts the component family: a third component
would centralize the entire residual, and therefore itself, in the radical-free
quotient. The four marked sections, both full supports, both within-pair
intersections and their cross-centralizations and separation feed the literal
TwoComponents.SourceSections contradiction.

This is conditional on natural types on U_Mc/Z. Their remaining transport from
the constructed seed spans belongs to qt-e-suitable-component-supports, together
with the normal PSL2(4), A6 and final catalogue branches. No seed, exhaustion,
component-count or full-support premise remains. Original14.6.18 is hsolv;
final14.6.24 assembly remains with qt-e-suitable-existence.
Source: Aschbacher--Smith14.6.21(3)--24, printed pp.1038--1041.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement Pointwise
open Representation.BinaryOffender.Homogeneous Representation.OneCohomology
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Subgroup.NormalSylowQuotientAction
open Chapter13.Section08.CriticalGeometry.Reorientation
variable {G : Type*} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv


/-- All natural seed and exhaustion premises of the normal-pair consumer
are constructed. Only recognition on the original irreducible sections remains. -/
theorem terminal_normal_pair_sections_of_natural_types
    (K C : Subgroup G) (hKM : K ≤ Mc) (hCM : C ≤ Mc)
    (hK : (K.subgroupOf Mc).IsCComponent) (hC : (C.subgroupOf Mc).IsCComponent)
    (hne : K ≠ C) (hnK : (K.subgroupOf Mc).Normal) (hnC : (C.subgroupOf Mc).Normal)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (eC : (C ⧸ pCore 2 C) ≃* BinaryLinearThree.Group)
    (hr : ((solvableResidual Mc).map Mc.subtype : Set G) = (K : Set G) * (C : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc)]
    (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
    (htypes : ∀ (S : Subrepresentation a.representation) (L : Subrepresentation S.toRepresentation),
      IsIrreducible L.quotientRepresentation →
      ChapterD.NaturalLinearThreeTypes L.quotientRepresentation (actorImage Mc K) ∧
      ChapterD.NaturalLinearThreeTypes L.quotientRepresentation (actorImage Mc C)) :
    ∃ (j : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (A B : Subgroup G),
      Nonempty (BinaryConjugationSection K A (centralInvolutions T)
        (BinaryLinearThree.W.comp (j.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) ∧
      Nonempty (BinaryConjugationSection K B (centralInvolutions T)
        (BinaryLinearThree.W.dual.comp (j.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) ∧
      ⁅conjugateSpanBy (localModule T M) Mc,K⁆ = A ⊔ B ∧
      A ⊓ B = centralInvolutions T ∧
      (∃ s : T, B = A.map (MulAut.conj (s:G)⁻¹).toMonoidHom) ∧
      conjugateSpanBy A (T : Subgroup G) = A ⊔ B ∧
      (normalizer (A : Set G)).relIndex (T : Subgroup G) = 2 ∧
      Mc ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  obtain ⟨j,A,B,⟨d⟩,⟨ddual⟩,hA,hB,hAB,hconj,hspan,hindex,_,hexhaust⟩ :=
    terminal_normal_l3_natural_sections_span
      hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hnK eK
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (terminal_outside hG T hempty hM hunique hmany hcard e).1.2.trans
      ((normal_subgroupOf_iff_le_normalizer hKM).mp hnK)
  have hspanK : conjugateSpanBy K (T : Subgroup G) = K :=
    le_antisymm (conjugateSpanBy_le le_rfl hTK) (le_conjugateSpanBy _ _)
  obtain ⟨hWM,hfull⟩ := terminal_normal_pair_full_support_of_natural_types
    hG T hempty hM hunique hmany hcard e hab hsolv
    K C hKM hCM hK hC hne hnK hnC j eC hr a htypes
    A B d ddual hA hB hAB.le (by rwa [hspanK]) hspan
  exact ⟨j,A,B,⟨d⟩,⟨ddual⟩,hfull,hAB,hconj,hspan,hindex,hWM⟩

private theorem source_components_exhausted_by_residual_pair
    (K C : Subgroup G) (hKM : K ≤ Mc) (hCM : C ≤ Mc)
    (hK : (K.subgroupOf Mc).IsCComponent) (hC : (C.subgroupOf Mc).IsCComponent)
    (hr : (solvableResidual Mc).map Mc.subtype = K ⊔ C) :
    ∀ J : Subgroup Mc, J.IsCComponent → J = K.subgroupOf Mc ∨ J = C.subgroupOf Mc := by
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let : Group.IsNilpotent (pCore 2 Mc) := pCore_isPGroup.isNilpotent
  have hR : solvableRadical (Mc ⧸ pCore 2 Mc) = ⊥ := by
    have hh := map_solvableRadical_equiv (QuotientGroup.quotientMulEquivOfEq
      (source_radical_eq_core hG T hempty hM hunique hmany hcard e hab hsolv Mc
        (terminal_outside hG T hempty hM hunique hmany hcard e)))
    rw [solvableRadical_quotient_solvableRadical,Subgroup.map_bot] at hh
    exact hh.symm
  have hr' : solvableResidual Mc = K.subgroupOf Mc ⊔ C.subgroupOf Mc := by
    apply map_injective Mc.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hKM,map_subgroupOf_eq_of_le hCM,hr]
  have hRq : solvableResidual (Mc ⧸ pCore 2 Mc) = actorImage Mc K ⊔ actorImage Mc C := by
    rw [←map_solvableResidual_eq q (QuotientGroup.mk'_surjective _),hr',Subgroup.map_sup]
    rfl
  intro J hJ
  by_cases hjK : J = K.subgroupOf Mc
  · exact Or.inl hjK
  by_cases hjC : J = C.subgroupOf Mc
  · exact Or.inr hjC
  have hJq := hJ.map_quotient (pCore 2 Mc)
  have hKq := hK.map_quotient (pCore 2 Mc)
  have hCq := hC.map_quotient (pCore 2 Mc)
  have hnK : J.map q ≠ actorImage Mc K := fun he => hjK (hJ.eq_of_map_quotient_eq hK _ he)
  have hnC : J.map q ≠ actorImage Mc C := fun he => hjC (hJ.eq_of_map_quotient_eq hC _ he)
  have hKJ : actorImage Mc K ≤ centralizer (J.map q : Set (Mc ⧸ pCore 2 Mc)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (hJq.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hR hKq hnK))
  have hCJ : actorImage Mc C ≤ centralizer (J.map q : Set (Mc ⧸ pCore 2 Mc)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (hJq.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hR hCq hnC))
  let : Group.IsPerfect (J.map q) := hJq.perfect
  have hle : J.map q ≤ actorImage Mc K ⊔ actorImage Mc C :=
    (le_solvableResidual_of_isPerfect (J.map q)).trans_eq hRq
  have hc : ⁅J.map q,J.map q⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hle.trans (sup_le hKJ hCJ))
  exact (hJq.ne_bot (disjoint_self.mp
    (hJq.disjoint_of_commutator_eq_bot_of_solvableRadical_eq_bot hR hc))).elim

/-- The original distinct normal pair is impossible once its original
irreducible sections have natural types. This constructs all four marked
sections, both full supports, both central intersections, both cross-actions
and the separation consumed by the literal paired-component theorem. -/
theorem terminal_normal_pair_impossible_of_natural_types
    (K C : Subgroup G) (hKM : K ≤ Mc) (hCM : C ≤ Mc)
    (hK : (K.subgroupOf Mc).IsCComponent) (hC : (C.subgroupOf Mc).IsCComponent)
    (hne : K ≠ C) (hnK : (K.subgroupOf Mc).Normal) (hnC : (C.subgroupOf Mc).Normal)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (eC : (C ⧸ pCore 2 C) ≃* BinaryLinearThree.Group)
    (hr : ((solvableResidual Mc).map Mc.subtype : Set G) = (K : Set G) * (C : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc)]
    (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
    (htypes : ∀ (S : Subrepresentation a.representation) (L : Subrepresentation S.toRepresentation),
      IsIrreducible L.quotientRepresentation →
      ChapterD.NaturalLinearThreeTypes L.quotientRepresentation (actorImage Mc K) ∧
      ChapterD.NaturalLinearThreeTypes L.quotientRepresentation (actorImage Mc C)) : False := by
  obtain ⟨j,A,B,⟨d⟩,⟨ddual⟩,hfull,hAB,_⟩ := terminal_normal_pair_sections_of_natural_types
    hG T hempty hM hunique hmany hcard e hab hsolv K C hKM hCM hK hC hne hnK hnC eK eC hr a htypes
  have hr' := (terminal_normal_pair_residual_coordinates
    hG T hempty hM hunique hmany hcard e hab hsolv K C hKM hCM hK hC hne hnK eK eC hr).1
  have hrRev : ((solvableResidual Mc).map Mc.subtype : Set G) = (C : Set G) * (K : Set G) := by
    rw [hr',sup_comm]
    exact coe_mul_of_right_le_normalizer_left C K
      (hKM.trans ((normal_subgroupOf_iff_le_normalizer hCM).mp hnC))
  obtain ⟨jC,Aplus,Bplus,⟨dplus⟩,⟨dplusDual⟩,hfullPlus,hABplus,_⟩ :=
    terminal_normal_pair_sections_of_natural_types
      hG T hempty hM hunique hmany hcard e hab hsolv C K hCM hKM hC hK hne.symm hnC hnK
      eC eK hrRev a (fun S L hi => (htypes S L hi).symm)
  have hall := source_components_exhausted_by_residual_pair
    hG T hempty hM hunique hmany hcard e hab hsolv K C hKM hCM hK hC hr'
  exact source_no_paired_components_of_full_supports
    hG T hempty hM hunique hmany hcard e hab hsolv K C hKM hCM hK hC hne hall
    j jC A B Aplus Bplus d ddual dplus dplusDual hfull hfullPlus hAB.le hABplus.le


end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
