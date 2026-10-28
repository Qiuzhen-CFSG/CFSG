module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.AlternatingSixSource
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.NormalFourSize

/-!
# Terminal component supports and one suitable involution

The complete A₆ support construction feeds the literal source exclusion.
Together with the established paired-component exclusions and the mixed-size
catalogue, every terminal component is the unique normal binary L₃(2)
residual. Its existing full natural/dual support construction gives the
original W, S and one involution satisfying all U₀--U₃.

Only the independent MixedSizeInput and original14.6.18 remain explicit.
Their final instantiation belongs to qt-e-suitable-existence and
qt-e-14625-source respectively. No local support, marking, geometry, action
or vector input remains. Final14.6.24(2--4) assembly belongs to
qt-e-suitable-component-marking; suitable choice to qt-e-suitable-existence.

Source: Aschbacher--Smith14.6.20--24, printed pp.1037--1041.
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

/-- All original terminal components are binary linear-three. Only the
independent mixed-size theorem and original14.6.18 remain explicit. -/
theorem terminal_component_linear_three_of_mixed_size
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent) :
    Nonempty ((K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) ∧
      ComponentModelDiagram T K ∧ (K.subgroupOf Mc).Normal ∧
      (solvableResidual Mc).map Mc.subtype = K ∧
      K ⊔ (T : Subgroup G) = Mc ∧
      (∀ C : Subgroup G, C ≤ Mc → (C.subgroupOf Mc).IsCComponent → C = K) ∧
      solvableResidual Mc = pResidual 2 Mc := by
  obtain ⟨hm,hd,hn,hr,hgen,huniq,hres⟩ := terminal_component_catalogue_of_mixed_size
    hG T hempty hM hunique hmany hcard e hab hsolv size K hKM hK
  change Nonempty ((K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) ∨
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) at hm
  rcases hm with hm | ha
  · exact ⟨hm,hd,hn,hr,hgen,huniq,hres⟩
  · exact (source_normal_a6_false hG T hempty hM hunique hmany hcard e hab hsolv
      K hKM hK hr (Classical.choice ha)).elim

/-- Construct the original component, both full natural supports, their
literal stabilizer and one suitable involution. Every support, action,
normalizer and same-vector premise is discharged from the original source
hypotheses; mixed-size and14.6.18 retain their independent source owners. -/
theorem terminal_exists_full_supports_suitable_of_mixed_size
    (size : Chapter10.MixedZeroCore.MixedSizeInput G) :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    ∃ K : Subgroup G, K ≤ Mc ∧ (K.subgroupOf Mc).IsCComponent ∧
      ComponentModelDiagram T K ∧ (K.subgroupOf Mc).Normal ∧
      (solvableResidual Mc).map Mc.subtype = K ∧
      K ⊔ (T : Subgroup G) = Mc ∧
      (∀ C : Subgroup G, C ≤ Mc → (C.subgroupOf Mc).IsCComponent → C = K) ∧
      solvableResidual Mc = pResidual 2 Mc ∧
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
        Mc ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) ∧
        Geometry T Mc (conjugateSpanBy (localModule T M) Mc) K A
          ((T : Subgroup G) ⊓ normalizer (A : Set G)) ∧
        ∃ u ∈ A, u ^ 2 = 1 ∧ u ≠ 1 ∧
          suitableQuotientCentralizer h u = (T : Subgroup G) ⊓ normalizer (A : Set G) ∧
          (∀ s ∈ (T : Subgroup G) ⊓ normalizer (A : Set G), ⁅u,s⁆ ∈ centralInvolutions T) ∧
          (∃ k ∈ K, ⁅u,k⁆ ∉ centralInvolutions T) ∧ Suitable h Mc u := by
  obtain ⟨_,K,hKM,hK,_⟩ := terminal_exists_component
    hG T hempty hM hunique hmany hcard e hab hsolv
  obtain ⟨⟨eK⟩,hd,hn,hr,hgen,huniq,hres⟩ := terminal_component_linear_three_of_mixed_size
    hG T hempty hM hunique hmany hcard e hab hsolv size K hKM hK
  exact ⟨K,hKM,hK,hd,hn,hr,hgen,huniq,hres,terminal_single_l3_full_supports_suitable
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hr eK⟩
end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
