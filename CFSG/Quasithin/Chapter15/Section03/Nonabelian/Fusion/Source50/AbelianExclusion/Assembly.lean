module
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.Complete
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion.Models
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion.Sieve
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion.Action
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion.Kernel
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion.Collapse
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Initial
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The abelian-U exclusion in the original source case

Assume U is abelian. The preceding 15.3.51 conclusions give an elementary
U and the common displacement line ZS/Z. A nonidentity Sylow-central
element of V-star then satisfies every literal G.6.1 hypothesis. The
proved G.6.4 and the prime-to-three normalizer restriction force U/Z to
have dimension two. Its marked fixed line yields C_U(V)≤ZS≤V, and
Y=[Y,U] collapses O₂(Y) into V, contradicting original 15.3.9.

The explicit inputs are earlier source facts: F.9 from 15.3.48, ordinary
and normalizer-three-prime conclusions from 15.3.49, and 15.3.51. The
original-source consumer discharges them without an added classification
or quotient-action premise.

Source: Aschbacher–Smith, Lemma 15.3.52, printed p.1145.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion
open Recognition Recognition.LocalRestrictions
open Chapter13.Section08.TransvectionRecognition
open Chapter13.Section08.TransvectionRecognition.Component
open Recognition.SplitBranch.G64Natural
variable {G : Type*} [Group G] [Finite G]

section Central
open ChapterG.Section06
open Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep
universe u
variable {A : Type u} [Group A] {E : Type u} [AddCommGroup E] [Module (ZMod 2) E]

private theorem central_alternative_of_source
    (ρ : Representation (ZMod 2) A E) (a : A)
    {Cover : Type u} [Group Cover] (q : Cover →* A)
    (h : Hypotheses KnownSimple.IsKnownSimple ρ a q)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (T : Sylow 2 A) (ha : a ∈ (center T).map (T : Subgroup A).subtype) :
    normalClosure ({a} : Set A) = ⊤ ∧ G64CentralAlternative ρ := by
  obtain ⟨hg, hm⟩ := (lemma_G_6_4 h hr).2 T ha
  exact ⟨hg, central_alternative_of_source_model ρ hm⟩

end Central

 theorem U_not_commutative_of_source51
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (h : (localSetup d (centralizerH d.Z)).Hypothesis)
    (ho : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V)
    (hVstar : Recognition.actorImage d.Z d.V ≠ ⊥)
    (h51 : IsMulCommutative (closureU d.Z d.ZS) →
      IsElementaryAbelian 2 (closureU d.Z d.ZS) ∧
        closureU d.Z d.ZS ≤ d.S ∧ d.ZS = d.V ⊓ closureU d.Z d.ZS)
    (hfull : d.Y = ⁅d.Y, closureU d.Z d.ZS⁆)
    (hthree : Nat.Coprime 3 (Nat.card (normalizer (d.ZS : Set G)))) :
    ¬ IsMulCommutative (closureU d.Z d.ZS) := by
  intro hc
  obtain ⟨hue, hUS, hintersection⟩ := h51 hc
  let := hue
  let : IsElementaryAbelian 2 d.V := h.elementary
  let := denominator_normal h.plus_le_H
  let : IsElementaryAbelian 2 (VectorQuotient d.Z d.ZS) := inferInstance
  have hkernel := source_kernel d.T d.Y d.V d.ZS d.Z h
  let ρ := actorRepresentation d.Z d.ZS hkernel
  let R : Sylow 2 (ActorQuotient d.Z) :=
    (d.T.subtype h.T_le_H).mapSurjective (QuotientGroup.mk'_surjective _)
  obtain ⟨t, htV, htne, htR⟩ := exists_central_mark d.Z d.V d.T
    h.T_le_H h.V_le_T h.T_normalizes_V hVstar
  have hcomm : ⁅d.V, closureU d.Z d.ZS⁆ ≤ d.ZS := by
    exact (module_commutator_bounds d (centralizerH d.Z) h).2.trans_eq hintersection.symm
  have hZ : Nat.card d.Z = 2 := h.point_card
  have hZS : Nat.card d.ZS = 4 := d.action.card_fixedPlane_planeStabilizer d.T d.sylow_le 1
  have he : LinearMap.range (ρ t - LinearMap.id) = vectorSubspace d.Z d.ZS d.ZS :=
    displacement_eq_line d.Z d.ZS hkernel d.V hcomm h.point_lt.le hZ hZS t htV htne
  have hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) = 1 := by
    rw [he]
    exact line_finrank d.Z d.ZS h.point_lt.le hZ hZS
  have htr := transvection_of_rank_one ρ t hr
  have hρ := actorRepresentation_injective d.Z d.ZS hkernel
  have hsource : ChapterG.Section06.Hypotheses KnownSimple.IsKnownSimple ρ t
      (QuotientGroup.mk' (pCore 2 (centralizerH d.Z))) := {
    finite_group := inferInstance
    finite_cover := inferInstance
    finite_displacement := inferInstance
    cover_sqtk := centralizer_sqtk hG d.Z hZ
    quotient_surjective := QuotientGroup.mk'_surjective _
    twoCore := pCore_quotient_pCore_eq_bot 2
    faithful := hρ
    involution := transvection_square hρ htr
    nonidentity := htne
    displacement_rank := by rw [hr]; decide
    generated := displacement_generates d.Z d.ZS hkernel t he }
  have hmodels := (central_alternative_of_source ρ t _ hsource hr R htR).2
  have hp : Nat.Coprime 3 (Nat.card (subspaceStabilizer ρ
      (LinearMap.range (ρ t - LinearMap.id)))) := by
    rw [he]
    exact line_stabilizer_three_prime d.Z d.ZS hkernel h.point_lt.le hthree
  have hd := finrank_eq_two_of_central_alternative ρ hρ t htr hp hmodels
  have hsmall : closureU d.Z d.ZS ⊓ centralizer (d.V : Set G) ≤ d.V :=
    (small_fixed_of_dimension_two d.Z d.ZS hkernel d.V h.point_lt.le h.plus_le
      inferInstance t htV hr (line_finrank d.Z d.ZS h.point_lt.le hZ hZS) hd).trans h.plus_le
  exact false_of_original_small_fixed hG d hempty hM hu hmany ho
    (hUS.trans inf_le_left) hfull hsmall

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion
