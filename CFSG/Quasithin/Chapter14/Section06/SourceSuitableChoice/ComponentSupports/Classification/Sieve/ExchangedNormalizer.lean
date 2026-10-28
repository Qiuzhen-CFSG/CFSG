module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.ExchangedStructure
public import Theory.GroupTheory.CComponent.PairSylowNormalizer
public import Theory.SpecificGroups.PSL3Two.Automorphisms.SylowStabilizer

/-!
# The original normalizer of the exchanged component stabilizer

Work intrinsically in Mc and use the actual pair product furnished by the
component alternatives. Each L₃(2) factor has self-normalizing Sylows; the
normal pair theorem gives N_Mc(N_T(K))=T. Mapping back to G retains the
literal intersection Mc∩N_G(N_T(K)). This removes the local-normalizer
premise of U3 in the exchanged support consumer.

The module and separated-support inputs remain with
qt-e-suitable-component-supports; original 14.6.18 remains with
qt-e-14625-source. Source: Aschbacher--Smith 14.6.21, 14.6.23(1) and
14.6.24(1), printed pp.1037--1039.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio
open Chapter13.Section08.Components.Models
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

/-- The exchanged branch supplies the literal local normalizer needed in U3. -/
theorem terminal_nonnormal_sylow_component_normalizer
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    Mc ⊓ normalizer (((T : Subgroup G) ⊓ normalizer (K : Set G) : Subgroup G) : Set G) = T := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  have hR := source_radical_eq_core hG T hempty hM hunique hmany hcard e hab hsolv Mc hout
  have hr : primeRank 3 Mc ≤ 2 :=
    (Chapter3.sqtk_of_mem_H hG hout.1.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  have hmodels := source_nonnormal_all_component_models
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK hn
  have hm (D : Subgroup Mc) (hD : D.IsCComponent) : ComponentQuotientModels D := by
    have hd : (D.map Mc.subtype).subgroupOf Mc = D :=
      comap_map_eq_self_of_injective Mc.subtype_injective D
    exact (hmodels (D.map Mc.subtype) (map_subtype_le D) (hd.symm ▸ hD)).transport
      (equivMapOfInjective D Mc.subtype Mc.subtype_injective).symm
  let P := T.subtype hout.1.2
  let B := K.subgroupOf Mc
  have heR := (terminal_nonnormal_residual_structure
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn).2.1
  have halt := component_models_alternatives hR hr hm P B hK
  have hnorm : normalizer (((P : Subgroup Mc) ⊓ normalizer (B : Set Mc) : Subgroup Mc) : Set Mc) = P := by
    rcases halt with ⟨he,_⟩ | ⟨ha,t,_,hnt,he⟩ | ⟨_,C,hC,hne,hnB,_⟩
    · have hBn : B.Normal := he ▸ (inferInstance : (solvableResidual Mc).Normal)
      exact (hn hBn).elim
    · have hne : B ≠ B.conjBy t⁻¹ := by
        intro hh
        have ht : t⁻¹ ∈ normalizer (B : Set Mc) := mem_normalizer_iff_map_conj_eq.mpr hh.symm
        exact hnt ((normalizer (B : Set Mc)).inv_mem_iff.mp ht)
      have hC : (B.conjBy t⁻¹).IsCComponent := hK.map_equiv (MulAut.conj t⁻¹)
      have hs : solvableResidual Mc = B ⊔ B.conjBy t⁻¹ := by
        apply SetLike.coe_injective
        exact he.trans (coe_mul_of_right_le_normalizer_left B (B.conjBy t⁻¹)
          ((le_cComponentLayer hC).trans (cComponentLayer_le_normalizer hK))).symm
      let : (B ⊔ B.conjBy t⁻¹).Normal := hs ▸ inferInstance
      exact hK.normalizer_sylow_component_eq_of_exchanged_pair P hR t⁻¹ hne
        (by rw [←hs,heR]; exact pResidual_sup_sylow_eq_top P)
        (Classical.choice ha) Matrix.PSL3Two.self_normalizing_sylow
    · exact (hn hnB).elim
  let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
  have hSM : S ≤ Mc := inf_le_left.trans hout.1.2
  have hi : (P : Subgroup Mc) ⊓ normalizer (B : Set Mc) = S.subgroupOf Mc := by
    rw [show B = K.subgroupOf Mc from rfl,←subgroupOf_normalizer_eq hKM]
    rfl
  have hiN : (normalizer (S : Set G)).subgroupOf Mc = (T : Subgroup G).subgroupOf Mc := by
    rw [subgroupOf_normalizer_eq hSM]
    rw [←hi]
    exact hnorm
  have hh := congrArg (Subgroup.map Mc.subtype) hiN
  rw [map_subgroupOf_eq_of_le hout.1.2,subgroupOf_map_subtype] at hh
  exact (inf_comm Mc (normalizer (S : Set G))).trans hh

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
