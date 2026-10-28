module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Normalizer.Source
public import Theory.SpecificGroups.BinaryLinear.ParabolicIntervalNormalizer

/-!
# The invariant binary-linear source normalizer

For the original H and S = N_T(H₁), the earlier exchanged-factor theorem
gives O₂(H) ≤ S, N_H(S) = T, and normalization of S by T. The literal
Mc/O₂(Mc) automorphism model carries this interval to Aut(PSL₄(2)) or
Aut(PSL₅(2)). Binary parabolic radicals control the image normalizer,
and lifting through the original quotient map places N_Mc(S) inside H.
The known H-normalizer then gives N_Mc(S) = T and the original index two.

The full invariant quotient is supplied by Closure/Models/InvariantSource;
CubicChoice discharges that model premise and constructs the suitable
involution in every cubic closure branch. The separate PSL₂(16) full-image
case is still needed for the complete original 14.6.14--15 assembly.

Source: Aschbacher--Smith, original 14.6.16, printed p.1035.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open BinaryLinear.OuterCyclic BinaryNaturalDual.ModelOrbits.AutomorphismModel
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
variable [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
include hG hempty hM hunique hmany hcard e hab hH

/-- Original 14.6.16 for either actual invariant binary-linear automorphism quotient. -/
theorem source_normalizer_invariant_closure
    (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (E : (Mc ⧸ pCore 2 Mc) ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    S.relIndex (T : Subgroup G) = 2 ∧ Mc ⊓ normalizer (S : Set G) = (T : Subgroup G) := by
  obtain ⟨hi,hHN,hQS,hTN⟩ := source_exchanged_normalizer_initial
    hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 d
  have hHMc : H ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hunique)
  have hTMc : (T : Subgroup G) ≤ Mc := hH.1.2.trans hHMc
  let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
  let E' := E.trans (projectiveAutEquiv (show 0 < n by omega))
  let f := E'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Mc))
  have hf : Function.Surjective f := E'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ E'.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hC : (H.subgroupOf Mc).pCoreIn 2 ≤ S.subgroupOf Mc := by
    rw [pCoreIn_subgroupOf 2 H Mc hHMc]
    exact subgroupOf_mono Mc hQS
  have hSn : (T.subtype hTMc : Subgroup Mc) ≤ normalizer (S.subgroupOf Mc : Set Mc) := by
    intro x hx
    exact S.le_normalizer_comap Mc.subtype (hTN hx).2
  have hN := BinaryLinear.automorphism_cover_interval_normalizer_le hn f hf hk
    (T.subtype hTMc) (H.subgroupOf Mc) (S.subgroupOf Mc)
    (subgroupOf_mono Mc hH.1.2) hC (subgroupOf_mono Mc inf_le_left) hSn
  refine ⟨hi,le_antisymm ?_ hTN⟩
  intro x hx
  rw [←hHN]
  have hxN : (⟨x,hx.1⟩ : Mc) ∈ normalizer (S.subgroupOf Mc : Set Mc) :=
    S.le_normalizer_comap Mc.subtype hx.2
  exact ⟨hN hxN,hx.2⟩
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
