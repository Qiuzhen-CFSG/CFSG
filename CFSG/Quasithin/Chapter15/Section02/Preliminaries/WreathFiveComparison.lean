module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveStarModels
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveStarLinearExclusions
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveStarExceptionalExclusions

/-!
# The complete failed-parabolic comparison in original 15.2.4

The actual C.2.7 input supplies its complete B.5 star-group catalogue. The
map from the original component to that star image has solvable kernel
of order prime to five, proved from the source central-kernel bound and
A.3.6. Each model exclusion therefore receives both the local A₅ and the
normalized five-residual through their literal maps. The triple cover of
A₆ is handled through its actual central quotient.

Every model is impossible. Thus when the original generated group has
nontrivial two-core, both quotient parabolics have generalized Fitting
equal to their two-core. This closes the C.2.7/A.3.15 comparison without
an additional classification or field-divisibility premise. The remaining
mixed-amalgam exclusion is separate.

Source: Aschbacher--Smith, original15.2.4, printed pp.1106--1107.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

private theorem composed_model_kernel {A D E : Type*} [Group A] [Group D] [Group E]
    (q : A →* D) (hq : Function.Surjective q) [Group.IsSolvable q.ker]
    (hk : ¬5 ∣ Nat.card q.ker) (e : D ≃* E) :
    Function.Surjective (e.toMonoidHom.comp q) ∧
    Group.IsSolvable (e.toMonoidHom.comp q).ker ∧
    ¬5 ∣ Nat.card (e.toMonoidHom.comp q).ker := by
  have he : (e.toMonoidHom.comp q).ker = q.ker := by ext x; simp
  exact ⟨e.surjective.comp hq,he.symm ▸ inferInstance,he.symm ▸ hk⟩

/-- The original local A₅ and normalized five-section exclude the complete
actual star catalogue, including central covers. -/
theorem source_wreath_five_star_contradiction
    {H K S W R M L Y : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn H) (hSH : S ≤ H)
    (heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hSyl : Chapter1.IsSylowIn 2 S W)
    (hL : L ∈ Chapter1.cComponentsIn W) (hKL : K ≤ L)
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (hsetup : Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple W R (W ⊓ M))
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hfit : generalizedFitting L = pCore 2 L) (hout : ¬L ≤ M)
    (hn : W ≤ normalizer (L : Set G)) : False := by
  obtain ⟨hm,hs,hfive⟩ := source_wreath_five_star_model_data hsetup hL hq hfit hout hn
  let q := toStarImage L R
  have hq : Function.Surjective q := toStarImage_surjective L R
  let : Group.IsSolvable q.ker := hs
  cases hm with
  | linearTwo F e =>
    obtain ⟨he,hs,hk⟩ := composed_model_kernel q hq hfive e
    let := hs
    exact source_local_component_star_rankOne_exclusion hK hSH heK hSyl hL hKL
      hYL hSN hc F (e.toMonoidHom.comp q) he hk
  | linearThree F e =>
    obtain ⟨he,hs,hk⟩ := composed_model_kernel q hq hfive e
    let := hs
    exact source_local_component_star_linearThree_exclusion hK hSH heK hSyl hL hKL
      hYL hSN hc F (e.toMonoidHom.comp q) he hk
  | symplectic F hF e =>
    obtain ⟨he,hs,hk⟩ := composed_model_kernel q hq hfive e
    let := hs
    exact source_local_component_star_symplectic_exclusion hK hSH heK hSyl hL hKL
      hYL hSN hc F (e.toMonoidHom.comp q) he hk
  | g2 F hF e =>
    obtain ⟨he,hs,hk⟩ := composed_model_kernel q hq hfive e
    let := hs
    exact source_local_component_star_g2_exclusion hK hSH heK hSyl hL hKL
      hYL hSN hc F (e.toMonoidHom.comp q) he hk
  | g2DerivedTwo e =>
    obtain ⟨he,hs,hk⟩ := composed_model_kernel q hq hfive e
    let := hs
    exact source_local_component_star_g2_derived_exclusion hSyl hL hYL hSN hc
      (e.toMonoidHom.comp q) he hk
  | alternating n hn e =>
    obtain ⟨he,hs,hk⟩ := composed_model_kernel q hq hfive e
    exact source_local_component_star_alternating_exclusion hSyl hL hYL hSN hc n hn
      (e.toMonoidHom.comp q) he hk
  | linearFiveTwo e =>
    obtain ⟨he,hs,hk⟩ := composed_model_kernel q hq hfive e
    exact source_local_component_star_linearFive_exclusion hSyl hL hYL hSN hc
      (e.toMonoidHom.comp q) he hk
  | tripleSix ez e =>
    exact source_local_component_star_tripleSix_exclusion hSyl hL hYL hSN hc q hq hfive ez e

open Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource

/-- The actual original wreath-five configuration has characteristic-two
quotient parabolics whenever its generated group has nontrivial two-core. -/
theorem source_HStar_wreath_five_quotient_parabolics
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (hcases : SourceCases.Dihedral (imageRepresentation M V hV.normalized) ∨
      SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn H ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧ ¬ K ≤ M ∧
      let L := ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K]
      let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
      let W := ChapterF.Source.generated L S
      let q := QuotientGroup.mk' (pCore 2 W)
      S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ S ∧
      (pCore 2 W ≠ ⊥ →
        ∀ i, generalizedFitting (((ChapterF.Source.parabolic L S i).subgroupOf W).map q) =
          pCore 2 (((ChapterF.Source.parabolic L S i).subgroupOf W).map q)) := by
  obtain ⟨l,hd,_⟩ := source_HStar_wreath_five_reduction
    hG T hempty hM hJ hu hmany hV hcases hH he
  obtain ⟨K,hK,heK,hout,hi,hJS,hconf⟩ :=
    source_HStar_wreath_five_failed_quotient_quasisimple_component
      hG T hempty hM hJ hu hmany hV hcases hH he
  refine ⟨K,hK,heK,hout,hi,hJS,?_⟩
  intro hcore
  by_contra hfailed
  obtain ⟨hSyl,hVcore,hWfit,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,hLfit,hnot,hYL,hq⟩ :=
    hconf hcore hfailed
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  have hYM : Y ≤ M := source_caseIIResidual_le T hM.1.2 (map_subtype_le _)
  have hMN : M ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp
      (source_dihedral_five_residual_normal T hM.1.2 hu hV l hd)
  have hc : Nat.card (Y ⧸ pCore 2 Y) = 5 := by
    rw [←(pCore 2 Y).index_eq_card]
    exact (source_dihedral_five_residual_core_index hG T hempty hM hJ hu hmany hV l
      ((primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)) hd).1
  exact source_wreath_five_star_contradiction hK (inf_le_left.trans hH.1.1.2)
    heK hSyl hL₁ hKL hYL (inf_le_left.trans (hM.1.2.trans hMN)) hc
    hsetup hq hLfit houtL hNL

end CFSG.Quasithin.Chapter15.Section02
