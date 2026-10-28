module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.ComponentStructure.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Decomposition

/-!
# The full component sum on the original terminal section

The component classification by rank identifies Mc's component layer with
its solvable residual. The proved two-group outer action then gives the
literal supplement Mc = Mc∞T. These facts discharge the factorization
premise of the Gaschütz support-sum theorem for the entire original component
family. Its entries are the ambient images of actual C-components of Mc.

The second theorem constructs coordinates on the literal U/Z, where
U = ⟨(localModule T M)^Mc⟩ and Z = centralInvolutions T. Thus it needs no
additional representation or quotient-identification premise. This is the
sum assertion in 14.6.23(3); directness of the component summands remains a
separate natural-module obligation, and is not inferred from hatted directness.

Source: Aschbacher--Smith, 14.6.21--23, printed pp.1037--1038.
The individual quotient models and remaining module recognition belong to
qt-e-suitable-component-supports; original 14.6.18 belongs to qt-e-14625-source.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.OneCohomology
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Classification
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
    (hm : ∀ K : Subgroup G, K ≤ Mc → (K.subgroupOf Mc).IsCComponent →
      ComponentQuotientModels K)

include hG hempty hM hunique hmany hcard e hab hsolv hm

/-- The full literal component sum, with its Sylow supplement derived from the models. -/
theorem source_full_component_sum_sup_fixed_of_models
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (ρ : Representation (ZMod 2) Mc X)
    (c : BinaryConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) ρ) :
    (⨆ K : {K : Subgroup Mc // K.IsCComponent},
      c.imageSpace ⁅conjugateSpanBy (localModule T M) Mc, K.val.map Mc.subtype⁆) ⊔
        fixed ρ = ⊤ := by
  have hTH := (terminal_outside hG T hempty hM hunique hmany hcard e).1.2
  have hl := (terminal_residual_models_of_component_models
    hG T hempty hM hunique hmany hcard e hab hsolv hm).1
  have hp := (terminal_residual_structure_of_component_models
    hG T hempty hM hunique hmany hcard e hab hsolv hm).2
  apply source_component_sum_sup_fixed hG T hempty hM hunique hmany hcard e hab ρ c
    (fun K : {K : Subgroup Mc // K.IsCComponent} => K.val.map Mc.subtype)
    (fun K => map_subtype_le K.val)
  intro m
  have hmem : (m : G) ∈ ((solvableResidual Mc).map Mc.subtype : Set G) *
      ((T : Subgroup G) : Set G) := hp ▸ m.property
  obtain ⟨r,hr,s,hs,he⟩ := hmem
  obtain ⟨r,hr,rfl⟩ := hr
  refine ⟨r,?_,⟨s,hTH hs⟩,hs,Subtype.ext he⟩
  have hgen : (⨆ K : {K : Subgroup Mc // K.IsCComponent}, K.val) = cComponentLayer Mc := by
    apply le_antisymm
    · exact iSup_le fun K => le_cComponentLayer K.property
    · exact sSup_le fun K hK => le_iSup (fun K : {K : Subgroup Mc // K.IsCComponent} => K.val) ⟨K,hK⟩
  have heq : (⨆ K : {K : Subgroup Mc // K.IsCComponent},
      (K.val.map Mc.subtype).subgroupOf Mc) = solvableResidual Mc := by
    calc
      _ = (⨆ K : {K : Subgroup Mc // K.IsCComponent}, K.val) :=
        iSup_congr fun K => comap_map_eq_self_of_injective Mc.subtype_injective K.val
      _ = _ := hgen.trans hl
  exact heq.ge hr

/-- Construct the same component sum on the actual quotient U/Z. -/
theorem source_canonical_component_sum_of_models :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    let _ : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc) :=
      h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
    let U := conjugateSpanBy (localModule T M) Mc
    let Z := centralInvolutions T
    ∃ ρ : Representation (ZMod 2) Mc (Additive (U ⧸ Z.subgroupOf U)),
      ∃ c : BinaryConjugationSection Mc U Z ρ,
        (⨆ K : {K : Subgroup Mc // K.IsCComponent},
          c.imageSpace ⁅U, K.val.map Mc.subtype⁆) ⊔ fixed ρ = ⊤ := by
  dsimp only
  let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc) :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  obtain ⟨ρ,c,_⟩ := source_canonical_commutator_decomposition
    hG T hempty hM hunique hmany hcard e hab
  exact ⟨ρ,c,source_full_component_sum_sup_fixed_of_models
    hG T hempty hM hunique hmany hcard e hab hsolv hm ρ c⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports
