module
public import CFSG.Quasithin.Chapter10.SourceA5FullTensorPassage.FaithfulSections
public import CFSG.Quasithin.Chapter10.SourceA5OriginalCentralizerFaithfulness.Complete
public import Theory.Representation.BinaryOffender.Homogeneous.IsotypicFaithfulness
public import Theory.Representation.NormalConstituentDisplacement.FixedLine

/-!
# Faithfulness of the actual original local type

The original local central image is irreducible and its full normal-subgroup
restriction is isotypic. Clifford semisimplicity therefore identifies its
kernel with that of the full action, proving faithfulness for the literal
image of L₀. The canonical minimal full action supplies this image together
with the genuine cubic bound and faithful starred-offender conjugation.

Source: Aschbacher–Smith D.3.9(1), printed pp.199–200. This discharges the
constituent-faithfulness input; no inference from ambient faithfulness alone
is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
attribute [local instance] tensorSectionsElementary tensorSectionsLocalElementary

/-- The actual local image carries a faithful simple type of the normal A₅ square. -/
theorem source_a5_full_quotient_faithful_local_type_of_seed_eq_local
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hseed : D.seed = D.moduleSubgroup) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    let _ : J.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
    ∀ τ : Representation (ZMod 2) (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))
        (Additive D.fullCentralQuotient), τ.IsIrreducible → Function.Injective τ →
      (∀ (m : D.maximalLocal) (v : D.fullModule),
        τ (q m) (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
          Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
            ⟨(m : G) * (v : G) * (m : G)⁻¹,
              (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule m.property) v).mp
                v.property⟩)) →
      ∃ S : Subrepresentation (τ.comp J.subtype),
        S.toSubmodule = (originalLocalCentralLinearProjection D).range ∧
        S.toRepresentation.IsIrreducible ∧ Function.Injective S.toRepresentation ∧
        IsIsotypicOfType (ZMod 2)[J] (Representation.asModule (τ.comp J.subtype)) S.asSubmodule := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let J := ((localOrbit T L).subgroupOf M).map q
  let _ : J.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  intro τ hi hf hτ
  obtain ⟨S,hr,hS,htype⟩ := source_a5_full_quotient_isotypic_of_seed_eq_local
    D e hn ht htn hseed τ hi hτ
  let := NormalConstituentDisplacement.restriction_semisimple τ hi J
  exact ⟨S,hr,hS,faithful_restriction_subrepresentation_of_isotypic τ hf J S htype,htype⟩

/-- The canonical original action supplies the faithful local type and all
starred-offender premises from the actual minimal setup and cubic bound. -/
theorem source_minimal_full_quotient_faithful_local_type
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hD : D.IsMinimalFullModule) (hseed : D.seed = D.moduleSubgroup)
    (hbound : SourceFullModuleCubicBound D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    let _ : J.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
    ∃ ρ : Representation (ZMod 2) (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))
      (Additive D.fullCentralQuotient),
      Function.Injective ρ ∧ ρ.IsIrreducible ∧ cubicRatio ρ ≤ 2 ∧
      (∀ A ∈ ChapterD.QhatStar ρ,
        Function.Injective ((MulAut.conjNormal :
          (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)) →* MulAut J).comp A.subtype)) ∧
      (∀ (m : D.maximalLocal) (v : D.fullModule),
        ρ (q m) (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
          Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
            ⟨(m : G) * (v : G) * (m : G)⁻¹,
              (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule m.property) v).mp
                v.property⟩)) ∧
      ∃ S : Subrepresentation (ρ.comp J.subtype),
        S.toSubmodule = (originalLocalCentralLinearProjection D).range ∧
        S.toRepresentation.IsIrreducible ∧ Function.Injective S.toRepresentation ∧
        IsIsotypicOfType (ZMod 2)[J]
          (Representation.asModule (ρ.comp J.subtype)) S.asSubmodule := by
  dsimp only
  let := (source_full_module_reduced D).normal
  obtain ⟨ρ,hf,hi,hb,ha,hρ⟩ := source_minimal_full_quotient_starred_conjugation
    D e hD hbound hn ht htn
  exact ⟨ρ,hf,hi,hb,ha,hρ,source_a5_full_quotient_faithful_local_type_of_seed_eq_local
    D e hn ht htn hseed ρ hi hf hρ⟩

end CFSG.Quasithin.Chapter10
