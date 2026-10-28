module
public import CFSG.Quasithin.Chapter10.SourceA5FullTensorPassage.LocalFaithfulness
public import CFSG.Quasithin.Chapter10.SourceA5OriginalTensorBranch
public import CFSG.Quasithin.Chapter10.SourceA5FullTensorPassage.LocalModel
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.CubicBudget
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.ModelTransport
/-!
# The original same-seed local module is the full tensor module

For the minimal original setup, the actual local central image is a faithful
simple type and the full normal-subgroup restriction is isotypic. Its natural
or deleted tensor coordinates make every section of that type non-FF. A
starred cubic actor acts faithfully on two such sections if the restriction
is reducible, contradicting its two-rank fixed-codimension budget.

Thus the nonzero local central image is the whole quotient. The actual central
kernel and full commutator generation lift this to equality of the original
local and full modules. Existing marked recognition then gives the determinant
tensor model, without a separate irreducibility or module-equality premise.

Source: Aschbacher–Smith D.3.9 and D.3.7, printed pp.197–201.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
attribute [local instance] tensorSectionsElementary tensorSectionsLocalElementary

private theorem local_eq_full_of_irreducible_local_image
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {H : Type*} [Group H]
    (ρ : Representation (ZMod 2) H (Additive D.fullCentralQuotient)) [ρ.IsIrreducible]
    (S : Subrepresentation ρ)
    (hr : S.toSubmodule = (originalLocalCentralLinearProjection D).range) :
    D.moduleSubgroup = D.fullModule := by
  have ht : S = ⊤ := by
    rcases eq_bot_or_eq_top S with hb | ht
    · exact (originalLocalCentralLinearProjection_range_ne_bot D
        (hr.symm.trans (congrArg Subrepresentation.toSubmodule hb))).elim
    · exact ht
  apply source_local_eq_full_of_central_projection_surjective D
  intro y
  have hy : Additive.ofMul y ∈ S.toSubmodule := by rw [ht]; trivial
  rw [hr] at hy
  obtain ⟨v,hv⟩ := hy
  exact ⟨v.toMul,hv⟩


open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous

/-- The original minimal same-seed local module fills the full module. -/
theorem source_a5_local_eq_full_of_seed_eq_local
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule) (hseed : D.seed = D.moduleSubgroup)
    (hbound : SourceFullModuleCubicBound D) :
    D.moduleSubgroup = D.fullModule := by
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp hn
  let U := D.fullModule.subgroupOf D.maximalLocal
  let := (source_full_module_reduced D).normal
  let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
  let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
  let _ : J.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : FiniteDimensional (ZMod 2) (Additive D.fullCentralQuotient) := Module.Finite.of_finite
  obtain ⟨ρ,_hf,hi,hb,ha,hρ,S,hr,hS,hSf,htype⟩ :=
    source_minimal_full_quotient_faithful_local_type D e hD hseed hbound hn ht htn
  obtain ⟨A,hA⟩ := (ChapterD.QhatStar_nonempty_iff ρ).mpr hb
  have hsmall := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp
    (hA.1.2.2.2.trans_le hA.1.1)
  have hmodel := source_a5_original_local_type_models D e hn ht htn ρ hρ S hr hS hSf
  let : ρ.IsIrreducible := hi
  let : Nontrivial (Additive D.fullCentralQuotient) :=
    Subrepresentation.irreducible_module_nontrivial ρ
  let : IsSemisimpleModule (ZMod 2)[J] (Representation.asModule (ρ.comp J.subtype)) :=
    NormalConstituentDisplacement.restriction_semisimple ρ hi J
  let : Representation.IsIrreducible (ρ.comp J.subtype) := by
    apply irreducible_of_faithful_nonFF_sections ρ J S htype A hA.1.2.1 hsmall (ha A hA)
    dsimp only
    intro W _ _ σ X he
    exact faithful_nonFF_of_a5_local_type ρ J (J ⊔ A) le_sup_left S hSf hmodel σ X he
  exact local_eq_full_of_irreducible_local_image D (ρ.comp J.subtype) S hr

/-- Same-seed local equality upgrades to equality with the full module. -/
theorem source_a5_seed_eq_full_of_seed_eq_local
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule) (hseed : D.seed = D.moduleSubgroup)
    (hbound : SourceFullModuleCubicBound D) :
    D.seed = D.fullModule :=
  hseed.trans (source_a5_local_eq_full_of_seed_eq_local D e hn hD hseed hbound)

/-- The original same-seed local branch has its marked determinant tensor model,
with full/local equality and irreducibility discharged. -/
theorem source_a5_original_tensor_model_of_seed_eq_local
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule) (hseed : D.seed = D.moduleSubgroup)
    (hbound : SourceFullModuleCubicBound D) :
    Nonempty (SourceA5TensorModel D e) :=
  source_a5_original_tensor_model_of_seed_eq_full D e hn hD
    (source_a5_seed_eq_full_of_seed_eq_local D e hn hD hseed hbound) hbound

end CFSG.Quasithin.Chapter10
