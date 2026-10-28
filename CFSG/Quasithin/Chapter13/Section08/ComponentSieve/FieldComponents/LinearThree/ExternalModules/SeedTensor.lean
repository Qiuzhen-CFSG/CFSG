module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.ChiefDecomposition.Product
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.SeedTensor.QuotientSection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.Transport
public import Theory.Representation.PSL3Two.PointTensor.SeedSurjection

/-!
# The actual marked generating seed in the covered-A₆ branch

The source seed is the literal binary image of V₃ in U_H/V₁. Normalization
by P = L₁T transports to invariance under the same point-parabolic product
used in the group marking. Its cubic commutator identity gives a fixed-point-
free cubic action. On this binary plane the commuting point-parabolic factor
acts trivially, by the inverted-cubic multiplicity calculation.

The generating point seed supplies an equivariant surjection from the actual
point-permutation tensor. Nontrivial component action makes the image of the
point-core tensor nonzero, and its natural simple head supplies a literal
natural tensor chief section. The product identification and its point
marking remain unchanged. The source adapter retains L₀ centralization and
derives full cubic commutator generation from the actual seed identity.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(1), covered-A₆ paragraph, printed p.957.
-/

public section
open Representation Representation.BinaryOffender InvertedCubicTensor
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules

/-- A marked generating point seed gives a natural tensor chief section whenever
the component acts nontrivially. The tensor surjection and the section's natural
orientation are proved, using the same product identification as the seed. -/
theorem exists_naturalTensorChiefSection_of_generating_point_seed
    {J U : Type*} [Group J] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) J U) (eJ : J ≃* TensorGroup)
    (D : Submodule (ZMod 2) U)
    (hseed : BinaryLinearThree.PointTensor.IsGeneratingSeed
      (ρ.comp eJ.symm.toMonoidHom) D)
    (hn : ∃ k : BinaryLinearThree.Group, ∃ v, ρ (eJ.symm (k, 1)) v ≠ v) :
    ∃ L N : Subrepresentation ρ, IsNaturalTensorChiefSection ρ eJ L N := by
  obtain ⟨q, hq⟩ := BinaryLinearThree.PointTensor.exists_surjective
    (ρ.comp eJ.symm.toMonoidHom) D hseed
  exact exists_naturalTensorChiefSection_of_pointTensor_surjective ρ eJ q hq hn

private theorem tensorCubic_normal : tensorCubic.Normal := by
  constructor
  rintro _ ⟨s, hs, rfl⟩ ⟨k, t⟩
  refine ⟨t * s * t⁻¹, (inferInstance : (alternatingGroup (Fin 3)).Normal).conj_mem s hs t, ?_⟩
  simp

variable {G : Type*} [Group G] [Finite G]
    (H V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsMulCommutative (Source.Utilde H V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- The genuine source clauses produce a point-fixed generating seed with
the original marking. Normality of X* is derived from its marked product
image; no ambient normality of X or choice of chief-factor orientation is
assumed. The L₀ centralization and both cubic identities are retained. -/
theorem source_generating_point_seed
    (act : SourceAction H V₃ V₁) (eH : Source.Hstar H ≃* TensorGroup)
    (L₁ T L₀ X : Subgroup G)
    (hP : L₁ ⊔ T ≤ normalizer (V₃ : Set G))
    (hXH : X ≤ H) (hXP : X ≤ L₁ ⊔ T)
    (hPmark : (Source.starImage H (L₁ ⊔ T)).map eH.toMonoidHom =
      Matrix.PSL3Two.pointParabolicSL.prod (⊤ : Subgroup S₃))
    (hXmark : tensorCubic.map eH.symm.toMonoidHom = Source.starImage H X)
    (hd : Module.finrank (ZMod 2) (Geometry.seedSpace H V₃ V₁) = 2)
    (hcentral : ⁅L₀, V₃⁆ ≤ V₁)
    (hcomm : V₃ ≤ ⁅X, V₃⁆ ⊔ V₁) :
    BinaryLinearThree.PointTensor.IsGeneratingSeed
      (act.representation.comp eH.symm.toMonoidHom) (Geometry.seedSpace H V₃ V₁) ∧
    Geometry.seedSpace H V₃ V₁ ≤ fixedSpace act.representation (Source.starImage H L₀) ∧
    subspaceCommutator act.representation (Geometry.seedSpace H V₃ V₁)
      (Source.starImage H X) = Geometry.seedSpace H V₃ V₁ ∧
    subspaceCommutator act.representation ⊤ (Source.starImage H X) = ⊤ := by
  have hn : (Source.starImage H X).Normal := by
    rw [← hXmark]
    exact tensorCubic_normal.map eH.symm.toMonoidHom eH.symm.surjective
  have hseed := Geometry.CoveredProduct.seed_commutator_of_group_generation
    H V₃ V₁ act X hXH (hXP.trans hP) hcomm
  have hfull := Geometry.normal_seed_generation H V₃ V₁ act X hn hseed
  refine ⟨?_, Geometry.CoveredProduct.seed_fixed_of_group_commutator
    H V₃ V₁ act L₀ hcentral, hseed, hfull⟩
  apply BinaryLinearThree.PointTensor.generatingSeed_of_parabolic_plane _ _ hd
  · intro g hg v hv
    have hg' : g ∈ (Source.starImage H (L₁ ⊔ T)).map eH.toMonoidHom := by
      rwa [hPmark]
    obtain ⟨p, hp, rfl⟩ := hg'
    simpa using Geometry.seedSpace_invariant H V₃ V₁ act (L₁ ⊔ T) hP p hp v hv
  · intro v _ hv
    let s : S₃ →* Source.Hstar H :=
      eH.symm.toMonoidHom.comp (MonoidHom.inr BinaryLinearThree.Group S₃)
    have he : (alternatingGroup (Fin 3)).map s = Source.starImage H X := by
      change (alternatingGroup (Fin 3)).map
        (eH.symm.toMonoidHom.comp (MonoidHom.inr BinaryLinearThree.Group S₃)) = _
      rw [← Subgroup.map_map]
      exact hXmark
    apply ambient_fixedFree_of_commutator act.representation s (by rwa [he]) v
    exact hv
  · intro N hN
    apply Subrepresentation.toSubmodule_injective
    apply Geometry.seedSpace_generates H V₃ V₁ act N.toSubmodule
    · intro g v hv
      simpa using N.apply_mem_toSubmodule (eH g) hv
    · exact hN

/-- Construct a natural tensor chief section of the literal source action on
U_H/V₁. The component, cubic subgroup and seed parabolic use the given product
marking. The seed dimension, normalization, L₀ centralization and cubic identity
are the earlier source clauses; no chief section or orientation is assumed. -/
theorem source_natural_tensor_chief_section
    (act : SourceAction H V₃ V₁) (eH : Source.Hstar H ≃* TensorGroup)
    (K L₁ T L₀ X : Subgroup G)
    (hKmark : (Source.starImage H K).map eH.toMonoidHom =
      (⊤ : Subgroup BinaryLinearThree.Group).prod ⊥)
    (hn : ∃ k : Source.starImage H K, ∃ v, act.representation k v ≠ v)
    (hP : L₁ ⊔ T ≤ normalizer (V₃ : Set G))
    (hXH : X ≤ H) (hXP : X ≤ L₁ ⊔ T)
    (hPmark : (Source.starImage H (L₁ ⊔ T)).map eH.toMonoidHom =
      Matrix.PSL3Two.pointParabolicSL.prod (⊤ : Subgroup S₃))
    (hXmark : tensorCubic.map eH.symm.toMonoidHom = Source.starImage H X)
    (hd : Module.finrank (ZMod 2) (Geometry.seedSpace H V₃ V₁) = 2)
    (hcentral : ⁅L₀, V₃⁆ ≤ V₁)
    (hcomm : V₃ ≤ ⁅X, V₃⁆ ⊔ V₁) :
    ∃ L N : Subrepresentation act.representation,
      IsNaturalTensorChiefSection act.representation eH L N := by
  obtain ⟨hseed, _, _, _⟩ := source_generating_point_seed H V₃ V₁ act eH
    L₁ T L₀ X hP hXH hXP hPmark hXmark hd hcentral hcomm
  apply exists_naturalTensorChiefSection_of_generating_point_seed
    act.representation eH (Geometry.seedSpace H V₃ V₁) hseed
  obtain ⟨k, v, hv⟩ := hn
  have hk : eH k.val ∈ (⊤ : Subgroup BinaryLinearThree.Group).prod
      (⊥ : Subgroup S₃) := by
    rw [← hKmark]
    exact Subgroup.mem_map_of_mem eH.toMonoidHom k.property
  have he : eH k.val = ((eH k.val).1, 1) :=
    Prod.ext rfl (Subgroup.mem_bot.mp hk.2)
  refine ⟨(eH k.val).1, v, ?_⟩
  simpa only [← he, eH.symm_apply_apply] using hv

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
