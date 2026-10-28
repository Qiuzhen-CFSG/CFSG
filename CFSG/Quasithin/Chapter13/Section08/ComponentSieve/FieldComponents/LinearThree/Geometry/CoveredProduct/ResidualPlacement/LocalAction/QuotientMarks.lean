module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.QuotientActions

/-!
# The actual quotient maps marking the two covered residuals

Relative normality makes the inclusion-induced map between two-core
quotients injective. The map retains conjugation by each ambient element.
Specializing it to L₀ and X preserves both source marks in L₁/O₂(L₁).
Every element of T∩L fixes the L₀ mark, by the previously proved central
preimage calculation. The factorization premise is exactly 13.2.2(3).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 and Lemma 13.2.2(3), printed p.877; 13.8.21(1), p.957.
Cubic orders, generation of the order-nine quotient, and existence of an
inverter are separate obligations, not assumptions in a conclusion record.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A relatively normal subgroup has a normal image in the intrinsic quotient. -/
theorem localImage_normal (B A : Subgroup G) (hAB : A ≤ B)
    (hn : B ≤ normalizer (A : Set G)) : (Source.starImage B A).Normal := by
  let : (A.subgroupOf B).Normal := (normal_subgroupOf_iff_le_normalizer hAB).mpr hn
  exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective (pCore 2 B))

/-- The injective map between the intrinsic two-core quotients induced by
 inclusion of a relatively normal subgroup. -/
noncomputable def localCoreMap (B A : Subgroup G) (hAB : A ≤ B)
    (hn : B ≤ normalizer (A : Set G)) : (A ⧸ pCore 2 A) →* (B ⧸ pCore 2 B) :=
  (Source.starImage B A).subtype.comp
    (normalStarEquiv B A hAB (localImage_normal B A hAB hn)).toMonoidHom

theorem localCoreMap_injective (B A : Subgroup G) (hAB : A ≤ B)
    (hn : B ≤ normalizer (A : Set G)) : Function.Injective (localCoreMap B A hAB hn) :=
  Subtype.val_injective.comp (normalStarEquiv B A hAB (localImage_normal B A hAB hn)).injective

theorem localCoreMap_mk (B A : Subgroup G) (hAB : A ≤ B)
    (hn : B ≤ normalizer (A : Set G)) (x : A) :
    localCoreMap B A hAB hn (QuotientGroup.mk' (pCore 2 A) x) =
      QuotientGroup.mk' (pCore 2 B) (inclusion hAB x) :=
  normalStarEquiv_mk B A hAB (localImage_normal B A hAB hn) x

theorem localCoreMap_range (B A : Subgroup G) (hAB : A ≤ B)
    (hn : B ≤ normalizer (A : Set G)) :
    (localCoreMap B A hAB hn).range = Source.starImage B A := by
  rw [localCoreMap, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (normalStarEquiv B A hAB (localImage_normal B A hAB hn)).surjective,
    ← MonoidHom.range_eq_map, range_subtype]

/-- Both quotient actions are still conjugation by the same ambient element. -/
theorem localCoreMap_equivariant (B A : Subgroup G) (hAB : A ≤ B)
    (hn : B ≤ normalizer (A : Set G)) (t : G)
    (htA : t ∈ normalizer (A : Set G)) (htB : t ∈ normalizer (B : Set G))
    (x : A ⧸ pCore 2 A) :
    localCoreMap B A hAB hn (coreAction A ⟨t, htA⟩ x) =
      coreAction B ⟨t, htB⟩ (localCoreMap B A hAB hn x) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) x
  rw [coreAction_mk, localCoreMap_mk, localCoreMap_mk, coreAction_mk]
  rfl

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
variable {G : Type*} [Group G]

/-- L₁ normalizes L₀, using only T-normality of L. -/
theorem one_normalizes_zero (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G)) :
    one L T V₁ ≤ normalizer (zero L : Set G) :=
  (one_le L T V₁).trans (inf_le_left.trans
    ((sup_le L.le_normalizer hTL).trans (normalizer_le_zero_normalizer L)))

/-- The commutator defining X lies in L, which is normal relative to LT. -/
theorem plus_le_L (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G)) : plus L T V₁ ≤ L := by
  have hn : one L T V₁ ≤ normalizer (L : Set G) :=
    (one_le L T V₁).trans (inf_le_left.trans (sup_le L.le_normalizer hTL))
  have hc : ⁅one L T V₁, L⁆ ≤ L := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp hn
  exact (residual_le _).trans ((commutator_mono le_rfl inf_le_right).trans hc)

/-- The earlier factorization 13.2.2(3) places both source factors in L₁. -/
theorem zero_le_one_of_factorization (L T V₁ : Subgroup G)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) : zero L ≤ one L T V₁ := by
  rw [hfactor]
  exact le_sup_right

/-- Together with relative normality, that factorization also places L₁ in L. -/
theorem one_le_L_of_factorization (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) : one L T V₁ ≤ L := by
  rw [hfactor]
  exact sup_le (plus_le_L L T V₁ hTL) (zero_le L)

variable [Finite G]

/-- The marked embedding of L₀/O₂(L₀) into L₁/O₂(L₁). The factorization
 premise is exactly the earlier clause 13.2.2(3). -/
noncomputable def zeroCoreMap (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) :
    (zero L ⧸ pCore 2 (zero L)) →* (one L T V₁ ⧸ pCore 2 (one L T V₁)) :=
  localCoreMap (one L T V₁) (zero L) (zero_le_one_of_factorization L T V₁ hfactor)
    (one_normalizes_zero L T V₁ hTL)

/-- The other marked embedding comes from the literal commutator residual X. -/
noncomputable def plusCoreMap (L T V₁ : Subgroup G)
    (hTV : T ≤ normalizer (V₁ : Set G)) :
    (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) →*
      (one L T V₁ ⧸ pCore 2 (one L T V₁)) :=
  localCoreMap (one L T V₁) (plus L T V₁) (plus_le_one L T V₁ hTV)
    (one_normalizes_plus L T V₁)

theorem zeroCoreMap_injective (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) :
    Function.Injective (zeroCoreMap L T V₁ hTL hfactor) :=
  localCoreMap_injective _ _ _ _

theorem plusCoreMap_injective (L T V₁ : Subgroup G)
    (hTV : T ≤ normalizer (V₁ : Set G)) :
    Function.Injective (plusCoreMap L T V₁ hTV) :=
  localCoreMap_injective _ _ _ _

/-- The same element of T∩L fixes the marked L₀ direction pointwise. -/
theorem zeroCoreMap_fixed (L T V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hTV : T ≤ normalizer (V₁ : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (t : (T ⊓ L : Subgroup G)) (x : zero L ⧸ pCore 2 (zero L)) :
    coreAction (one L T V₁) ⟨t.val, T_normalizes_one L T V₁ hTV t.property.1⟩
      (zeroCoreMap L T V₁ hTL hfactor x) = zeroCoreMap L T V₁ hTL hfactor x := by
  rw [zeroCoreMap, ← localCoreMap_equivariant _ _ _ _ t.val
    (L_normalizes_zero L t.property.2)]
  have ht := L_centralizes_zero_quotient L ⟨t.val, t.property.2⟩
  rw [ht]
  rfl

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
