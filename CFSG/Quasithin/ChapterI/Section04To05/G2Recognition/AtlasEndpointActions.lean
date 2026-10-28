module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.AtlasFormCoordinates
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalAlignedSplit
public import Theory.SpecificGroups.G2.TernaryLevi

/-!
# Lifting the literal quotient-action comparison to whole endpoints

Both target GL₂(3) embeddings and their full semidirect decompositions are
constructed in TernaryLevi. A comparison of the original four-dimensional
quotient actions now extends to actual endpoint isomorphisms, retaining
the core, actor and Sylow-aligner maps. No model actor or splitting is an input.
The remaining comparison is precisely the quotient intertwining condition;
its construction and compatibility on the whole common middle remain open.

Source: Aschbacher–Smith I.4.5, printed p.417. The actual original pair is
supplied to the Chapter14 source application by Chapter14AtlasCoreModels.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
namespace CubicTorus
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
variable (t : CubicTorus c)

/-- A full original short endpoint map from a compatible quotient comparison. -/
noncomputable def cubicAtlasShortEndpointEquiv
    (hc : Nat.card (cubicOddCore c t.x)=243)
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V)
    (hform : ∀ v w,t.cubicLineScalar (t.cubicCommutatorLine hc v w)=
      Multiplicative.ofAdd (Atlas.G2.TernaryCore.shortForm (e v) (e w)))
    (κ : Atlas.G2.TernaryLevi.GL23 ≃* Atlas.G2.TernaryLevi.GL23)
    (haction : ∀ a v,e (t.cubicAbelianizationAction
      (inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm a)) v)=
      Atlas.G2.TernaryLevi.shortQuotientAction (κ a) (e v)) :
    cubicNormalizer c t.x ≃* Atlas.G2.LieParabolicSetup.parabolic₁ (F:=ZMod 3) :=
  (t.cubicSplitEquiv hc).symm.trans ((SemidirectProduct.congr
    (t.cubicAtlasShortEquiv hc e hform) κ
    (by
      intro a
      apply MulEquiv.ext
      intro x
      exact t.cubicAtlasShortEquiv_action hc e hform a
        (Atlas.G2.TernaryLevi.endpointEmbedding false (κ a))
        (Atlas.G2.TernaryLevi.embedding_commutes false (κ a)) (haction a) x)).trans
      (Atlas.G2.TernaryLevi.splitEquiv false))

/-- A full original long endpoint map with the opposite literal root convention. -/
noncomputable def cubicAtlasLongEndpointEquiv
    (hc : Nat.card (cubicOddCore c t.x)=243)
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V)
    (hform : ∀ v w,t.cubicLineScalar (t.cubicCommutatorLine hc v w)=
      Multiplicative.ofAdd (Atlas.G2.TernaryCore.longForm (e v) (e w)))
    (κ : Atlas.G2.TernaryLevi.GL23 ≃* Atlas.G2.TernaryLevi.GL23)
    (haction : ∀ a v,e (t.cubicAbelianizationAction
      (inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm a)) v)=
      Atlas.G2.TernaryLevi.longQuotientAction (κ a) (e v)) :
    cubicNormalizer c t.x ≃* Atlas.G2.LieParabolicSetup.parabolic₂ (F:=ZMod 3) :=
  (t.cubicSplitEquiv hc).symm.trans ((SemidirectProduct.congr
    (t.cubicAtlasLongEquiv hc e hform) κ
    (by
      intro a
      apply MulEquiv.ext
      intro x
      exact t.cubicAtlasLongEquiv_action hc e hform a
        (Atlas.G2.TernaryLevi.endpointEmbedding true (κ a))
        (Atlas.G2.TernaryLevi.embedding_commutes true (κ a)) (haction a) x)).trans
      (Atlas.G2.TernaryLevi.splitEquiv true))

section Short
variable (hc : Nat.card (cubicOddCore c t.x)=243)
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V)
    (hform : ∀ v w,t.cubicLineScalar (t.cubicCommutatorLine hc v w)=
      Multiplicative.ofAdd (Atlas.G2.TernaryCore.shortForm (e v) (e w)))
    (κ : Atlas.G2.TernaryLevi.GL23 ≃* Atlas.G2.TernaryLevi.GL23)
    (haction : ∀ a v,e (t.cubicAbelianizationAction
      (inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm a)) v)=
      Atlas.G2.TernaryLevi.shortQuotientAction (κ a) (e v))

theorem cubicAtlasShortEndpointEquiv_core (x : cubicOddCore c t.x) :
    (t.cubicAtlasShortEndpointEquiv hc e hform κ haction
      (inclusion t.cubicCore_le_normalizer x):Atlas.G2.Model (ZMod 3))=
        t.cubicAtlasShortEquiv hc e hform x := by
  have hx : inclusion t.cubicCore_le_normalizer x=
      t.cubicSplitEquiv hc (SemidirectProduct.inl x) :=
    Subtype.ext (t.cubicSplitEquiv_inl hc x).symm
  rw [hx]
  change (Atlas.G2.TernaryLevi.splitEquiv false
    (SemidirectProduct.congr _ _ _ ((t.cubicSplitEquiv hc).symm
      (t.cubicSplitEquiv hc (SemidirectProduct.inl x)))):Atlas.G2.Model (ZMod 3))=_
  rw [MulEquiv.symm_apply_apply]
  change (Atlas.G2.TernaryLevi.splitEquiv false
    ⟨t.cubicAtlasShortEquiv hc e hform x,κ 1⟩:Atlas.G2.Model (ZMod 3))=_
  rw [map_one]
  exact Atlas.G2.TernaryLevi.splitEquiv_inl false (t.cubicAtlasShortEquiv hc e hform x)

theorem cubicAtlasShortEndpointEquiv_actor (a : Atlas.G2.TernaryLevi.GL23) :
    (t.cubicAtlasShortEndpointEquiv hc e hform κ haction
      (inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm a)):
        Atlas.G2.Model (ZMod 3))=Atlas.G2.TernaryLevi.embedding false (κ a) := by
  have hx : inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm a)=
      t.cubicSplitEquiv hc (SemidirectProduct.inr a) :=
    Subtype.ext (t.cubicSplitEquiv_inr hc a).symm
  rw [hx]
  change (Atlas.G2.TernaryLevi.splitEquiv false
    (SemidirectProduct.congr _ _ _ ((t.cubicSplitEquiv hc).symm
      (t.cubicSplitEquiv hc (SemidirectProduct.inr a)))):Atlas.G2.Model (ZMod 3))=_
  rw [MulEquiv.symm_apply_apply]
  change (Atlas.G2.TernaryLevi.splitEquiv false
    ⟨t.cubicAtlasShortEquiv hc e hform 1,κ a⟩:Atlas.G2.Model (ZMod 3))=_
  rw [map_one]
  exact Atlas.G2.TernaryLevi.splitEquiv_inr false (κ a)
end Short

section Long
variable (hc : Nat.card (cubicOddCore c t.x)=243)
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V)
    (hform : ∀ v w,t.cubicLineScalar (t.cubicCommutatorLine hc v w)=
      Multiplicative.ofAdd (Atlas.G2.TernaryCore.longForm (e v) (e w)))
    (κ : Atlas.G2.TernaryLevi.GL23 ≃* Atlas.G2.TernaryLevi.GL23)
    (haction : ∀ a v,e (t.cubicAbelianizationAction
      (inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm a)) v)=
      Atlas.G2.TernaryLevi.longQuotientAction (κ a) (e v))

theorem cubicAtlasLongEndpointEquiv_core (x : cubicOddCore c t.x) :
    (t.cubicAtlasLongEndpointEquiv hc e hform κ haction
      (inclusion t.cubicCore_le_normalizer x):Atlas.G2.Model (ZMod 3))=
        t.cubicAtlasLongEquiv hc e hform x := by
  have hx : inclusion t.cubicCore_le_normalizer x=
      t.cubicSplitEquiv hc (SemidirectProduct.inl x) :=
    Subtype.ext (t.cubicSplitEquiv_inl hc x).symm
  rw [hx]
  change (Atlas.G2.TernaryLevi.splitEquiv true
    (SemidirectProduct.congr _ _ _ ((t.cubicSplitEquiv hc).symm
      (t.cubicSplitEquiv hc (SemidirectProduct.inl x)))):Atlas.G2.Model (ZMod 3))=_
  rw [MulEquiv.symm_apply_apply]
  change (Atlas.G2.TernaryLevi.splitEquiv true
    ⟨t.cubicAtlasLongEquiv hc e hform x,κ 1⟩:Atlas.G2.Model (ZMod 3))=_
  rw [map_one]
  exact Atlas.G2.TernaryLevi.splitEquiv_inl true (t.cubicAtlasLongEquiv hc e hform x)

theorem cubicAtlasLongEndpointEquiv_actor (a : Atlas.G2.TernaryLevi.GL23) :
    (t.cubicAtlasLongEndpointEquiv hc e hform κ haction
      (inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm a)):
        Atlas.G2.Model (ZMod 3))=Atlas.G2.TernaryLevi.embedding true (κ a) := by
  have hx : inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm a)=
      t.cubicSplitEquiv hc (SemidirectProduct.inr a) :=
    Subtype.ext (t.cubicSplitEquiv_inr hc a).symm
  rw [hx]
  change (Atlas.G2.TernaryLevi.splitEquiv true
    (SemidirectProduct.congr _ _ _ ((t.cubicSplitEquiv hc).symm
      (t.cubicSplitEquiv hc (SemidirectProduct.inr a)))):Atlas.G2.Model (ZMod 3))=_
  rw [MulEquiv.symm_apply_apply]
  change (Atlas.G2.TernaryLevi.splitEquiv true
    ⟨t.cubicAtlasLongEquiv hc e hform 1,κ a⟩:Atlas.G2.Model (ZMod 3))=_
  rw [map_one]
  exact Atlas.G2.TernaryLevi.splitEquiv_inr true (κ a)
end Long
end CubicTorus
namespace CubicTorus
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
variable (t : CubicTorus c) (hc : Nat.card (cubicOddCore c t.x)=243)

/-- Quotient-level input, allowing the basis change of the original GL₂(3) marking.
No full-core or endpoint equivalence is assumed. -/
structure ShortQuotientComparison where
  coordinates : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V
  actor : Atlas.G2.TernaryLevi.GL23 ≃* Atlas.G2.TernaryLevi.GL23
  form : ∀ v w,t.cubicLineScalar (t.cubicCommutatorLine hc v w)=
    Multiplicative.ofAdd (Atlas.G2.TernaryCore.shortForm (coordinates v) (coordinates w))
  intertwines : ∀ a v,coordinates (t.cubicAbelianizationAction
    (inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm a)) v)=
      Atlas.G2.TernaryLevi.shortQuotientAction (actor a) (coordinates v)

/-- The analogous comparison with the literal long-root quotient convention. -/
structure LongQuotientComparison where
  coordinates : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V
  actor : Atlas.G2.TernaryLevi.GL23 ≃* Atlas.G2.TernaryLevi.GL23
  form : ∀ v w,t.cubicLineScalar (t.cubicCommutatorLine hc v w)=
    Multiplicative.ofAdd (Atlas.G2.TernaryCore.longForm (coordinates v) (coordinates w))
  intertwines : ∀ a v,coordinates (t.cubicAbelianizationAction
    (inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm a)) v)=
      Atlas.G2.TernaryLevi.longQuotientAction (actor a) (coordinates v)

/-- Checking two specified actors suffices for the full quotient comparison. -/
theorem short_quotient_intertwines_of_generators
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V)
    (κ : Atlas.G2.TernaryLevi.GL23 ≃* Atlas.G2.TernaryLevi.GL23)
    (h : ∀ b v,e (t.cubicAbelianizationAction
      (inclusion t.cubicLevi_le_normalizer
        ((t.cubicLeviLinearEquiv hc).symm (Atlas.G2.TernaryLevi.generator b))) v)=
      Atlas.G2.TernaryLevi.shortQuotientAction (κ (Atlas.G2.TernaryLevi.generator b)) (e v)) :
    ∀ a v,e (t.cubicAbelianizationAction
      (inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm a)) v)=
      Atlas.G2.TernaryLevi.shortQuotientAction (κ a) (e v) :=
  Atlas.G2.TernaryLevi.equivariant_of_generators
    (t.cubicAbelianizationAction.comp ((inclusion t.cubicLevi_le_normalizer).comp
      (t.cubicLeviLinearEquiv hc).symm.toMonoidHom))
    (Atlas.G2.TernaryLevi.shortQuotientAction.comp κ.toMonoidHom) e h

theorem long_quotient_intertwines_of_generators
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V)
    (κ : Atlas.G2.TernaryLevi.GL23 ≃* Atlas.G2.TernaryLevi.GL23)
    (h : ∀ b v,e (t.cubicAbelianizationAction
      (inclusion t.cubicLevi_le_normalizer
        ((t.cubicLeviLinearEquiv hc).symm (Atlas.G2.TernaryLevi.generator b))) v)=
      Atlas.G2.TernaryLevi.longQuotientAction (κ (Atlas.G2.TernaryLevi.generator b)) (e v)) :
    ∀ a v,e (t.cubicAbelianizationAction
      (inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm a)) v)=
      Atlas.G2.TernaryLevi.longQuotientAction (κ a) (e v) :=
  Atlas.G2.TernaryLevi.equivariant_of_generators
    (t.cubicAbelianizationAction.comp ((inclusion t.cubicLevi_le_normalizer).comp
      (t.cubicLeviLinearEquiv hc).symm.toMonoidHom))
    (Atlas.G2.TernaryLevi.longQuotientAction.comp κ.toMonoidHom) e h
end CubicTorus

namespace AlignedCubicPair
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
variable {t : CubicTorus c} (p : AlignedCubicPair t)

/-- The entire original first endpoint from its quotient comparison. -/
noncomputable def leftAtlasEndpointEquiv (l : t.ShortQuotientComparison p.core_order) :
    p.leftEndpoint ≃* Atlas.G2.LieParabolicSetup.parabolic₁ (F:=ZMod 3) :=
  t.cubicAtlasShortEndpointEquiv p.core_order l.coordinates l.form l.actor l.intertwines

/-- The entire opposite endpoint with the original Sylow aligner. -/
noncomputable def rightAtlasEndpointEquiv (r : t.swap.LongQuotientComparison p.right_core_order) :
    p.rightEndpoint ≃* Atlas.G2.LieParabolicSetup.parabolic₂ (F:=ZMod 3) :=
  p.rightEndpointEquiv.symm.trans (t.swap.cubicAtlasLongEndpointEquiv p.right_core_order
    r.coordinates r.form r.actor r.intertwines)

/-- The endpoint map extends the reconstructed core map with precisely these coordinates. -/
theorem leftAtlasEndpointEquiv_core (l : t.ShortQuotientComparison p.core_order) (x : p.leftCore) :
    (p.leftAtlasEndpointEquiv l (inclusion t.cubicCore_le_normalizer x):Atlas.G2.Model (ZMod 3))=
      t.cubicAtlasShortEquiv p.core_order l.coordinates l.form x :=
  t.cubicAtlasShortEndpointEquiv_core p.core_order _ _ _ l.intertwines x

/-- The right extension uses the literal transported original core inclusion. -/
theorem rightAtlasEndpointEquiv_core (r : t.swap.LongQuotientComparison p.right_core_order)
    (x : cubicOddCore (swapFactors c) t.swap.x) :
    (p.rightAtlasEndpointEquiv r
      (p.rightEndpointEquiv (inclusion t.swap.cubicCore_le_normalizer x)):Atlas.G2.Model (ZMod 3))=
      t.swap.cubicAtlasLongEquiv p.right_core_order r.coordinates r.form x := by
  change (t.swap.cubicAtlasLongEndpointEquiv _ _ _ _ r.intertwines
    (p.rightEndpointEquiv.symm (p.rightEndpointEquiv _)):Atlas.G2.Model (ZMod 3))=_
  rw [MulEquiv.symm_apply_apply]
  exact t.swap.cubicAtlasLongEndpointEquiv_core p.right_core_order _ _ _ r.intertwines x

/-- The entire GL₂(3) actor, with its stated basis change, is retained. -/
theorem leftAtlasEndpointEquiv_actor (l : t.ShortQuotientComparison p.core_order)
    (a : Atlas.G2.TernaryLevi.GL23) :
    (p.leftAtlasEndpointEquiv l
      (inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv p.core_order).symm a)):
        Atlas.G2.Model (ZMod 3))=Atlas.G2.TernaryLevi.embedding false (l.actor a) :=
  t.cubicAtlasShortEndpointEquiv_actor p.core_order _ _ _ l.intertwines a

/-- The whole-actor formula retains the original opposite Sylow alignment. -/
theorem rightAtlasEndpointEquiv_actor (r : t.swap.LongQuotientComparison p.right_core_order)
    (a : Atlas.G2.TernaryLevi.GL23) :
    (p.rightAtlasEndpointEquiv r
      (p.rightEndpointEquiv (inclusion t.swap.cubicLevi_le_normalizer
        ((t.swap.cubicLeviLinearEquiv p.right_core_order).symm a))):
        Atlas.G2.Model (ZMod 3))=Atlas.G2.TernaryLevi.embedding true (r.actor a) := by
  change (t.swap.cubicAtlasLongEndpointEquiv _ _ _ _ r.intertwines
    (p.rightEndpointEquiv.symm (p.rightEndpointEquiv _)):Atlas.G2.Model (ZMod 3))=_
  rw [MulEquiv.symm_apply_apply]
  exact t.swap.cubicAtlasLongEndpointEquiv_actor p.right_core_order _ _ _ r.intertwines a
end AlignedCubicPair

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
