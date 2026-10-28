module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking.SourceAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking.Quotients
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The literal source radical R₁

Notation 13.2.1 defines M₁ = N_{LT}(V₁), L₁ = O²(M₁), and R₁ as the
preimage in T of O₂(M̄₁). The bar here is the actual action on V, with
kernel C_{M₁}(V), not the star quotient by O₂(H). These definitions retain
both maps. Sylow supplementation proves M₁ = L₁T.

Once (L₁T)* is marked as the line parabolic, |L₁T| = 6·2ⁿ. The earlier
full conjugation action on the four-group V₃/V₁ has image of order six,
so its kernel is a two-group. The centralizer of V lies in that kernel.
Thus the two-core lifts through the bar action, and its preimage in T is
exactly O₂(L₁T). This proves the needed identification in this branch
without assuming it or importing the exceptional covered-A₆ order analysis.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 (printed p.877), the standing setup of §13.8 (p.946),
and the opening parabolic step of 13.8.19 (p.953).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking
variable {G : Type*} [Group G] [Finite G]


/-- The parabolic image has order 24 and its quotient kernel is a two-group. -/
private theorem parabolic_card (H P : Subgroup G) (hPH : P ≤ H)
    (e : Source.Hstar H ≃* BinaryLinearThree.Group)
    (he : (Source.starImage H P).map e.toMonoidHom = Matrix.PSL3Two.lineParabolicSL) :
    ∃ n : ℕ, Nat.card P = 6 * 2 ^ n := by
  let f := (QuotientGroup.mk' (pCore 2 H)).comp (Subgroup.inclusion hPH)
  have hr : f.range = Source.starImage H P := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨⟨p.val, hPH p.property⟩, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p.val, hp⟩, rfl⟩
  have hk : IsPGroup 2 f.ker := by
    dsimp only [f]
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective (Subgroup.inclusion hPH) (Subgroup.inclusion_injective hPH)
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  have hcard : Nat.card f.range = 24 := by
    rw [hr, Nat.card_congr (e.subgroupMap (Source.starImage H P)).toEquiv]
    change Nat.card ((Source.starImage H P).map e.toMonoidHom) = 24
    rw [he]
    exact Matrix.PSL3Two.card_lineParabolicSL
  refine ⟨n + 2, ?_⟩
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker, hn, hcard] at hc
  rw [← hc, pow_add]
  ring


/-- The actual action of a normalizing local group on V. -/
def fullAction (P V : Subgroup G) (hPV : P ≤ normalizer (V : Set G)) : P →* MulAut V :=
  V.normalizerMonoidHom.comp (Subgroup.inclusion hPV)

omit [Finite G] in
/-- The action kernel is exactly the source relative centralizer. -/
theorem fullAction_ker (P V : Subgroup G) (hPV : P ≤ normalizer (V : Set G)) :
    (fullAction P V hPV).ker = (centralizer (V : Set G)).subgroupOf P := by
  change V.normalizerMonoidHom.ker.comap (Subgroup.inclusion hPV) = _
  rw [Subgroup.normalizerMonoidHom_ker]
  rfl

/-- The preimage in T of the core of the actual action image of P. -/
def radicalPreimage (P V : Subgroup G) (T : Sylow 2 G)
    (hTP : (T : Subgroup G) ≤ P) (hPV : P ≤ normalizer (V : Set G)) : Subgroup G :=
  ((pCore 2 (fullAction P V hPV).range).comap
    ((fullAction P V hPV).rangeRestrict.comp (Subgroup.inclusion hTP))).map
      (T : Subgroup G).subtype

private theorem radicalPreimage_eq_core (P V : Subgroup G) (T : Sylow 2 G)
    (hTP : (T : Subgroup G) ≤ P) (hPV : P ≤ normalizer (V : Set G))
    (hk : IsPGroup 2 (fullAction P V hPV).ker) :
    radicalPreimage P V T hTP hPV = P.pCoreIn 2 := by
  have hkr : IsPGroup 2 (fullAction P V hPV).rangeRestrict.ker := by
    rwa [MonoidHom.ker_rangeRestrict]
  have hc := (fullAction P V hPV).rangeRestrict.comap_pCore_of_ker_isPGroup
    (fullAction P V hPV).rangeRestrict_surjective hkr
  unfold radicalPreimage
  rw [← Subgroup.comap_comap, hc]
  apply le_antisymm
  · rintro x ⟨t, ht, rfl⟩
    exact ⟨⟨t.val, hTP t.property⟩, ht, rfl⟩
  · rintro x ⟨p, hp, rfl⟩
    have ht : p.val ∈ (T : Subgroup G) :=
      pCore_isPGroup.le_sylow_of_normal (T.subtype hTP) hp
    exact ⟨⟨p.val, ht⟩, hp, rfl⟩

variable {H P V V₃ V₁ : Subgroup G}
    [(V₁.subgroupOf V₃).Normal] [IsKleinFour (V₃ ⧸ V₁.subgroupOf V₃)]

private theorem seed_kernel_two {hPn : P ≤ normalizer (V₃ : Set G)}
    (a : SeedAction V₃ V₁ P hPn) (hPH : P ≤ H)
    (e : Source.Hstar H ≃* BinaryLinearThree.Group)
    (he : (Source.starImage H P).map e.toMonoidHom = Matrix.PSL3Two.lineParabolicSL) :
    IsPGroup 2 a.action.ker := by
  obtain ⟨n, hn⟩ := parabolic_card H P hPH e he
  have hi : a.action.ker.index = 6 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ a.surjective,
      Subgroup.card_top, IsKleinFour.card_mulAut]
  have hc := a.action.ker.card_mul_index
  rw [hi, hn, Nat.mul_comm 6] at hc
  exact IsPGroup.of_card (Nat.mul_right_cancel (by decide : 0 < 6) hc)

omit [Finite G] in
omit [Finite G] [IsKleinFour (V₃ ⧸ V₁.subgroupOf V₃)] in
private theorem fullAction_kernel_le_seed_kernel {hPn : P ≤ normalizer (V₃ : Set G)}
    (a : SeedAction V₃ V₁ P hPn) (hPV : P ≤ normalizer (V : Set G))
    (h3V : V₃ ≤ V) : (fullAction P V hPV).ker ≤ a.action.ker := by
  intro p hp
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro q
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf V₃) q
  rw [a.conjugation]
  have hf := congrArg (fun f : MulAut V => (f ⟨v.val, h3V v.property⟩).val)
    (MonoidHom.mem_ker.mp hp)
  have hv : p.val * v.val * p.val⁻¹ = v.val := hf
  exact congrArg (QuotientGroup.mk' (V₁.subgroupOf V₃)) (Subtype.ext hv)

private theorem radicalPreimage_eq_core_of_marking (T : Sylow 2 G)
    (hTP : (T : Subgroup G) ≤ P) {hPn : P ≤ normalizer (V₃ : Set G)}
    (a : SeedAction V₃ V₁ P hPn) (hPV : P ≤ normalizer (V : Set G))
    (h3V : V₃ ≤ V) (hPH : P ≤ H)
    (e : Source.Hstar H ≃* BinaryLinearThree.Group)
    (he : (Source.starImage H P).map e.toMonoidHom = Matrix.PSL3Two.lineParabolicSL) :
    radicalPreimage P V T hTP hPV = P.pCoreIn 2 :=
  radicalPreimage_eq_core P V T hTP hPV
    ((seed_kernel_two a hPH e he).to_le (fullAction_kernel_le_seed_kernel a hPV h3V))


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking
variable {G : Type*} [Group G] [Finite G]

/-- M₁ = N_{LT}(V₁), the normalizer computed inside LT. -/
def sourcePointStabilizer (L V₁ : Subgroup G) (T : Sylow 2 G) : Subgroup G :=
  (L ⊔ (T : Subgroup G)) ⊓ normalizer (V₁ : Set G)

/-- The notation L₁ = O²(M₁) and Sylow supplementation give M₁ = L₁T. -/
theorem sourcePointStabilizer_eq_join (L L₁ V₁ : Subgroup G) (T : Sylow 2 G)
    (hT : (T : Subgroup G) ≤ normalizer (V₁ : Set G))
    (hL₁ : (pResidual 2 (sourcePointStabilizer L V₁ T)).map
      (sourcePointStabilizer L V₁ T).subtype = L₁) :
    sourcePointStabilizer L V₁ T = L₁ ⊔ (T : Subgroup G) := by
  have hTM : (T : Subgroup G) ≤ sourcePointStabilizer L V₁ T := le_inf le_sup_right hT
  have hs := congrArg (fun X : Subgroup (sourcePointStabilizer L V₁ T) =>
      X.map (sourcePointStabilizer L V₁ T).subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTM))
  rw [Subgroup.map_sup, hL₁, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM,
    ← MonoidHom.range_eq_map, range_subtype] at hs
  exact hs.symm

/-- Notation 13.2.1: the preimage in T of O₂(M̄₁), where the bar is the
actual conjugation action on V. Its image is canonically the quotient by
C_{M₁}(V); no two-group kernel is assumed by this definition. -/
def sourceR1 (L V V₁ : Subgroup G) (T : Sylow 2 G)
    (hT : (T : Subgroup G) ≤ normalizer (V₁ : Set G))
    (hV : L ⊔ (T : Subgroup G) ≤ normalizer (V : Set G)) : Subgroup G :=
  radicalPreimage (sourcePointStabilizer L V₁ T) V T
    (le_inf le_sup_right hT) (inf_le_left.trans hV)

theorem sourceR1_eq_core_of_marking (H L L₁ V V₃ V₁ : Subgroup G) (T : Sylow 2 G)
    [(V₁.subgroupOf V₃).Normal] [IsKleinFour (V₃ ⧸ V₁.subgroupOf V₃)]
    (hT : (T : Subgroup G) ≤ normalizer (V₁ : Set G))
    (hV : L ⊔ (T : Subgroup G) ≤ normalizer (V : Set G))
    (hL₁ : (pResidual 2 (sourcePointStabilizer L V₁ T)).map
      (sourcePointStabilizer L V₁ T).subtype = L₁)
    (hPn : L₁ ⊔ (T : Subgroup G) ≤ normalizer (V₃ : Set G))
    (a : SeedAction V₃ V₁ (L₁ ⊔ (T : Subgroup G)) hPn)
    (h3V : V₃ ≤ V) (hPH : L₁ ⊔ (T : Subgroup G) ≤ H)
    (e : Source.Hstar H ≃* BinaryLinearThree.Group)
    (he : (Source.starImage H (L₁ ⊔ (T : Subgroup G))).map e.toMonoidHom =
      Matrix.PSL3Two.lineParabolicSL) :
    sourceR1 L V V₁ T hT hV = (L₁ ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hM := sourcePointStabilizer_eq_join L L₁ V₁ T hT hL₁
  have hMn : sourcePointStabilizer L V₁ T ≤ normalizer (V₃ : Set G) := hM.symm ▸ hPn
  have aM : SeedAction V₃ V₁ (sourcePointStabilizer L V₁ T) hMn := by
    simpa only [hM] using a
  have hMH : sourcePointStabilizer L V₁ T ≤ H := hM.symm ▸ hPH
  have heM : (Source.starImage H (sourcePointStabilizer L V₁ T)).map e.toMonoidHom =
      Matrix.PSL3Two.lineParabolicSL := by rw [hM]; exact he
  exact (radicalPreimage_eq_core_of_marking T (le_inf le_sup_right hT) aM
    (inf_le_left.trans hV) h3V hMH e heM).trans (congrArg (fun P => P.pCoreIn 2) hM)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking
