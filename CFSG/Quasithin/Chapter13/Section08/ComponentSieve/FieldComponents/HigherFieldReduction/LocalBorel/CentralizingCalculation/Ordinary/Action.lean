module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.TwoKernels

/-!
# The ordinary product action on the actual A₆ quotient

Conjugation on L/O₂(L), transported through the given ordinary model,
has exactly the literal Borel centralizer as its kernel. If its image is
covered by the image of L₁, two-perfectness and relative normality give
J = B_C L₁. The model-image premise is isolated explicitly for the concrete
point-residual normalizer calculation; it is not a new SourceContext field.

Source: Aschbacher–Smith 13.7.3(9), p.936, and the proof of 13.8.20,
printed p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
namespace Ordinary.Action
universe u v
variable {G : Type u} [Group G]

/-- Conjugation on the intrinsic quotient, restricted to a local overgroup. -/
def quotientAction (J L : Subgroup G) (hJL : J ≤ normalizer (L : Set G)) :
    J →* MulAut (L ⧸ pCore 2 L) :=
  (coreAction L).comp (inclusion hJL)

/-- The action kernel is exactly the literal quotient centralizer. -/
theorem quotientAction_kernel (J L : Subgroup G)
    (hJL : J ≤ normalizer (L : Set G)) :
    (quotientAction J L hJL).ker.map J.subtype =
      commutatorPreimage J L (L.pCoreIn 2) := by
  apply le_antisymm
  · apply le_commutatorPreimage (map_subtype_le _)
    apply commutator_le.mpr
    rintro _ ⟨x, hx, rfl⟩ l hl
    have he : coreAction L ⟨x.val, hJL x.property⟩ = 1 := hx
    have hc := (coreAction_eq_one_iff _ _).mp he ⟨l, hl⟩
    exact ⟨_, hc, rfl⟩
  · intro x hx
    have hxJ := commutatorPreimage_le J L (L.pCoreIn 2) hx
    refine ⟨⟨x, hxJ⟩, ?_, rfl⟩
    change coreAction L ⟨x, hJL hxJ⟩ = 1
    apply (coreAction_eq_one_iff _ _).mpr
    intro l
    have hc := commutator_commutatorPreimage_le J L (L.pCoreIn 2)
      (hJL.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
      (commutator_mem_commutator hx l.property)
    obtain ⟨y, hy, he⟩ := hc
    have he' : y = L.normalizerMonoidHom ⟨x, hJL hxJ⟩ l * l⁻¹ := Subtype.ext he
    exact he' ▸ hy

variable [Finite G]

variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)
  (a : ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.NaturalSetup
    L (T : Subgroup G) V V₁)

/-- The local action, transported through the genuine ordinary quotient isomorphism. -/
noncomputable def modelAction :
    (d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G) →*
      MulAut (alternatingGroup (Fin 6)) :=
  (MulAut.congr a.model).toMonoidHom.comp
    (quotientAction _ L d.product_normalizes_L)

/-- The transported action has precisely the source Borel-centralizer kernel. -/
theorem modelAction_kernel :
    (modelAction d a).ker.map (d.B ⊔ one L (T : Subgroup G) V₁).subtype =
      borelCentralizer d.B (one L (T : Subgroup G) V₁) L := by
  have he : (modelAction d a).ker =
      (quotientAction _ L d.product_normalizes_L).ker := by
    ext x
    change MulAut.congr a.model (quotientAction _ L d.product_normalizes_L x) = 1 ↔ _
    rw [map_eq_one_iff _ (MulAut.congr a.model).injective]
    rfl
  rw [he]
  exact quotientAction_kernel _ L d.product_normalizes_L

/-- Covering the concrete action by L₁ gives the source product factorization.
The model normalizer calculation, rather than a centralizer factorization,
is the explicit premise of this reduction. -/
theorem product_eq_of_action_image
    (himage : ∀ g : (d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G),
      ∃ l : one L (T : Subgroup G) V₁,
        modelAction d a g = modelAction d a (inclusion le_sup_right l)) :
    d.B ⊔ one L (T : Subgroup G) V₁ =
      centralizingResidual d.B (one L (T : Subgroup G) V₁) L ⊔
        one L (T : Subgroup G) V₁ := by
  classical
  let J := d.B ⊔ one L (T : Subgroup G) V₁
  let I := borelCentralizer d.B (one L (T : Subgroup G) V₁) L
  let N := (one L (T : Subgroup G) V₁).subgroupOf J
  have hi : I ≤ J := commutatorPreimage_le _ _ _
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
    (TwoKernels.product_normalizes_one d)
  have hcover : (J : Set G) ⊆ (I : Set G) * (N.map J.subtype : Set G) := by
    intro x hx
    obtain ⟨l, hl⟩ := himage ⟨x, hx⟩
    let y : J := ⟨x, hx⟩ * (inclusion le_sup_right l)⁻¹
    have hy : y ∈ (modelAction d a).ker := by
      change modelAction d a y = 1
      dsimp only [y]
      rw [map_mul, map_inv, hl, mul_inv_cancel]
    have hyI : y.val ∈ I := by
      change y.val ∈ borelCentralizer d.B (one L (T : Subgroup G) V₁) L
      rw [← modelAction_kernel d a]
      exact mem_map_of_mem J.subtype hy
    refine Set.mem_mul.mpr ⟨y.val, hyI, l.val, ?_, ?_⟩
    · exact ⟨inclusion le_sup_right l, l.property, rfl⟩
    · change (x * l.val⁻¹) * l.val = x
      group
  have hs := eq_mul_embedded_pResidual_of_cover 2 J I N (TwoKernels.product_isPPerfect d) hcover
  rw [inf_eq_right.mpr hi, map_subgroupOf_eq_of_le (show one L (T : Subgroup G) V₁ ≤ J from le_sup_right)] at hs
  apply le_antisymm
  · intro x hx
    change x ∈ (J : Set G) at hx
    rw [hs] at hx
    obtain ⟨c, hc, l, hl, rfl⟩ := Set.mem_mul.mp hx
    exact mul_mem_sup hc hl
  · exact sup_le (centralizingResidual_le _ _ _) le_sup_right


end Ordinary.Action
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation
