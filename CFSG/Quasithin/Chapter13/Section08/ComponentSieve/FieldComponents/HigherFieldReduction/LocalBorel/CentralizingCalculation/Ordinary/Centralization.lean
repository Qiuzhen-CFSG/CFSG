module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.TwoKernels
public import Theory.Representation.BinaryPermutationMulAction
/-!
# Centralization of the entire source natural module

The source identity H ∩ M = N_H(V) makes BL₁ normalize V. Conjugation
by C commutes on V with the full L-action, since [C,L] lies in O₂(L)
and this core centralizes V. Transport by the standing coordinate
isomorphism therefore puts the C-action in the centralizer of natural A₆.
Its intrinsic trivial-centralizer theorem then gives actual centralization
of V, with no assertion merely about a quotient of V.

The exact intrinsic natural-action centralizer fact is explicit here;
the independent model-normalizer task supplies it for final assembly.
Source: Aschbacher–Smith 13.7.3(9), p.936, and 13.8.20, p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.Centralization
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u v
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)

/-- The source intersection identity makes the full product normalize V. -/
theorem product_normalizes_V : d.B ⊔ one L (T : Subgroup G) V₁ ≤ normalizer (V : Set G) := by
  have hj : d.B ⊔ one L (T : Subgroup G) V₁ ≤ H ⊓ M :=
    le_inf (sup_le ((borel_le_component _ _ _ _ _).trans d.component_le) d.one_le_H)
      (sup_le d.borel_in_M d.one_le_M)
  rw [d.intersection] at hj
  exact hj.trans inf_le_right

include d in
private theorem core_centralizes_V : L.pCoreIn 2 ≤ centralizer (V : Set G) := by
  rintro _ ⟨l, hl, rfl⟩
  change l ∈ (centralizer (V : Set G)).subgroupOf L
  rw [← d.standing.centralCore_eq_centralizer]
  change QuotientGroup.mk' (pCore 2 L) l ∈ center (L ⧸ pCore 2 L)
  have hq : QuotientGroup.mk' (pCore 2 L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
  rw [hq]
  exact one_mem _

private noncomputable def coordinateAction : normalizer (V : Set G) →*
    MulAut (Multiplicative (BinaryPermutation.natural (Fin 6))) :=
  (MulAut.congr d.standing.coordinate).toMonoidHom.comp V.normalizerMonoidHom

private theorem coordinateAction_L (l : L) :
    coordinateAction d ⟨l.val, d.standing.normalizes_V (mem_sup_left l.property)⟩ =
      BinaryPermutation.naturalMulAction (Fin 6)
        (d.standing.local_quotient
          (QuotientGroup.mk' (TransvectionRecognition.Component.ModelExtension.centralCore L) l)).val := by
  apply MulEquiv.ext
  intro w
  obtain ⟨v, rfl⟩ := d.standing.coordinate.surjective w
  change d.standing.coordinate (V.normalizerMonoidHom _
    (d.standing.coordinate.symm (d.standing.coordinate v))) = _
  rw [d.standing.coordinate.symm_apply_apply]
  exact d.standing.conjugation l v

private theorem coordinateAction_eq_one_iff (x : normalizer (V : Set G)) :
    coordinateAction d x = 1 ↔ x.val ∈ centralizer (V : Set G) := by
  change MulAut.congr d.standing.coordinate (V.normalizerMonoidHom x) = 1 ↔ _
  rw [map_eq_one_iff _ (MulAut.congr d.standing.coordinate).injective]
  change x ∈ V.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

/-- The literal centralizing residual centralizes all V after the intrinsic model calculation. -/
theorem centralizingResidual_le_of_natural_centralizer
    (hnat : centralizer ((alternatingGroup (Fin 6)).map
      (BinaryPermutation.naturalMulAction (Fin 6)) :
        Set (MulAut (Multiplicative (BinaryPermutation.natural (Fin 6))))) = ⊥) :
    centralizingResidual d.B (one L (T : Subgroup G) V₁) L ≤
      M ⊓ centralizer (V : Set G) := by
  refine le_inf (centralizingResidual_le_M _ _ _ _ d.borel_in_M d.one_le_M) ?_
  intro c hc
  have hcV := product_normalizes_V d (centralizingResidual_le _ _ _ hc)
  let x : normalizer (V : Set G) := ⟨c, hcV⟩
  apply (coordinateAction_eq_one_iff d x).mp
  have hm : coordinateAction d x ∈ centralizer ((alternatingGroup (Fin 6)).map
      (BinaryPermutation.naturalMulAction (Fin 6)) :
        Set (MulAut (Multiplicative (BinaryPermutation.natural (Fin 6))))) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨q, hq⟩ := d.standing.local_quotient.surjective ⟨s, hs⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective
      (TransvectionRecognition.Component.ModelExtension.centralCore L) q
    let y : normalizer (V : Set G) :=
      ⟨l.val, d.standing.normalizes_V (mem_sup_left l.property)⟩
    have hy := coordinateAction_L d l
    rw [hq] at hy
    change coordinateAction d y = BinaryPermutation.naturalMulAction (Fin 6) s at hy
    rw [← hy]
    suffices hcomm : ⁅coordinateAction d x, coordinateAction d y⁆ = 1 by
      exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm
    rw [← map_commutatorElement]
    apply (coordinateAction_eq_one_iff d _).mpr
    exact core_centralizes_V d
      (centralizingResidual_commutator_le d.B (one L (T : Subgroup G) V₁) L
        (d.product_normalizes_L.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
          (commutator_mem_commutator hc l.property))
  rw [hnat] at hm
  exact hm
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.Centralization
