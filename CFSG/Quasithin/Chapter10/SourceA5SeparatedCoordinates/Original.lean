module
public import CFSG.Quasithin.Chapter10.SourceA5SeparatedCoordinates.Support
public import CFSG.Quasithin.Chapter10.SourceA5SeparatedCoordinates.Models
public import Theory.Representation.NormalPairSupport.Exchange

/-!
# Homogeneous coordinates on the original separated full quotient

The source-separated seed supplies the actual complementary support spaces and
the original factor exchange. Normal-pair homogeneity then gives equal positive
multiplicity, and the complete binary A₅ classifier marks their common simple
model as natural or deleted. All faithful-actor and quotient diagrams remain
literal. No full/local equality or local irreducibility is used in this step.

Source: Aschbacher--Smith D.3.21 and 3.2.6, printed pp.206 and581.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
local instance separatedOriginalFieldFourAlgebra : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) := ZMod.algebra _ 2
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- Minimality supplies the faithful full-quotient action before the numerical
bound is known. Any eventual source cubic bound applies to this same action. -/
theorem source_minimal_full_quotient_faithful_action (hD : D.IsMinimalFullModule) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    ∃ τ : Representation (ZMod 2) (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))
      (Additive D.fullCentralQuotient),
      Function.Injective τ ∧ τ.IsIrreducible ∧
      (SourceFullModuleCubicBound D → BinaryOffender.cubicRatio τ ≤ 2) ∧
      (∀ (m : D.maximalLocal) (v : D.fullModule),
        τ (q m) (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
          Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
            ⟨(m : G) * (v : G) * (m : G)⁻¹,
              (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule m.property) v).mp
                v.property⟩)) := by
  dsimp only
  let U := D.fullModule.subgroupOf D.maximalLocal
  let := (source_full_module_reduced D).normal
  let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
  obtain ⟨σ,hirr,_,hσ⟩ := source_minimal_full_quotient_action D hD
  obtain ⟨τ,he,hcubic⟩ := source_full_quotient_cubic_bound D σ hσ
  have hτ (m : D.maximalLocal) (v : D.fullModule) :
      τ (q m) (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
        Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
          ⟨(m : G) * (v : G) * (m : G)⁻¹,
            (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule m.property) v).mp
              v.property⟩) := by
    have hm : τ (q m) = σ m := congrArg (fun r => r m) he
    rw [hm]
    exact hσ m v
  refine ⟨τ,source_full_central_quotient_faithful D τ hτ,?_,hcubic,hτ⟩
  apply (irreducible_comp_surjective_iff q (QuotientGroup.mk'_surjective _) τ).mp
  rw [he]
  exact hirr

/-- The actual separated minimal full quotient is the sum of equal positive
numbers of copies of one common four-dimensional natural or deleted A₅ model. -/
theorem source_a5_full_separated_coordinates
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule)
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    ∃ (τ : Representation (ZMod 2) (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))
        (Additive D.fullCentralQuotient))
      (i : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →*
        (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))),
      Function.Injective τ ∧ τ.IsIrreducible ∧
      (SourceFullModuleCubicBound D → BinaryOffender.cubicRatio τ ≤ 2) ∧
      Function.Injective i ∧ i.range.Normal ∧
      IsCompl (NormalPairSupport.left τ i) (NormalPairSupport.right τ i) ∧
      (∀ m,
        ((NormalPairSupport.left τ i).map (τ m) = NormalPairSupport.left τ i ∧
          (NormalPairSupport.right τ i).map (τ m) = NormalPairSupport.right τ i) ∨
        ((NormalPairSupport.left τ i).map (τ m) = NormalPairSupport.right τ i ∧
          (NormalPairSupport.right τ i).map (τ m) = NormalPairSupport.left τ i)) ∧
      ((∃ f : alternatingGroup (Fin 5) ≃* SL(2,OrthogonalFourMinus.FiniteModel.Field 1),
        Nonempty (NormalPairHomogeneous.Coordinates τ i
          (SL2.BinarySmall.natural.comp f.toMonoidHom))) ∨
       Nonempty (NormalPairHomogeneous.Coordinates τ i BinaryPermutation.FiveTensorSquare.δ)) ∧
      (∀ x y, q ⟨t,le_normalizer_componentOrbit L T ht⟩ * i (x,y) *
        (q ⟨t,le_normalizer_componentOrbit L T ht⟩)⁻¹ =
          i (originalA5ConjugationTwist D e hn ht y,x)) ∧
      (∀ x : localOrbit T L,
        i (originalA5ProductProjection D e hn ht htn x) =
          q (inclusion (localOrbit T L).le_normalizer x)) ∧
      (∀ (m : D.maximalLocal) (v : D.fullModule),
        τ (q m) (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
          Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
            ⟨(m : G) * (v : G) * (m : G)⁻¹,
              (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule m.property) v).mp
                v.property⟩)) := by
  dsimp only
  let := (source_full_module_reduced D).normal
  obtain ⟨τ,hfaith,hτirr,hcubic,hτ⟩ := source_minimal_full_quotient_faithful_action D hD
  obtain ⟨i,hi,hnorm,hdiag⟩ := source_a5_original_product_embedding D e hn ht htn
  have hs := source_separated_full_support_nonzero D e hn ht htn hsep τ i hdiag hτ
  have hexchange := source_original_full_pair_exchange D e hn ht htn i hdiag
  let : i.range.Normal := hnorm
  let : τ.IsIrreducible := hτirr
  let g := QuotientGroup.mk'
    (centralizer (D.fullModule.subgroupOf D.maximalLocal : Set D.maximalLocal))
    ⟨t,le_normalizer_componentOrbit L T ht⟩
  let α := originalA5ConjugationTwist D e hn ht
  let β : MulAut (alternatingGroup (Fin 5)) := MulEquiv.refl _
  have he : ∀ x y, g * i (x,y) * g⁻¹ = i (α y,β x) := hexchange
  have hleft := NormalPairSupport.left_ne_bot_of_exchange τ i g α β he hs
  let E := NormalPairSupport.exchangeEquiv τ i g α β he
  have hmodels := source_a5_separated_model_coordinates τ i hi hfaith hleft E
  have hZ : center (alternatingGroup (Fin 5)) = ⊥ := alternatingGroup.center_eq_bot (by simp)
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup }
  exact ⟨τ,i,hfaith,hτirr,hcubic,hi,hnorm,
    NormalPairSupport.support_isCompl τ i hi hZ hfaith hs,
    NormalPairSupport.support_map_eq_or_exchanged τ i hi hZ,
    hmodels,hexchange,hdiag,hτ⟩

end CFSG.Quasithin.Chapter10
