module
public import CFSG.Quasithin.Chapter10.SourceA5SeparatedCoordinates.Original
public import CFSG.Quasithin.Chapter10.SourceA5SeparatedCoordinates.NormalizedModels

/-!
# Fixed model coordinates for the original separated full quotient

The literal minimal full quotient is identified with equal positive numbers of
copies of the fixed natural or deleted model used by the multiplicity-centralizer
consumer. The original faithful actor, normal pair embedding, full-actor support
permutation, Sylow exchange, and quotient diagrams are retained. A later source
cubic bound applies to the same chosen representation.

Source: Aschbacher--Smith D.3.21 and 3.2.6, printed pp.206 and581.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Representation.AlternatingFiveMovedPair
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The actual separated minimal full quotient is the sum of equal positive
numbers of copies of one common four-dimensional natural or deleted A₅ model. -/
theorem source_a5_full_separated_normalized_coordinates
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
      ((∃ n : ℕ, 0 < n ∧
        ∃ c : Additive D.fullCentralQuotient ≃ₗ[ZMod 2]
            ((Fin n → SeparatedCentralizer.Natural) × (Fin n → SeparatedCentralizer.Natural)),
          ∀ d v, c (τ (i d) v) =
            (fun j => SeparatedCentralizer.natural d.1 ((c v).1 j),
             fun j => SeparatedCentralizer.natural d.2 ((c v).2 j))) ∨
       (∃ n : ℕ, 0 < n ∧
        ∃ c : Additive D.fullCentralQuotient ≃ₗ[ZMod 2]
            ((Fin n → SeparatedCentralizer.Deleted) × (Fin n → SeparatedCentralizer.Deleted)),
          ∀ d v, c (τ (i d) v) =
            (fun j => SeparatedCentralizer.deleted d.1 ((c v).1 j),
             fun j => SeparatedCentralizer.deleted d.2 ((c v).2 j)))) ∧
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
  obtain ⟨τ,i,hfaith,hτirr,hcubic,hi,hnorm,hcompl,hperm,_,hexchange,hdiag,hτ⟩ :=
    source_a5_full_separated_coordinates D e hn ht htn hD hsep
  let : i.range.Normal := hnorm
  let : τ.IsIrreducible := hτirr
  let g := QuotientGroup.mk'
    (centralizer (D.fullModule.subgroupOf D.maximalLocal : Set D.maximalLocal))
    ⟨t,le_normalizer_componentOrbit L T ht⟩
  let α := originalA5ConjugationTwist D e hn ht
  let β : MulAut (alternatingGroup (Fin 5)) := MulEquiv.refl _
  have he : ∀ x y, g * i (x,y) * g⁻¹ = i (α y,β x) := hexchange
  have hs := source_separated_full_support_nonzero D e hn ht htn hsep τ i hdiag hτ
  have hleft := NormalPairSupport.left_ne_bot_of_exchange τ i g α β he hs
  let E := NormalPairSupport.exchangeEquiv τ i g α β he
  have hmodels := source_a5_separated_normalized_coordinates τ i hi hfaith hleft E
  exact ⟨τ,i,hfaith,hτirr,hcubic,hi,hnorm,hcompl,hperm,hmodels,hexchange,hdiag,hτ⟩

end CFSG.Quasithin.Chapter10
