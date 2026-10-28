module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.SemisimpleSpan
public import Theory.Representation.NormalSpanConstituents
/-!
# Constituent types on the original terminal central section

The original V₃ seeds generate U_H/V₁ under H, including after scalar
extension. If every seed is a sum of images of the trivial line and one
conjugation-invariant irreducible D-module, these two type spans fill the
restriction to D. Semisimplicity then identifies every simple constituent.

For the normal Suzuki component the seed maps are the actual ovoid orbit
maps, and the second model is the marked Steinberg representation pulled
through the literal component quotient. Those independent model inputs are
kept explicit here. Source: Aschbacher--Smith, 13.6, printed p.918.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped TensorProduct IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio
open Section08
variable {G : Type*} [Group G] {H V₃ V₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  (hn : H ≤ normalizer (V₁ : Set G))
  (K : Type*) [Field K] [Algebra (ZMod 2) K]
local instance sourceSpanCommGroup : CommGroup (Source.UH H V₃) := inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- The two allowed model types span the literal extended source quotient. -/
theorem extendScalars_typeSpan_sup_eq_top
    (D : Subgroup H) [D.Normal]
    {W : Type*} [AddCommGroup W] [Module K W]
    (τ : Representation K D W)
    (ht : ∀ x : H, Nonempty ((conjugateRep (G := H) τ x).Equiv τ))
    (hseed : ∀ v : V₃,
      ∃ f₀ : (trivial K D K).IntertwiningMap
        ((extendScalars K (representation H V₃ V₁ hn)).comp D.subtype),
      ∃ f₁ : τ.IntertwiningMap
        ((extendScalars K (representation H V₃ V₁ hn)).comp D.subtype),
      (1 : K) ⊗ₜ[ZMod 2] seedVector (H := H) (V₁ := V₁) v ∈ f₀.range ⊔ f₁.range) :
    typeSpan ((extendScalars K (representation H V₃ V₁ hn)).comp D.subtype) (trivial K D K) ⊔
      typeSpan ((extendScalars K (representation H V₃ V₁ hn)).comp D.subtype) τ = ⊤ := by
  apply typeSpan_sup_eq_top_of_seed _ D (trivial K D K) τ
    (conjugate_trivial_equiv D) ht
    (fun v : V₃ => (1 : K) ⊗ₜ[ZMod 2] seedVector (H := H) (V₁ := V₁) v)
  · intro v
    obtain ⟨f₀,f₁,hv⟩ := hseed v
    have hle : f₀.range ⊔ f₁.range ≤
        typeSpan _ (trivial K D K) ⊔ typeSpan _ τ :=
      sup_le_sup (le_iSup _ f₀) (le_iSup _ f₁)
    exact hle hv
  · exact extendScalars_eq_top_of_seed_mem hn K

set_option backward.isDefEq.respectTransparency false in
/-- Every simple source constituent is trivial or the supplied invariant model. -/
theorem extendScalars_constituent_of_seed_ranges
    (D : Subgroup H) [D.Normal]
    {W : Type*} [AddCommGroup W] [Module K W]
    (τ : Representation K D W) [τ.IsIrreducible]
    [IsSemisimpleModule K[D] (Representation.asModule
      ((extendScalars K (representation H V₃ V₁ hn)).comp D.subtype))]
    (ht : ∀ x : H, Nonempty ((conjugateRep (G := H) τ x).Equiv τ))
    (hseed : ∀ v : V₃,
      ∃ f₀ : (trivial K D K).IntertwiningMap
        ((extendScalars K (representation H V₃ V₁ hn)).comp D.subtype),
      ∃ f₁ : τ.IntertwiningMap
        ((extendScalars K (representation H V₃ V₁ hn)).comp D.subtype),
      (1 : K) ⊗ₜ[ZMod 2] seedVector (H := H) (V₁ := V₁) v ∈ f₀.range ⊔ f₁.range)
    (J : Subrepresentation
      ((extendScalars K (representation H V₃ V₁ hn)).comp D.subtype))
    (hJ : IsAtom J) :
    Nonempty (J.toRepresentation.Equiv (trivial K D K)) ∨
      Nonempty (J.toRepresentation.Equiv τ) := by
  let := trivial_line_irreducible (k := K) (G := D)
  exact constituent_of_typeSpan_sup_eq_top _ _ _
    (extendScalars_typeSpan_sup_eq_top hn K D τ ht hseed) J hJ
end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio
