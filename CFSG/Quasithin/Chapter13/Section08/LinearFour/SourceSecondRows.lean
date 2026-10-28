module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSecondKernel
public import Theory.Representation.TransitiveSeedCover.Rows

/-!
# Both full second tensor rows on the original quotient

The invariant-kernel dichotomy now identifies the literal V₀/U₀ with either
(dual U_H/V₂) tensor (V/V₂), or (dual U_H/V₂) tensor (V/V₂ plus a trivial line).
The natural plane is marked by an actual BinaryConjugationSection of V/V₂
using the original I₂ quotient homomorphism. The tensor equivalence uses the
same full G₂ quotient action and maps the exact first slice to V_H/U₀.
The original g still sends its first natural vector to the second.

No tensor-row or kernel hypothesis is added to the original seed inputs.
The subsequent extra-line movement, critical intersections and chief-factor
obstruction remain with the same source-theorem owner; this is not the final
13.8.28 contradiction.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.29(4), printed p.964.
-/

public noncomputable section
open Subgroup Representation
open scoped TensorProduct
open QuadraticFourGroup.TensorClassification
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open scoped MatrixGroups IsMulCommutative
open CyclicSeedTensor
open SourceCompletion TransvectionRecognition.Component.ModelExtension BinaryPermutation
open BinaryLinear.OuterCyclic
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open BinaryParabolicExteriorSquare SingularPresentation
open PlaneSpan (pointSpace firstSpace planeSpace)
open BinaryLinear.FlagCoordinates
open Theory.LinearAlgebra BinaryFivePointStabilizer
variable {G K U W : Type*} [Group G] [Finite G] [Group K]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  [AddCommGroup W] [Module (ZMod 2) W]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- Construct both full tensor alternatives on the canonical second quotient,
with the literal natural seed, both actor maps and the same original conjugator. -/
theorem source_second_tensor_rows_from_original_seed
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hab : IsMulCommutative (conjugateSpanBy V G₁))
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (hHeq : H = normalizer (V₁:Set G))
    (A L2 : Subgroup G)
    (hK : ((K2 H V₂).subgroupOf (G2 V₂)).Normal)
    (hG : G2 V₂ = K2 H V₂ ⊔ L2 ⊔ (T:Subgroup G))
    (hV : L2 ⊔ (T:Subgroup G) ≤ normalizer (V:Set G))
    (π : G2 V₂ →* K × Equiv.Perm (Fin 3)) (hπ : Function.Surjective π)
    (hπker : π.ker = pCore 2 (G2 V₂)) (hcore : Q2 V₂ ≤ H)
    (σ : Representation (ZMod 2) K U)
    (κ : ↥(H ⊓ G2 V₂) →* K)
    (dU : BinaryConjugationSection (H ⊓ G2 V₂) (Source.UH H V₃) V₂ (σ.comp κ))
    (hκker : κ.ker = pCore 2 ↥(H ⊓ G2 V₂))
    (hκ : Function.Surjective (κ.comp (inclusion (K2_le_localNormalizer H V₂))))
    (hπK : ∀ k : K2 H V₂,
      π (inclusion ((K2_le_localNormalizer H V₂).trans inf_le_right) k) =
        (κ (inclusion (K2_le_localNormalizer H V₂) k),1))
    (eI : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (hAcore : A.pCoreIn 2 = A ⊓ centralizer (V₂:Set G))
    (hQA : H.pCoreIn 2 ≤ A) (hnA : G2 V₂ ≤ normalizer A)
    (hALT : A ≤ L ⊔ (T:Subgroup G)) (hVA : V ≤ A) (hAG : A ≤ G2 V₂)
    (hπI : ∀ a : A, π (inclusion hAG a) = (1,eI (QuotientGroup.mk' (pCore 2 A) a)))
    (hgen : Source.UH H V₃ = conjugateSpanBy V₃ (K2 H V₂))
    (hdim : Module.finrank (ZMod 2) U = 3)
    (g : A) (hg : (g:G) ∉ H)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π₄ : H →* SL(4,ZMod 2))
    (hker : π₄.ker = (Source.QH H).subgroupOf H)
    (honto : Function.Surjective π₄)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π₄ h).val w)
    (hpoint : d.imageSpace V₂ = Submodule.span (ZMod 2) {Pi.single 0 1})
    (hplane : d.imageSpace V₃ = plane)
    (eU : QuotientSpace (Pi.single 0 1 : Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U)
    (hcoords : ∀ u : Source.UH H V₃, (dU.coordinates u).toAdd =
      eU ((line (Pi.single 0 1)).mkQ (d.coordinates u).toAdd))
    (hUcard : Nat.card (Source.UH H V₃) = 32)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T:Subgroup G) ≤ N → N = M)
    (hgenerate : L ⊔ (T:Subgroup G) ≤ H ⊔ zpowers (g:G)) :
    ∃ hn : ((U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂)).Normal,
      let := hn
      ∃ he : IsElementaryAbelian 2
          (V0 (Source.VH H V) V₂ ⧸ (U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂)),
        let := he
        ∃ (e : Equiv.Perm (Fin 3) ≃* LinearGroup 2)
          (τ : Representation (ZMod 2) (K × Equiv.Perm (Fin 3))
          (Additive (V0 (Source.VH H V) V₂ ⧸
            (U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂))))
          (q : BinaryConjugationSection (G2 V₂) (V0 (Source.VH H V) V₂)
            (U0 (Source.UH H V₃) V₂) (τ.comp π)),
          (∃ cV : BinaryConjugationSection A V V₂
            ((LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp e.toMonoidHom).comp
              (eI.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A)))),
            cV.imageSpace V₃ = Submodule.span (ZMod 2) {first}) ∧
          (∀ v : V0 (Source.VH H V) V₂, (q.coordinates v).toAdd =
            Additive.ofMul (QuotientGroup.mk'
              ((U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂)) v)) ∧
          (∃ f : σ.dual.IntertwiningMap (τ.comp (MonoidHom.inl K (Equiv.Perm (Fin 3)))),
            Function.Injective f ∧ f.range.toSubmodule = q.imageSpace (Source.VH H V) ∧
            ((∃ E : (externalTensor σ.dual
                (TransitiveSeedCover.planeNatural e.toMonoidHom)).Equiv τ,
              ∀ u, E (u ⊗ₜ[ZMod 2] first) = f u) ∨
             (∃ E : (externalTensor σ.dual
                ((TransitiveSeedCover.planeNatural e.toMonoidHom).prod
                  (Representation.trivial (ZMod 2) (Equiv.Perm (Fin 3)) (ZMod 2)))).Equiv τ,
              ∀ u, E (u ⊗ₜ[ZMod 2] (first,(1 : ZMod 2))) = f u))) ∧
          Module.finrank (ZMod 2) (Additive (V0 (Source.VH H V) V₂ ⧸
            (U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂))) ≤ 9 ∧
          Module.finrank (ZMod 2) (q.imageSpace (Source.VH H V)) = 3 ∧
          Disjoint (q.imageSpace (Source.VH H V))
            ((q.imageSpace (Source.VH H V)).map (τ (π (inclusion hAG g)⁻¹))) ∧
          (⨆ a : G2 V₂, (q.imageSpace (Source.VH H V)).map (τ (π a))) = ⊤ ∧
          (∀ i, e i first = first → ∀ w ∈ q.imageSpace (Source.VH H V), τ (1,i) w = w) ∧
          e (eI (QuotientGroup.mk' (pCore 2 A) g⁻¹)) first = second ∧
          ∀ B : Subgroup G, U0 (Source.UH H V₃) V₂ ≤ B → B ≤ Source.VH H V →
            K2 H V₂ ≤ normalizer B → B = U0 (Source.UH H V₃) V₂ ∨ B = Source.VH H V := by
  obtain ⟨hn,he,e,τ,q,hseed,hq,⟨f,hf,hr,F,hF,hkerF,hmark⟩,hbound,hd,hdis,hspan,hfix,ha,hmin⟩ :=
    source_second_kernel_from_original_seed s hab h hH hcentral hHeq A L2 hK hG hV
      π hπ hπker hcore σ κ dU hκker hκ hπK eI hAcore hQA hnA hALT hVA hAG hπI
      hgen hdim g hg ρ d π₄ hker honto hnatural hpoint hplane eU hcoords hUcard hu hgenerate
  let := hn
  let := he
  refine ⟨hn,he,e,τ,q,hseed,hq,⟨f,hf,hr,?_⟩,hbound,hd,hdis,hspan,hfix,ha,hmin⟩
  rcases hkerF with hzero | hconstant
  · right
    obtain ⟨E,hE⟩ := TransitiveSeedCover.extra_row_of_kernel e.toMonoidHom σ.dual τ F hF hzero
    exact ⟨E,fun u => (hE u TransitiveSeedCover.basePoint).trans (hmark u)⟩
  · left
    obtain ⟨E,hE⟩ := TransitiveSeedCover.natural_row_of_kernel e.toMonoidHom σ.dual τ F hF hconstant
    exact ⟨E,fun u => (hE u TransitiveSeedCover.basePoint).trans (hmark u)⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour
