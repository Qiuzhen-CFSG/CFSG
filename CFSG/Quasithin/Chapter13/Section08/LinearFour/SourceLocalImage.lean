module
public import Theory.Representation.BinaryConjugationSection.PlaneCentralResidual
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefAccounting
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceMaximalChief
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.CubicOrders

/-!
# The original central residual's matrix image

The natural A₆ action makes L₀ centralize V, and hence the marked V₃/V₁
plane. Its covered quotient has center of order three, so L₀ is not a
two-group. The proved original seed-normalizer bound supplies relative
normality through the unchanged natural matrix quotient. The plane-residual
recognition theorem therefore identifies its exact image as 2⁴:3.

The terminal application removes the separate matrix-image hypothesis from
SourceChiefAccounting. The nine-factor bound, compatible extra-line movement
and the earlier source inputs remain obligations of the original assembly;
this conditional consumer does not establish Theorem 13.8.28.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
Notation 13.2.1, printed p.877, and 13.8.29--31, printed pp.964--965.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open Subgroup Representation
open BinaryParabolicExteriorSquare PlaneSpan
open BinaryLinear.FlagCoordinates
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]

/-- The central residual is not a two-group, from the actual covered quotient. -/
theorem source_zero_not_two_of_cover (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) :
    ¬ IsPGroup 2 (zero L) := by
  intro hp
  have hq := hp.comap_subtype.map
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
  change IsPGroup 2 (((zero L).subgroupOf L).map
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) at hq
  rw [source_zero_cover_image L e] at hq
  have hh := hq.card_eq_or_dvd
  rw [Representation.Hexacode.even_center_card] at hh
  norm_num at hh


variable {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The original seed normalizer and covered quotient identify the exact L₀ image.
No matrix-image, radical-image or cubic-placement premise is added. -/
theorem source_zero_matrix_image_from_original_seed
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hab : IsMulCommutative (conjugateSpanBy V G₁))
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (hDH : zero L ≤ H)
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = (Source.QH H).subgroupOf H)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hplane : d.imageSpace V₃ = plane) :
    ((zero L).subgroupOf H).map π = PlaneRadical.complementLocal := by
  let ds := s.toLocalSetup hab
  have hzV : zero L ≤ centralizer (V:Set G) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := residual_le (ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.centralPreimage L) hx
    change y ∈ centralCore L at hy
    rw [ds.centralCore_eq_centralizer] at hy
    exact hy
  have hn : H ⊓ normalizer (V₃:Set G) ≤ normalizer (zero L : Set G) :=
    (source_seed_normalizer_le_LT s h hH hcentral ρ d π hker hnatural).trans
      ((sup_le L.le_normalizer s.normalizes_L).trans (normalizer_le_zero_normalizer L))
  exact BinaryConjugationSection.complement_image_of_plane_centralizer H (zero L) (Source.UH H V₃) V₁ V₃
    (Source.QH H) hDH (isPPerfect_embedded_pResidual 2 (ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.centralPreimage L))
    (source_zero_not_two_of_cover L eL) (hzV.trans (centralizer_le s.seed_le)) hn
    ρ d π hker (isPGroup_pCoreIn 2 H) honto hnatural
    (s.line_le_plane.trans s.plane_le_seed) (le_conjugateSpanBy _ _) hplane

end CFSG.Quasithin.Chapter13.Section08.LinearFour

namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open BinaryLinear.OuterCyclic CriticalGeometry
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open BinaryParabolicExteriorSquare SingularPresentation
open PlaneSpan (pointSpace firstSpace planeSpace)
open BinaryLinear.FlagCoordinates
open Theory.LinearAlgebra BinaryFivePointStabilizer
open NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]
variable {K U : Type*} [Group K]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The covered quotient supplies the exact local matrix image in the terminal
consumer. The nine-factor lower bound remains an explicit source obligation. -/
theorem source_linear_four_exclusion_from_original_cover_nine_factors
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
    (hgenerate : L ⊔ (T:Subgroup G) ≤ H ⊔ zpowers (g:G))
    (hF : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T:Subgroup G) H V) (hb : 3 ≤ c.path.length)
    (Kc : Subgroup G) (hKcH : Kc ≤ H) (hKc : IsPPerfect 2 Kc)
    (hseedQ : ⁅V₃,Source.QH H⁆ ≠ ⊥)
    (hseed : ⁅centralizer (V₃:Set G),V⁆ ≤ V₁)
    (hcaseone : (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃ ∨
        Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃) →
      c.Aone V₁ ≤ Source.UH H V₃ ∧ ¬ c.Vgamma ≤ Source.QH H)
    (hDK : zero L ≤ Kc)
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hnine : ∀ t : ChiefSeries (zero L), t.head = ⊥ → t.last = ⊤ →
      9 ≤ t.noncentralTwoCount)
    (Q R : Subgroup G) (hQR : Source.QH H ≤ R) (hindex : Q.relIndex R = 4)
    (hcent : Q ⊓ Source.QH H ≤ centralizer (V₃:Set G))
    (hQV : Q ≤ centralizer (V:Set G))
    (hcover : IsSQTK KnownSimple.IsKnownSimple H)
    (hKonto : Function.Surjective
      ((QuotientGroup.mk' (pCore 2 H)).comp (Kc.subgroupOf H).subtype)) : False := by
  have hlocal := source_zero_matrix_image_from_original_seed s hab h hH hcentral
    (hDK.trans hKcH) eL ρ d π₄ hker honto hnatural hplane
  exact source_linear_four_exclusion_from_original_nine_factors
    s hab h hH hcentral hHeq A L2 hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK
    eI hAcore hALT hVA hAG hπI hgen hdim g hg ρ d π₄ hker honto hnatural
    hpoint hplane eU hcoords hUcard hu hgenerate hF c hb Kc hKcH hKc
    hseedQ hseed hcaseone hDK hlocal hnine Q R hQR hindex hcent hQV hcover hKonto

end CFSG.Quasithin.Chapter13.Section08.LinearFour
