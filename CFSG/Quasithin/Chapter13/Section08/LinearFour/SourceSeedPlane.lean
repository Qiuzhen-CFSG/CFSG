module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceNaturalFlag
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSeedNormalizer
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.ResidualSpan
public import Theory.Representation.BinaryParabolicExteriorSquare.MarkedCubic

/-!
# Original seed actors for the exterior span

The flag marking identifies N_H(V₃) with the natural plane stabilizer.
Lift its plane cubic through the two-group action kernel to an actual
order-three element. Original 13.7.5's theta bound places this element
in L₁. Every element of that same L₁ preserves the marked plane.

These actors discharge the block and cubic premises of the exterior
five-space calculation, giving the literal index 64 over V. In the
maximal quotient, the existing generation and degree argument then gives
field dimension three and the exact kernel V. The original natural and
exterior quotient maps are used throughout. The final constructor obtains
the natural flag and this cubic from the F.9 action and source orders.

Compatible exterior/tensor markings, extra-line movement and the full
13.8.31 obstruction remain obligations of the linear-four owner; these
results do not establish 13.8.28. Earlier 13.8.27 and final source assembly
retain their existing owners. Source: Aschbacher--Smith, The Classification
of Quasithin Groups, 13.7.5(3),13.8.29--30, printed pp.938,964.
-/

public noncomputable section



open Subgroup Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open SourceCompletion BinaryLinear.OuterCyclic BinaryLinear.FlagCoordinates
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Representation.BinaryParabolicExteriorSquare.PlaneSpan
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H V V₁ V₂ V₃ M G₁ : Subgroup G}

/-- The original theta bound supplies an actual cubic in L₁ with the marked
plane matrix, while every element of L₁ preserves the same natural plane. -/
theorem source_seed_plane_actors
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π : H →* SL(4,ZMod 2)) (hker : IsPGroup 2 π.ker)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hplane : d.imageSpace V₃ = plane)
    (h1H : sourceOne L T V₁ ≤ H) :
    (∀ a : sourceOne L T V₁, (π (inclusion h1H a)).val 2 0 = 0 ∧
      (π (inclusion h1H a)).val 2 1 = 0 ∧
      (π (inclusion h1H a)).val 3 0 = 0 ∧
      (π (inclusion h1H a)).val 3 1 = 0) ∧
    ∃ a : sourceOne L T V₁, orderOf a = 3 ∧
      (π (inclusion h1H a)).val = planeCubic := by
  let φ := (slEquivLinear 4).toMonoidHom.comp π
  have hnat : ∀ h w, ρ h w = φ h w := fun h w =>
    (hnatural h w).trans (slEquivLinear_apply 4 (π h) w).symm
  have hn (x : H) : (x:G) ∈ normalizer (V₃:Set G) ↔ φ x ∈ BinaryLinear.parabolic plane := by
    rw [←hplane]
    exact d.natural_normalizer_iff φ hnat V₃ (le_conjugateSpanBy _ _)
      (s.line_le_plane.trans s.plane_le_seed) x
  constructor
  · intro a
    have hp := (hn (inclusion h1H a)).mp
      (Section07.ModelExclusions.point_residual_normalizes_seed s a.property)
    have h0 := (hp (Pi.single 0 1)).mpr first_mem_plane
    have h1 := (hp (Pi.single 1 1)).mpr (show (Pi.single 1 1 : Four) ∈ plane by
      constructor <;> simp)
    change (φ (inclusion h1H a) (Pi.single 0 1)) 2 = 0 ∧
      (φ (inclusion h1H a) (Pi.single 0 1)) 3 = 0 at h0
    change (φ (inclusion h1H a) (Pi.single 1 1)) 2 = 0 ∧
      (φ (inclusion h1H a) (Pi.single 1 1)) 3 = 0 at h1
    simp only [φ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,slEquivLinear_apply,Matrix.mulVec_single,MulOpposite.op_one,one_smul,Matrix.col_apply] at h0 h1
    exact ⟨h0.1,h1.1,h0.2,h1.2⟩
  · let P := H ⊓ normalizer (V₃:Set G)
    let f := π.comp (inclusion (show P ≤ H from inf_le_left))
    have hk : IsPGroup 2 f.ker := by
      rw [←MonoidHom.comap_ker]
      exact hker.comap_of_injective _ (inclusion_injective _)
    obtain ⟨x,hx⟩ := honto cubicElement
    have hxP : (x:G) ∈ normalizer (V₃:Set G) := by
      apply (hn x).mpr
      intro w
      change Matrix.mulVec (π x).val w ∈ plane ↔ w ∈ plane
      rw [hx]
      change Matrix.mulVec planeCubic w ∈ plane ↔ w ∈ plane
      simp [plane,planeCubic,dotProduct,Fin.sum_univ_succ]
    obtain ⟨A,a,hA,_,ha⟩ := exists_marked_cubic f hk ⟨⟨x,x.property,hxP⟩,hx⟩
    have ho : orderOf (a:P) = 3 := by
      apply Nat.dvd_antisymm
      · rw [A.orderOf_coe a,←hA]
        exact orderOf_dvd_natCard a
      · rw [←cubicElement_order,←ha]
        exact orderOf_map_dvd f a
    have hm : ((a:P):G) ∈ sourceOne L T V₁ :=
      Section07.ModelExclusions.seed_normalizer_theta_le s h hH hcentral
        (K:=H) le_rfl (subset_closure ⟨(a:P).property,(P.orderOf_coe _).trans ho⟩)
    refine ⟨⟨a,hm⟩,?_,congrArg Subtype.val ha⟩
    exact ((sourceOne L T V₁).orderOf_coe ⟨a,hm⟩).symm.trans
      ((P.orderOf_coe _).trans ho)

end CFSG.Quasithin.Chapter13.Section08.LinearFour


open Subgroup Representation
open scoped MatrixGroups
open Atlas.Order20160A8.Bivectors (exteriorMap)
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open SourceCompletion BinaryLinear.FlagCoordinates
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Representation.BinaryParabolicExteriorSquare.PlaneSpan
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H V V₁ V₂ V₃ M G₁ : Subgroup G}

/-- The original seed normalizer supplies both actor premises of the exterior
span calculation, retaining the same natural and exterior quotient maps. -/
theorem source_cubic_span_of_original_seed
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π : H →* SL(4,ZMod 2)) (hker : IsPGroup 2 π.ker)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hplane : d.imageSpace V₃ = plane)
    (ξ : Representation (ZMod 2) H Six)
    (p : BinaryConjugationSection H (Source.VH H V) (Source.UH H V₃) ξ)
    (hexterior : ∀ h w, ξ h w = exteriorMap (π h).val w)
    (hUV : U0 (Source.UH H V₃) V₂ ≤ Source.VH H V)
    (hfirst : p.imageSpace (U0 (Source.UH H V₃) V₂) = firstSpace)
    (hVU : V ≤ U0 (Source.UH H V₃) V₂)
    (hindex : V.relIndex (U0 (Source.UH H V₃) V₂) = 16) :
    p.imageSpace (conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁)) = planeSpace ∧
    V.relIndex (conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁)) = 64 := by
  have h1H : sourceOne L T V₁ ≤ H := le_sup_left.trans hH.1.2
  obtain ⟨hblock,a,_,ha⟩ := source_seed_plane_actors s h hH hcentral ρ d π hker honto hnatural hplane h1H
  exact ⟨source_cubic_span_image H (Source.VH H V) (Source.UH H V₃) V₂ (sourceOne L T V₁)
      ξ p π hexterior h1H hUV hfirst hblock a ha,
    source_cubic_span_index H (Source.VH H V) (Source.UH H V₃) V₂ (sourceOne L T V₁)
      ξ p π hexterior h1H hUV hfirst hblock a ha V hVU hindex⟩

open Representation.Hexacode Atlas.Codes

/-- In the original maximal quotient the source seed actors give the exact
kernel V and field dimension three of the exterior span. No cubic lift,
block-matrix premise, or kernel bound on that span is assumed. -/
theorem source_span_kernel_of_original_seed
    {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z] [Module F Z]
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π : H →* SL(4,ZMod 2)) (hker : IsPGroup 2 π.ker)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hplane : d.imageSpace V₃ = plane)
    (ξ : Representation (ZMod 2) H Six)
    (p : BinaryConjugationSection H (Source.VH H V) (Source.UH H V₃) ξ)
    (hexterior : ∀ h w, ξ h w = exteriorMap (π h).val w)
    (hUV : U0 (Source.UH H V₃) V₂ ≤ Source.VH H V)
    (hfirst : p.imageSpace (U0 (Source.UH H V₃) V₂) = firstSpace)
    (hVU : V ≤ U0 (Source.UH H V₃) V₂)
    (hindex : V.relIndex (U0 (Source.UH H V₃) V₂) = 16)
    (UL N D : Subgroup G)
    (η : Representation (ZMod 2) L Z) [IsIrreducible η]
    (q : BinaryConjugationSection L UL N η)
    (h1L : sourceOne L T V₁ ≤ L)
    (hgen : (sourceOne L T V₁).subgroupOf L ⊔ (G2 V₂).subgroupOf L = ⊤)
    (hSU : U0 (Source.UH H V₃) V₂ ≤ UL) (hVN : V ≤ N)
    (hDL : D ≤ L) (hD1 : D ≤ sourceOne L T V₁)
    (χ : D →* Fˣ) (hχ : Function.Surjective χ)
    (hscalar : ∀ x w, η (inclusion hDL x) w = (χ x : F) • w)
    (hDU : D ≤ normalizer (U0 (Source.UH H V₃) V₂))
    (hd2 : Module.finrank F (q.scalarImage D hDL χ hχ hscalar
      (U0 (Source.UH H V₃) V₂) hDU) = 2)
    (τ : Representation F HexEvenAutomorphisms Z) [IsIrreducible τ]
    (hz : ∀ w, τ hexEvenZ w = Hexacode.omega • w) :
    Module.finrank F (q.scalarImage D hDL χ hχ hscalar
      (conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁))
      (hD1.trans (le_normalizer_conjugateSpanBy _ _))) = 3 ∧
    conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁) ⊓ N = V := by
  have hi := (source_cubic_span_of_original_seed s h hH hcentral ρ d π hker honto
    hnatural hplane ξ p hexterior hUV hfirst hVU hindex).2
  exact source_span_dimension_and_kernel L UL N (Source.UH H V₃) V₂ (sourceOne L T V₁)
    V D η q h1L hgen hSU hVU hVN hi hDL hD1 χ hχ hscalar hDU hd2 τ hz

end CFSG.Quasithin.Chapter13.Section08.LinearFour


open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open SourceCompletion BinaryLinear.OuterCyclic BinaryLinear.FlagCoordinates
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Representation.BinaryParabolicExteriorSquare.PlaneSpan
variable {G : Type*} [Group G] [Finite G]

/-- The original orders construct the whole marked flag and its actual L₁
cubic. This is one natural marking shared by the subsequent exterior action. -/
theorem source_natural_flag_with_seed_actors
    (F : ChapterF.Section09.Setup G) (hF : F.Hypothesis)
    [IsElementaryAbelian 2 F.UH]
    (hU : Nat.card F.UH = 32)
    (e₀ : (F.H ⧸ pCore 2 F.H) ≃* LinearGroup 4)
    (V2 M G1 : Subgroup G)
    (s : NaturalSetup F.T F.L F.V F.V₁ V2 F.Vplus M G1)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple F.T F.L)
    (hH : F.H ∈ Source.Hz (sourceOne F.L F.T F.V₁) F.T G1 M)
    (hcentral : centralizer (F.Vplus:Set G) ≤ M ⊓ normalizer (F.V:Set G)) :
    ∃ (ρ : Representation (ZMod 2) F.H (Space 4))
      (d : BinaryConjugationSection F.H F.UH F.V₁ ρ)
      (π : F.H →* SL(4,ZMod 2)),
      π.ker = (Source.QH F.H).subgroupOf F.H ∧ Function.Surjective π ∧
      (∀ h w, ρ h w = Matrix.mulVec (π h).val w) ∧
      d.imageSpace V2 = Submodule.span (ZMod 2) {Pi.single 0 1} ∧
      d.imageSpace F.Vplus = plane ∧
      (∀ a : sourceOne F.L F.T F.V₁,
        (π (inclusion (le_sup_left.trans hH.1.2) a)).val 2 0 = 0 ∧
        (π (inclusion (le_sup_left.trans hH.1.2) a)).val 2 1 = 0 ∧
        (π (inclusion (le_sup_left.trans hH.1.2) a)).val 3 0 = 0 ∧
        (π (inclusion (le_sup_left.trans hH.1.2) a)).val 3 1 = 0) ∧
      ∃ a : sourceOne F.L F.T F.V₁, orderOf a = 3 ∧
        (π (inclusion (le_sup_left.trans hH.1.2) a)).val = planeCubic := by
  obtain ⟨ρ,d,π,hker,honto,hnatural,hpoint,hplane⟩ := source_natural_flag_marking
    F hF hU e₀ V2 s.line_le_plane s.plane_le_seed s.plane_card s.seed_card
  have hk : IsPGroup 2 π.ker := by
    rw [hker]
    exact (isPGroup_pCoreIn 2 F.H).comap_subtype
  obtain ⟨hblock,ha⟩ := source_seed_plane_actors s h hH hcentral ρ d π hk honto
    hnatural hplane (le_sup_left.trans hH.1.2)
  exact ⟨ρ,d,π,hker,honto,hnatural,hpoint,hplane,hblock,ha⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour

