module
public import Theory.Representation.BinaryParabolicExteriorSquare.SingularRecognition
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceExteriorAlignment
public import Theory.Representation.BinaryConjugationSection.Relabel

/-!
# Constructing the compatible exterior marking from a source line

The singular-point and singular-line calculations construct an injective
exterior intertwiner from one marked line relation. The original equality
V_H = ⟨V^H⟩ makes it surjective. Relabelling the literal V_H/U_H section
retains its original coordinate map through the resulting linear equivalence
and uses exactly the supplied natural four-space quotient map.

The natural seed plane and original seed normalizer supply the required
point-stabilizer invariance. The final application constructs the exterior
coordinates and feeds them to the original L₁-span calculation, obtaining
the marked images and index 64 without assuming an exterior representation,
a presentation kernel, line transitivity, or two-point coverage.

The local line relation and its marked actors remain explicit: they must
be transported from the original first tensor. The second tensor, extra-line
movement and chief-factor obstruction also remain with this linear-four
owner. This conditional construction does not complete 13.8.28. Earlier
13.8.27 remains with qt-d-138-six-g2-source, and final 13.8.1 assembly with
qt-d-1381-source.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
B.4.13 and 13.8.29(5)--30, printed pp.97--98,964.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups
open Atlas.Order20160A8.Bivectors (pfaffian exteriorMap)
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open Representation.BinaryParabolicExteriorSquare
open SingularPresentation
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

/-- One marked line constructs the exterior marking on the original VH/UH.
The quotient map changes only by the resulting linear equivalence. -/
theorem source_exterior_marking_of_one_line
    (H UH V : Subgroup G) (ρ : Representation (ZMod 2) H W)
    (p : BinaryConjugationSection H (Source.VH H V) UH ρ)
    (π : H →* SL(4,ZMod 2)) (hπ : Function.Surjective π)
    (v : W) (hseed : p.imageSpace V = Submodule.span (ZMod 2) {v})
    (hproper : ¬ V ≤ UH)
    (hfix : ∀ g, exteriorMap (π g).val (Pi.single 0 1) = (Pi.single 0 1 : Six) → ρ g v = v)
    (a b : H)
    (ha : exteriorMap (π a).val (Pi.single 0 1) = (Pi.single 1 1 : Six))
    (hb : exteriorMap (π b).val (Pi.single 0 1) = (Pi.single 0 1 + Pi.single 1 1 : Six))
    (hline : v + ρ a v = ρ b v) :
    ∃ (p₆ : BinaryConjugationSection H (Source.VH H V) UH (action π))
      (E : Six ≃ₗ[ZMod 2] W),
      (∀ v : Source.VH H V, E (p₆.coordinates v).toAdd = (p.coordinates v).toAdd) ∧
      E (Pi.single 0 1) = v := by
  have hv0 : v ≠ 0 := by
    intro he
    have hz : p.imageSpace V = ⊥ := by rw [hseed,he,Submodule.span_singleton_eq_bot.mpr rfl]
    apply hproper
    intro v hv
    have hh := (p.mem_imageSpace_iff V _).mpr
      ⟨⟨v,le_conjugateSpanBy V H hv⟩,hv,rfl⟩
    rw [hz] at hh
    exact (p.coordinates_eq_one_iff _).mp hh
  obtain ⟨F,hF,hvalue⟩ := exists_intertwiner_of_one_line π hπ ρ v hv0 hfix a b ha hb hline
  have hgen : F.range.toSubmodule = ⊤ := by
    apply p.generated_image_le V rfl F.range
    rw [hseed]
    apply Submodule.span_le.mpr
    intro w hw
    obtain rfl := Set.mem_singleton_iff.mp hw
    exact ⟨Pi.single 0 1,hvalue⟩
  have honto : Function.Surjective F := LinearMap.range_eq_top.mp hgen
  let E := F.ofBijective ⟨hF,honto⟩
  let p₆ : BinaryConjugationSection H (Source.VH H V) UH (action π) :=
    p.relabel (MonoidHom.id H) E.symm
  refine ⟨p₆,E.toLinearEquiv,?_,hvalue⟩
  intro v
  exact E.toLinearEquiv.apply_symm_apply (p.coordinates v).toAdd

private theorem wedge_point_columns : ∀ u v : Fin 4 → ZMod 2,
    Atlas.Order20160A8.Bivectors.wedge u v = Pi.single 0 1 →
      (u 2 = 0 ∧ u 3 = 0) ∧ (v 2 = 0 ∧ v 3 = 0) := by
  decide +kernel

/-- The original seed normalizer supplies point-stabilizer invariance of
its quotient line, for the same natural marking used by the exterior action. -/
theorem source_exterior_seed_fixed
    (H UH V1 V3 VH V : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2))
    (hnatural : ∀ h x, ρ h x = Matrix.mulVec (π h).val x)
    (h13 : V1 ≤ V3) (h3U : V3 ≤ UH)
    (hplane : d.imageSpace V3 = BinaryLinear.FlagCoordinates.plane)
    (hNV : H ⊓ normalizer (V3:Set G) ≤ normalizer (V:Set G))
    (ξ : Representation (ZMod 2) H W) (p : BinaryConjugationSection H VH UH ξ)
    (v : W) (hseed : p.imageSpace V = Submodule.span (ZMod 2) {v})
    (a : H) (ha : exteriorMap (π a).val (Pi.single 0 1) = (Pi.single 0 1 : Six)) :
    ξ a v = v := by
  let P := BinaryLinear.FlagCoordinates.plane
  have hcols : ρ a (Pi.single 0 1) ∈ P ∧ ρ a (Pi.single 1 1) ∈ P := by
    have he : exteriorMap (π a).val (Pi.single 0 1) =
        Atlas.Order20160A8.Bivectors.wedge
          ((π a).val.mulVec (Pi.single 0 1)) ((π a).val.mulVec (Pi.single 1 1)) := by
      rw [←Atlas.Order20160A8.Bivectors.wedge_basis 0,
        Atlas.Order20160A8.Bivectors.exteriorMap_wedge]
      rfl
    change ((ρ a (Pi.single 0 1)) 2 = 0 ∧ (ρ a (Pi.single 0 1)) 3 = 0) ∧
      ((ρ a (Pi.single 1 1)) 2 = 0 ∧ (ρ a (Pi.single 1 1)) 3 = 0)
    simpa only [hnatural] using wedge_point_columns _ _ (he.symm.trans ha)
  have hle : P.map (ρ a) ≤ P := by
    rintro y ⟨x,hx,rfl⟩
    have he : x = x 0 • Pi.single 0 1 + x 1 • Pi.single 1 1 := by
      ext i
      fin_cases i <;> simp [show x 2 = 0 from hx.1,show x 3 = 0 from hx.2]
    rw [he,map_add,map_smul,map_smul]
    exact P.add_mem (P.smul_mem _ hcols.1) (P.smul_mem _ hcols.2)
  let E : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) := {
    toLinearMap := ρ a
    invFun := ρ a⁻¹
    left_inv := ρ.inv_self_apply a
    right_inv := ρ.self_inv_apply a }
  have heP : P.map (ρ a) = P :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq E P)
  have haN : (a:G) ∈ normalizer (V3:Set G) := by
    rw [←d.subspacePreimage_imageSpace V3 h3U h13,hplane,
      d.mem_normalizer_subspacePreimage_iff]
    exact heP
  by_cases hv : v = 0
  · simp [hv]
  have hvP : v ∈ p.imageSpace V := by rw [hseed]; exact Submodule.subset_span (Set.mem_singleton v)
  have hh := p.imageSpace_apply_mem V a (hNV ⟨a.property,haN⟩) v hvP
  rw [hseed] at hh
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hh
  have hc0 : c ≠ 0 := by
    intro hc0
    have hz : ξ a v = 0 := by simpa only [hc0,zero_smul] using hc.symm
    have hh := congrArg (ξ a⁻¹) hz
    rw [Representation.inv_self_apply,map_zero] at hh
    exact hv hh
  have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
  simpa only [hc1,one_smul] using hc.symm

open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open PlaneSpan (pointSpace firstSpace planeSpace)
open BinaryLinear.FlagCoordinates
variable [Finite G] {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}

/-- A single source line constructs the compatible exterior coordinates and
feeds the literal L₁-span calculation, including its original index 64. -/
theorem source_cubic_span_of_one_line
    {H : Subgroup G}
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π : H →* SL(4,ZMod 2))
    (hker : π.ker = (Source.QH H).subgroupOf H)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hpoint : d.imageSpace V₂ = Submodule.span (ZMod 2) {Pi.single 0 1})
    (hplane : d.imageSpace V₃ = plane)
    (ξ : Representation (ZMod 2) H W)
    (p : BinaryConjugationSection H (Source.VH H V) (Source.UH H V₃) ξ)
    (v : W) (hseed : p.imageSpace V = Submodule.span (ZMod 2) {v})
    (hproper : ¬ V ≤ Source.UH H V₃)
    (a b : H)
    (ha : exteriorMap (π a).val (Pi.single 0 1) = (Pi.single 1 1 : Six))
    (hb : exteriorMap (π b).val (Pi.single 0 1) = (Pi.single 0 1 + Pi.single 1 1 : Six))
    (hline : v + ξ a v = ξ b v)
    (hUV : U0 (Source.UH H V₃) V₂ ≤ Source.VH H V)
    (hVU : V ≤ U0 (Source.UH H V₃) V₂)
    (hindex : V.relIndex (U0 (Source.UH H V₃) V₂) = 16)
    (hUcard : Nat.card (Source.UH H V₃) = 32) :
    ∃ p₆ : BinaryConjugationSection H (Source.VH H V) (Source.UH H V₃) (action π),
      p₆.imageSpace V = pointSpace ∧
      p₆.imageSpace (U0 (Source.UH H V₃) V₂) = firstSpace ∧
      p₆.imageSpace (conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁)) = planeSpace ∧
      V.relIndex (conjugateSpanBy (U0 (Source.UH H V₃) V₂) (sourceOne L T V₁)) = 64 := by
  have hNV : H ⊓ normalizer (V₃:Set G) ≤ normalizer (V:Set G) :=
    (source_seed_normalizer_le_LT s h hH hcentral ρ d π hker hnatural).trans s.normalizes_V
  have hfix := source_exterior_seed_fixed H (Source.UH H V₃) V₁ V₃ (Source.VH H V) V
    ρ d π hnatural (s.line_le_plane.trans s.plane_le_seed)
    (le_conjugateSpanBy _ _) hplane hNV ξ p v hseed
  obtain ⟨p₆,E,hcoords,hvalue⟩ := source_exterior_marking_of_one_line
    H (Source.UH H V₃) V ξ p π honto v hseed hproper hfix a b ha hb hline
  exact ⟨p₆,source_cubic_span_with_forced_exterior_images s h hH hcentral
    ρ d π hker honto hnatural hpoint hplane (action π) p₆ (fun _ _ => rfl)
    hUV hVU hindex hUcard⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour
