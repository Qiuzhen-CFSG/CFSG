module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry.Marking
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.Coordinates
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.Marked

/-!
# The marked projective geometry of the actual G.2.4 upper quotient

The concrete field F₄ and an actual SL₂(F₄) isomorphism mark the literal U*
as the root of the standard field point. Transport the canonical starred
action on Additive(S/S₂) along that isomorphism. Its original quotient
coordinates retain the W and Wᵍ images, which are complementary. The supplied
starred Borel equality gives full root-normalizer invariance. The general
G.1.5(3) orbit construction then proves every clause of G.1.3, for the same
quotient and the same right conjugator g, including the zero-module case.

The earlier generation, kernel, splitting, V Vᵍ, Sylow and Borel conclusions
remain explicit. Their producers are `qt-g024-structure` and
`qt-g024-starred-borel`; the enclosing G.2.4 source owner discharges them.
This module constructs the geometry without a recognition input. The parent
uses genuine G.1.3 to recognize the module and the proved `fixed_copies_card`
for the final root-fixed equality, rather than assuming G.1.5(2).

Source: Aschbacher–Smith, G.1.1, G.1.3 and G.1.5(3), printed pp.327–328,
and G.2.4(6), printed pp.334–335, PDF pp.338–339 and 345–346.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup Recognition Recognition.ProjectiveGeometry
open RankOneHigherFields.QuotientAction.Projective
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}
  (d : Hypothesis D g)

/-- The literal upper quotient satisfies every projective recognition clause,
with its original quotient map, W-image and original right conjugator. -/
theorem exists_upper_projective_geometry
    (hI : D.I g = D.L ⊔ D.U)
    (hcore : D.S g = D.I g ⊓ D.LT.pCoreIn 2)
    (hsplit : D.S g = D.W g ⊔ conjugate (D.W g) g)
    (hVV : D.V ⊔ conjugate D.V g = D.VL)
    (hSylow : ∃ P : Sylow 2 (D.star D.L),
      (P : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U)
    (hB : (D.star D.L₁).subgroupOf (D.star D.L) =
      normalizer (((D.star D.U).subgroupOf (D.star D.L)) : Set (D.star D.L))) :
    let hLI : D.L ≤ D.I g := hI ▸ le_sup_left
    let hILT := d.upper_actor_le hI
    let hstar := d.upper_actor_star hI (upper_star_U_le hSylow)
    let := d.second_normal_in_core hLI
    let := d.upper_elementary hLI hcore hsplit
    ∃ (e : D.star D.L ≃* SL(2, F4))
      (σ : Representation (ZMod 2) SL(2, F4) (Additive (UpperQuotient D g)))
      (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g)
        (σ.comp (e.toMonoidHom.comp (upperStarProjection D g hILT hstar))))
      (φ : ProjectivePoint F4 → Submodule (ZMod 2) (Additive (UpperQuotient D g))),
      ((D.star D.U).subgroupOf (D.star D.L)).map e.toMonoidHom =
        RootGroup F4 standardPoint.val ∧
      (∀ s : D.S g, (c.coordinates s).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)) s)) ∧
      ProjectiveCriterion σ φ ∧
      φ standardPoint = upperSubspace D g (D.W g) ∧
      φ (translate (e (upperStarProjection D g hILT hstar
        (⟨g, hLI d.g_mem⟩ : D.I g)⁻¹)) standardPoint) =
          upperSubspace D g (conjugate (D.W g) g) := by
  let hLI : D.L ≤ D.I g := hI ▸ le_sup_left
  let hILT := d.upper_actor_le hI
  let hstar := d.upper_actor_star hI (upper_star_U_le hSylow)
  let := d.second_normal_in_core hLI
  let := d.upper_elementary hLI hcore hsplit
  obtain ⟨e, he⟩ := d.exists_upper_marked_model hSylow
  obtain ⟨σ₀, c₀, hcoord⟩ := d.upper_action hLI hcore hsplit hILT hstar
  let σ := σ₀.comp e.symm.toMonoidHom
  let π := upperStarProjection D g hILT hstar
  let c : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g)
      (σ.comp (e.toMonoidHom.comp π)) := {
    c₀ with
    equivariant := by
      intro i s
      change _ = σ₀ (e.symm (e (π i))) (c₀.coordinates s).toAdd
      rw [e.symm_apply_apply]
      exact c₀.equivariant i s }
  let t := e (π (⟨g, hLI d.g_mem⟩ : D.I g)⁻¹)
  have ht : t = e (starProjection D (⟨g, d.g_mem⟩ : D.L))⁻¹ := by
    change e (π ((⟨g, hLI d.g_mem⟩ : D.I g)⁻¹)) = _
    simp only [map_inv]
    exact congrArg (fun x => (e x)⁻¹)
      (upperStarProjection_on_L D g hILT hstar hLI ⟨g, d.g_mem⟩)
  have hne : standardPoint.val ≠
      standardPoint.val.map (Representation.specialLinearNatural 2 t) := by
    rw [ht]
    exact d.upper_marked_point_ne hB e standardPoint he
  obtain ⟨hcompl, hmove₀⟩ := d.upper_marked_complement hLI hsplit hVV (σ₀.comp π) c₀
  have hmove : c.imageSpace (conjugate (D.W g) g) =
      (c.imageSpace (D.W g)).map (σ t) := by
    change c₀.imageSpace (conjugate (D.W g) g) =
      (c₀.imageSpace (D.W g)).map (σ₀ (e.symm (e (π _))))
    rw [e.symm_apply_apply]
    exact hmove₀
  have hcompl' : IsCompl (c.imageSpace (D.W g)) ((c.imageSpace (D.W g)).map (σ t)) := by
    rw [← hmove]
    exact hcompl
  have hroot : ∀ a ∈ RootGroup F4 standardPoint.val,
      LinearMap.range (σ a - 1) ≤ c.imageSpace (D.W g) ∧
      ∀ v ∈ c.imageSpace (D.W g), σ a v = v := by
    intro a ha
    rw [← he] at ha
    exact d.upper_star_root_bounds hcore hILT hstar σ₀ c₀ (e.symm a)
      (mem_map_equiv.mp ha)
  have hN : ∀ a ∈ normalizer (RootGroup F4 standardPoint.val : Set SL(2, F4)),
      (c.imageSpace (D.W g)).map (σ a) = c.imageSpace (D.W g) := by
    intro a ha
    rw [← he, ← map_normalizer_eq_of_bijective _ e.bijective] at ha
    exact d.upper_normalizer_invariant hLI hILT hstar hB σ₀ c₀ (e.symm a)
      (mem_map_equiv.mp ha)
  obtain ⟨φ, hA, hφ, hcriterion⟩ := exists_orbit_criterion σ standardPoint
    (c.imageSpace (D.W g)) t hne hcompl' hN hroot
  have himage (K : Subgroup G) : c.imageSpace K = upperSubspace D g K :=
    upper_imageSpace_eq hILT hstar σ₀ c₀ hcoord K
  refine ⟨e, σ, c, φ, he, hcoord, hcriterion, hA.trans (himage _), ?_⟩
  exact (hφ t (translate t standardPoint) (translate_val t standardPoint)).trans
    (hmove.symm.trans (himage _))

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
