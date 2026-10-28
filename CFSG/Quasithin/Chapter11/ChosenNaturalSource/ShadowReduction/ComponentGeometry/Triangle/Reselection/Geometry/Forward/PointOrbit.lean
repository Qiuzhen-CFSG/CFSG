module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry.PointPlacement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.ScalarGeometry

/-!
# Centralizing the reselected point through the Cartan orbit

A nontrivial T-invariant point meets the actual Sylow omega-center. Every
element of K centralizes that intersection. The Cartan normalizes K and
acts transitively on the nonidentity elements of the field point, so all
of K centralizes the point, without requiring K to lie in I.

This replaces the printed expression [Z ∩ U₁, X_K], which is trivial
under [Z,K] = 1 and X_K ≤ K. The Cartan orbit uses the full X instead.
The original-triangle application is in Forward/Source.lean; the paired
Cartan placement remains with qt-d-1222-shadow-component-triangle.
Source: Aschbacher–Smith, 11.1.2(3), printed p.764.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
open LocalGeometry LocalGeometry.Normalizers
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {I U : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T I U) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Omega-center detection and the full Cartan orbit place the entire
ambient K in the centralizer of the literal new point. -/
theorem component_centralizes_point_of_cartan
    (hfix : U ⊓ centralizer (I : Set G) = ⊥)
    (hfixed : f.Vi 0 = U ⊓ centralizer (sourceTL T I : Set G))
    (K X : Subgroup G) (hX : IsCartan T I X)
    (hXK : X ≤ normalizer (K : Set G))
    (hKZ : K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G)) :
    K ≤ centralizer (f.Vi 0 : Set G) := by
  let Z := omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype)
  have hPU : f.Vi 0 ≤ U := D.centralQuotientPreimage_le _
  have hne : Z ⊓ f.Vi 0 ≠ ⊥ := by
    intro he
    exact f.V_ne_bot 0 (eq_bot_of_normalized_of_omega_center_disjoint
      (T : Subgroup G) (f.Vi 0) T.isPGroup' (hPU.trans D.le_sylow) (f.invariant 0) he)
  obtain ⟨⟨v, hv⟩, hvne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hv1 : v ≠ 1 := fun he => hvne (Subtype.ext he)
  have hvK : v ∈ centralizer (K : Set G) := (le_centralizer_iff.mp hKZ) hv.1
  have hXN : X ≤ normalizer (centralizer (K : Set G) : Set G) :=
    hXK.trans (normalizer_le_normalizer_centralizer _)
  have hreg := (chosen_line_scalar_geometry f hX hfixed hfix).2.1
  apply le_centralizer_iff.mpr
  intro u hu
  by_cases hu1 : u = 1
  · exact hu1 ▸ (centralizer (K : Set G)).one_mem
  let v' : Additive (f.Vi 0) := Additive.ofMul ⟨v,hv.2⟩
  let u' : Additive (f.Vi 0) := Additive.ofMul ⟨u,hu⟩
  have hv0 : v' ≠ 0 := fun he => hv1 (congrArg (fun w : Additive (f.Vi 0) => w.toMul.val) he)
  have hu0 : u' ≠ 0 := fun he => hu1 (congrArg (fun w : Additive (f.Vi 0) => w.toMul.val) he)
  obtain ⟨a,ha,_⟩ := hreg v' u' hv0 hu0
  obtain ⟨x,hx,hxa⟩ := a.property
  have he : x.val * v * x.val⁻¹ = u := by
    have hh : lineAction f x v' = u' := by rw [hxa]; exact ha
    exact congrArg (fun w : Additive (f.Vi 0) => w.toMul.val) hh
  rw [← he]
  exact (mem_normalizer_iff.mp (hXN hx) v).mp hvK

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
