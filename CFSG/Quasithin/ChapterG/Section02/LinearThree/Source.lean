module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Intersection
public import Theory.Representation.SpecialLinearThreeTransitivity

/-!
# The genuine marked natural action in G.2.5

The model is an isomorphism from the actual starred image of L to SL₃(F).
Coordinates identify V with the additive natural module and intertwine
ambient conjugation with that model. The marked point is an F-line, and
the three marked points give an internal direct decomposition of V.
No radical, generation, quotient-layer or chief-factor conclusion is part
of this hypothesis.

Transitivity of SL₃(F) on nonzero columns proves irreducibility on the
underlying binary group. G.2.2's containment U≤T and Frattini bound then
give the triple intersection and commutator conclusions without further
normalization or elementary-abelian assumptions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Hypothesis G.2.1 and Lemma G.2.5, printed pp.332,335–336.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree
open Setup
variable {G : Type*} [Group G]

/-- The restriction of the literal star quotient map to L. -/
def starProjection (D : Setup G) : D.L →* D.star D.L :=
  ((QuotientGroup.mk' (pCore 2 D.LT)).comp
    (inclusion (show D.L ≤ D.LT from le_sup_left))).codRestrict _
    (fun l => mem_map.mpr ⟨⟨l, (show D.L ≤ D.LT from le_sup_left) l.property⟩,
      l.property, rfl⟩)

theorem starProjection_surjective (D : Setup G) : Function.Surjective (starProjection D) := by
  intro q
  obtain ⟨l, hl, he⟩ := q.property
  exact ⟨⟨l, hl⟩, Subtype.ext he⟩

theorem normalizes_of_span (D : Setup G) (hspan : D.VL = D.V) :
    D.L ≤ normalizer (D.V : Set G) := by
  rw [← hspan]
  exact le_normalizer_conjugateSpanBy D.V₁ D.L

/-- All the additional hypotheses printed in G.2.5, with actual carriers,
quotient map and natural action. The two directness fields, together with
`points_span`, express V=V₁⊕V₁ᵍ⊕V₁ʰ. -/
structure Hypothesis [Finite G] (D : Setup G) (F : Type*) [Field F] [Finite F]
    (n : ℕ) (g h : G) where
  setup : D.Hypothesis
  exponent_pos : 0 < n
  field_card : Nat.card F = 2 ^ n
  span_eq : D.VL = D.V
  model : D.star D.L ≃* SL(3, F)
  coordinates : D.V ≃* Multiplicative (Fin 3 → F)
  equivariant (l : D.L) (v : D.V) :
    (coordinates ⟨(l : G) * v * (l : G)⁻¹,
      (mem_normalizer_iff.mp (normalizes_of_span D span_eq l.property) v).mp v.property⟩).toAdd =
        (model (starProjection D l)).val *ᵥ (coordinates v).toAdd
  point : Submodule F (Fin 3 → F)
  point_dimension : Module.finrank F point = 1
  point_mem (v : D.V) : (v : G) ∈ D.V₁ ↔ (coordinates v).toAdd ∈ point
  star_U_ne_bot : D.star D.U ≠ ⊥
  g_mem : g ∈ D.L
  h_mem : h ∈ D.L
  points_disjoint : Disjoint D.V₁ (conjugate D.V₁ g)
  third_disjoint : Disjoint (D.V₁ ⊔ conjugate D.V₁ g) (conjugate D.V₁ h)
  points_span : (D.V₁ ⊔ conjugate D.V₁ g) ⊔ conjugate D.V₁ h = D.V

namespace Hypothesis
variable [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : Hypothesis D F n g h)

include d

/-- Irreducibility is proved from the model and its actual conjugation
action, even when F has more than two elements. -/
theorem irreducible (A : Subgroup G) (hAV : A ≤ D.V)
    (hLA : D.L ≤ normalizer (A : Set G)) : A = ⊥ ∨ A = D.V := by
  by_cases hA : A = ⊥
  · exact Or.inl hA
  right
  apply le_antisymm hAV
  obtain ⟨a, ha1⟩ := ne_bot_iff_exists_ne_one.mp hA
  have ha := a.property
  have ha1 : (a : G) ≠ 1 := fun he => ha1 (Subtype.ext he)
  have hca : (d.coordinates ⟨a, hAV ha⟩).toAdd ≠ 0 := by
    intro he
    have hh : (⟨a, hAV ha⟩ : D.V) = 1 := d.coordinates.injective (he.trans d.coordinates.map_one.symm)
    exact ha1 (congrArg Subtype.val hh)
  intro v hv
  by_cases hv1 : v = 1
  · simp [hv1]
  have hcv : (d.coordinates ⟨v, hv⟩).toAdd ≠ 0 := by
    intro he
    have hh : (⟨v, hv⟩ : D.V) = 1 := d.coordinates.injective (he.trans d.coordinates.map_one.symm)
    exact hv1 (congrArg Subtype.val hh)
  obtain ⟨x, hx⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three _ _ hca hcv
  obtain ⟨l, hl⟩ := (d.model.surjective.comp (starProjection_surjective D)) x
  change d.model (starProjection D l) = x at hl
  have he := (d.equivariant l ⟨a, hAV ha⟩).trans (by simpa [hl] using hx)
  have he' : (l : G) * a * (l : G)⁻¹ = v :=
    congrArg Subtype.val (d.coordinates.injective he)
  exact he' ▸ (mem_normalizer_iff.mp (hLA l.property) a).mp ha

/-- The two-group input needed by the intersection proof follows from the
actual Sylow marking and the preceding conclusion U≤T of G.2.2. -/
theorem U_isPGroup (hUT : D.U ≤ D.T) : IsPGroup 2 D.U := by
  obtain ⟨P, hP⟩ := d.setup.sylow_LT
  have hT : IsPGroup 2 D.T := by
    rw [← hP]
    exact P.isPGroup'.map D.LT.subtype
  exact hT.of_injective (inclusion hUT) (inclusion_injective hUT)

/-- All three generating subgroups normalize the actual natural module. -/
theorem I_normalizes (hUT : D.U ≤ D.T) : I D g h ≤ normalizer (D.V : Set G) := by
  have hU := hUT.trans d.setup.T_normalizes_V
  have hc (x : G) (hx : x ∈ D.L) : conjugate D.U x ≤ normalizer (D.V : Set G) := by
    rintro _ ⟨u, hu, rfl⟩
    change x⁻¹ * u * x⁻¹⁻¹ ∈ normalizer (D.V : Set G)
    rw [inv_inv]
    exact (normalizer (D.V : Set G)).mul_mem
      ((normalizer (D.V : Set G)).mul_mem
        ((normalizer (D.V : Set G)).inv_mem (normalizes_of_span D d.span_eq hx)) (hU hu))
      (normalizes_of_span D d.span_eq hx)
  exact sup_le (sup_le hU (hc g d.g_mem)) (hc h d.h_mem)

/-- G.2.5's actual triple intersection, using only the two stated G.2.2
outputs. The source model discharges every geometric input to the lemma. -/
theorem intersection (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    D.V ≤ S₂ D g h ∧ S₂ D g h ≤ S D g h ∧
    ((S₂ D g h).subgroupOf (I D g h)).Normal ∧
    ⁅S₂ D g h, I D g h⁆ ≤ D.V ∧ IsElementaryAbelian 2 (S₂ D g h) :=
  intersection_layer D g h (d.U_isPGroup hUT) hf d.setup.point_le (d.I_normalizes hUT)
    (normalizes_of_span D d.span_eq d.g_mem)
    (normalizes_of_span D d.span_eq d.h_mem) d.points_disjoint

/-- Once clause (2) has placed L in I, the first source layer is central
in S. The natural-action irreducibility premise is fully discharged. -/
theorem central_first (hUT : D.U ≤ D.T) (hLI : D.L ≤ I D g h) :
    D.V ≤ S D g h ⊓ centralizer (S D g h : Set G) :=
  central_first_layer D g h (d.U_isPGroup hUT) (d.I_normalizes hUT) hLI d.irreducible

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree
