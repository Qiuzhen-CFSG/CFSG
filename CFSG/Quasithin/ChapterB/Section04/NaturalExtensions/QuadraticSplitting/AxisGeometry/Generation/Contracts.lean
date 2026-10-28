module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.AxisGeometry.FourSubgroups
/-!
# Marked parameters for full axis generation

Shear parameters turn subgroup generation into additive generation. Two
independent parameters give a literal order-four subgroup of the marked Q.
The remaining matrix obligations are stated separately: full Levi pair
transports and the identification of original root groups with parameter
lines, including inverse-transpose orientation. These are obligations,
not extra hypotheses of B.4.9(1).

Source: Aschbacher–Smith B.4.9(1), printed p.92, combined manuscript
of 1 March 2004.
-/

@[expose] public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterK.Linear.Natural
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F n ρ}
namespace QuotientCoordinates
variable (m : QuotientCoordinates d) (j : Fin n)
theorem axisShear_injective : Function.Injective (m.axisShear j) :=
  m.action.groupEquiv.symm.injective.comp (shear_injective F n j)

@[simp] theorem axisShear_add (u v : coordinateHyperplane F n j) :
    m.axisShear j (u+v) = m.axisShear j u * m.axisShear j v := by
  simp only [axisShear, shear_add, map_mul]

@[simp] theorem axisShear_neg (u : coordinateHyperplane F n j) :
    m.axisShear j (-u) = (m.axisShear j u)⁻¹ := by
  apply mul_left_cancel (a := m.axisShear j u)
  rw [← m.axisShear_add, add_neg_cancel, m.axisShear_zero, mul_inv_cancel]

noncomputable def axisShearHom : Multiplicative (coordinateHyperplane F n j) →* G where
  toFun w := m.axisShear j w.toAdd
  map_one' := m.axisShear_zero j
  map_mul' u v := m.axisShear_add j u.toAdd v.toAdd

/-- The additive shear parameters belonging to a given actual subgroup. -/
noncomputable def axisParameters (H : Subgroup G) : AddSubgroup (coordinateHyperplane F n j) where
  carrier := {w | m.axisShear j w ∈ H}
  zero_mem' := by change m.axisShear j 0 ∈ H; rw [m.axisShear_zero]; exact H.one_mem
  add_mem' := by intro u v hu hv; change m.axisShear j (u+v) ∈ H; rw [m.axisShear_add]; exact H.mul_mem hu hv
  neg_mem' := by intro u hu; change m.axisShear j (-u) ∈ H; rw [m.axisShear_neg]; exact H.inv_mem hu

/-- The actual binary four-group obtained from two independent shear parameters. -/
noncomputable def axisPair (u v : coordinateHyperplane F n j) : Subgroup G :=
  (Submodule.span (ZMod 2) {u,v}).toAddSubgroup.toSubgroup.map (m.axisShearHom j)

theorem axisPair_le_Q (u v : coordinateHyperplane F n j) :
    m.axisPair j u v ≤ m.Q j := by
  rintro _ ⟨w, _, rfl⟩
  exact m.axisShear_mem j w.toAdd

theorem axisPair_left (u v : coordinateHyperplane F n j) :
    m.axisShear j u ∈ m.axisPair j u v := by
  refine ⟨Multiplicative.ofAdd u, ?_, rfl⟩
  change u ∈ Submodule.span (ZMod 2) {u,v}
  exact Submodule.subset_span (by simp)

theorem axisPair_right (u v : coordinateHyperplane F n j) :
    m.axisShear j v ∈ m.axisPair j u v := by
  refine ⟨Multiplicative.ofAdd v, ?_, rfl⟩
  change v ∈ Submodule.span (ZMod 2) {u,v}
  exact Submodule.subset_span (by simp)

theorem axisPair_card (u v : coordinateHyperplane F n j)
    (h : LinearIndependent F.Carrier ![u,v]) : Nat.card (m.axisPair j u v) = 4 := by
  have hi : Function.Injective (m.axisShearHom j) :=
    (m.axisShear_injective j).comp Multiplicative.toAdd.injective
  rw [axisPair, Subgroup.card_map_of_injective hi]
  change Nat.card (Submodule.span (ZMod 2) {u,v}) = 4
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hr := finrank_span_eq_card (h.restrict_scalars' (ZMod 2))
  have hset : Set.range ![u,v] = {u,v} := by
    ext w
    change (∃ i : Fin 2, ![u,v] i = w) ↔ w = u ∨ w = v
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi.symm
      · exact Or.inr hi.symm
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [hset, Fintype.card_fin] at hr
  rw [hr]
  norm_num

/-- Literal conjugation transports needed from the full Levi. The two-dimensional
case retains scalar cubes; the binary case permits every independent target pair. -/
structure LeviPairTransports : Prop where
  binary : F.degree = 1 → 3 ≤ n →
    ∀ u v : coordinateHyperplane F n j, LinearIndependent F.Carrier ![u,v] →
    ∀ e x : coordinateHyperplane F n j, LinearIndependent F.Carrier ![e,x] →
    ∃ g : G, g * m.axisShear j u * g⁻¹ = m.axisShear j e ∧
      g * m.axisShear j v * g⁻¹ = m.axisShear j x
  cubic : n = 3 →
    ∀ u v : coordinateHyperplane F n j, LinearIndependent F.Carrier ![u,v] →
    ∀ e : coordinateHyperplane F n j, e ≠ 0 →
    ∃ x : coordinateHyperplane F n j,
      (∀ w, ∃ a b : F.Carrier, w = a • e + b • x) ∧
      ∀ a t : F.Carrier, t ≠ 0 →
        ∃ g : G, g * m.axisShear j u * g⁻¹ = m.axisShear j e ∧
          g * m.axisShear j v * g⁻¹ = m.axisShear j (a • e + t^3 • x)

/-- Root groups in the original marking are precisely the defining-field
lines of shear parameters. Both recorded orientations must establish this. -/
def RootLineDescription : Prop :=
  ∀ A : Subgroup G, A ≤ m.Q j →
    (InRootGroup d A ↔ ∃ w : coordinateHyperplane F n j, w ≠ 0 ∧
      ∀ a ∈ A, ∃ c : F.Carrier, m.axisShear j (c • w) = a)
end QuotientCoordinates
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
