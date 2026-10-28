module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.Radical.Action
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.Radical.LinearImage
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.Radical.Geometry.Generation

/-!
# Point-radical inputs for G.2.5

The faithful starred action places U* inside the supplied L*: its semilinear
action fixes the marked F-line pointwise, and its square-one elements have
determinant one. Full point-parabolic minimality then identifies U* with the
two-core of N_L(V₁)* and gives actual additive F² coordinates. The radicals
at the original three independent marked points generate L*, so I* = L*.

The imported action results give elementarity and [V,U]=V₁. The action
commutator formula below identifies this with [V,U*] for the literal star
quotient. Only U≤T and Φ(U)≤V₁, the two earlier G.2.2 conclusions, remain
explicit. Every result includes n=1. The structural assembly in `Structure`
uses these outputs to discharge the independent central-kernel branch.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.5(1–2), printed pp.335–336, using G.2.2–3 on pp.332–334.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree
open Setup
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G]
variable {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : Hypothesis D F n g h)

include d

/-- G.2.5(1): the two-core of the full starred setwise point normalizer.
The linear-image premise of the geometric calculation is discharged. -/
theorem star_U_eq_point_core (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    D.star D.U = (D.star (D.L ⊓ D.G₁)).pCoreIn 2 :=
  d.star_U_eq_pointNormalizer_core hUT hf (d.star_U_le_star_L hUT hf)

/-- The actual radical in G.2.5(1), with its additive F² coordinates. -/
noncomputable def starUEquiv (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    D.star D.U ≃* Multiplicative (Fin 2 → F) :=
  d.starUPointRadicalEquiv hUT hf (d.star_U_le_star_L hUT hf)

/-- The order of the elementary abelian starred U is 2^(2n). -/
theorem card_star_U (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    Nat.card (D.star D.U) = 2 ^ (2 * n) :=
  d.card_star_U_point_radical hUT hf (d.star_U_le_star_L hUT hf)

/-- The three original marked conjugates generate the whole starred L.
This supplies the starred-generation input to `Structure.Reduction`. -/
theorem star_I_eq_star_L (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    D.star (I D g h) = D.star D.L :=
  d.star_I_eq_star_L_of_linear_image hUT hf (d.star_U_le_star_L hUT hf)

/-- Lifting a starred U-actor gives exactly its original conjugation on V. -/
theorem starAction_UStarProjection (hUT : D.U ≤ D.T) (u : D.U) (v : D.V) :
    (d.coordinates.symm
      (d.starAction (UStarProjection D hUT u) (d.coordinates v)) : G) =
        (u : G) * v * (u : G)⁻¹ := by
  change (d.coordinates.symm
    (d.naturalAction ⟨u, (hUT.trans le_sup_right) u.property⟩ (d.coordinates v)) : G) = _
  rw [d.naturalAction_apply, d.coordinates.symm_apply_apply]

/-- The subgroup [V,U*] formed from the actual induced action is the marked
point V₁. Coordinates are pulled back to V before embedding in G. -/
theorem starAction_commutator_eq_point (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    Subgroup.closure {x : G | ∃ u : D.star D.U, ∃ v : D.V,
      (d.coordinates.symm (d.starAction u (d.coordinates v)) : G) * (v : G)⁻¹ = x} =
        D.V₁ := by
  rw [← d.commutator_V_U_eq_point hUT hf, commutator_comm D.V D.U,
    Subgroup.commutator_def]
  congr 1
  ext x
  constructor
  · rintro ⟨u, v, rfl⟩
    obtain ⟨a, rfl⟩ := UStarProjection_surjective hUT u
    refine ⟨a, a.property, v, v.property, ?_⟩
    rw [d.starAction_UStarProjection hUT]
    rfl
  · rintro ⟨u, hu, v, hv, rfl⟩
    refine ⟨UStarProjection D hUT ⟨u, hu⟩, ⟨v, hv⟩, ?_⟩
    rw [d.starAction_UStarProjection hUT]
    rfl

/-- The faithful star action and the induced two-core quotient model agree,
with starred generation now proved for the original I, g and h. -/
theorem coreQuotientEquiv_starAction (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (i : I D g h) (v : Fin 3 → F) :
    (d.starAction (d.IStarProjection hUT (d.star_I_eq_star_L hUT hf) i)
      (Multiplicative.ofAdd v)).toAdd =
        (d.coreQuotientEquiv hUT (d.star_I_eq_star_L hUT hf)
          (QuotientGroup.mk' (pCore 2 (I D g h)) i)).val *ᵥ v := by
  rw [d.coreQuotientEquiv_mk]
  exact d.starAction_on_L _ v

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree
