module

public import CFSG.Quasithin.ChapterJ.Section04To05.Span.CenterCommutator
public import CFSG.Quasithin.ChapterJ.Section04To05.SteinbergCommutator.Closure
public import CFSG.Quasithin.ChapterJ.Section04To05.SteinbergCommutator.GroupCommutators
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The source subgroup W lies in the second Steinberg preimage

The actual U lies in S₂, and the second parabolic normalizes S₂, giving
W₀≤S₂. On HC, both R₂ and Q centralize modulo S₂: the first by the
defining Steinberg commutators and the second because Q/U is abelian.
Since T=R₂Q and Q₀=U[HC,T], also Q₀≤S₂. Thus W≤S₂, independently of
the order calculation for W.

Source: the containment part of Aschbacher–Smith J.4.3(2), printed p.441.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

private theorem HC_le_S : d.toTypeRuSetup.HC ≤ d.toTypeRuSetup.S := by
  have h : d.toTypeRuSetup.HC ≤ centralizer (d.V : Set G) :=
    inf_le_right.trans (centralizer_le (le_conjugateSpan _ _))
  rwa [d.ru1.centralizer_V] at h

/-- The Sylow displacements of HC lie in the original S₂. -/
theorem Plane.commutator_HC_T_le_S₂ :
    ⁅d.toTypeRuSetup.HC,(d.T : Subgroup G)⁆ ≤ p.S₂ := by
  have hR : p.R₂ ≤ commutatorPreimage (d.T : Subgroup G) d.toTypeRuSetup.HC p.S₂ :=
    le_commutatorPreimage p.R₂_le_T
      ((commutator_mono le_rfl (HC_le_S (d:=d))).trans p.commutator_R₂_S_le_S₂)
  have hQT : d.toTypeRuSetup.Q ≤ (d.T : Subgroup G) := by
    rw [← p.R₂_sup_Q]
    exact le_sup_right
  have hQ : d.toTypeRuSetup.Q ≤ commutatorPreimage (d.T : Subgroup G) d.toTypeRuSetup.HC p.S₂ :=
    le_commutatorPreimage hQT
      ((commutator_mono le_rfl d.toTypeRuSetup.HC_le_Q).trans
        (commutator_Q_Q_le_U.trans p.U_le_S₂))
  have hT : (d.T : Subgroup G) ≤ commutatorPreimage (d.T : Subgroup G) d.toTypeRuSetup.HC p.S₂ := by
    calc
      (d.T : Subgroup G) = p.R₂ ⊔ d.toTypeRuSetup.Q := p.R₂_sup_Q.symm
      _ ≤ commutatorPreimage (d.T : Subgroup G) d.toTypeRuSetup.HC p.S₂ := sup_le hR hQ
  rw [commutator_comm]
  exact (commutator_mono hT le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _
      (p.sylow_le_parabolic.trans p.S₂_normalized))

/-- The complete original central preimage is absorbed by S₂. -/
theorem Plane.Q₀_le_S₂ : Q₀ d ≤ p.S₂ := by
  rw [Q₀_eq_U_sup_commutator_HC_T]
  exact sup_le p.U_le_S₂ p.commutator_HC_T_le_S₂

/-- Every original L₂-conjugate of U lies in S₂. -/
theorem Plane.W₀_le_S₂ : p.W₀ ≤ p.S₂ := by
  rw [p.W₀_eq_conjugateSpanBy]
  exact conjugateSpanBy_le p.U_le_S₂ (p.L₂_le_parabolic.trans p.S₂_normalized)

/-- The source W is bounded by S₂ before its order is calculated. -/
theorem Plane.W_le_S₂ : p.W ≤ p.S₂ := by
  intro x hx
  change x ∈ (p.W : Set G) at hx
  rw [p.W_eq_product] at hx
  obtain ⟨a,ha,b,hb,rfl⟩ := hx
  exact p.S₂.mul_mem (p.W₀_le_S₂ ha) (p.Q₀_le_S₂ hb)

end CFSG.Quasithin.ChapterJ.RuSubgroup
