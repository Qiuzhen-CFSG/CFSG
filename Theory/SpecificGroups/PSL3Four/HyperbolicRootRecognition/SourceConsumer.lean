module

public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.Recognition
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.Frames

/-!
# The actual root pair is UT₃(F₄)

The source IsType hypothesis produces the literal two hyperbolic factors,
their involution frames, and the two exact quotient reflections. Applying
intrinsic recognition therefore has no group-model or action assumption.
The stronger export retains the original ambient conjugators and their
pointwise action on R, as well as the two individually invariant elementary
sixteen-groups. This is the source 45.3 input to the normalizer assembly.

Source: Aschbacher, *Sporadic Groups* (1994), 45.3, printed pp.242–243.
-/

public section
open Subgroup
open Theory.GroupTheory.HyperbolicRecognition
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
variable {G : Type*} [Group G] [Finite G] {z : G} (P : RootPair z)

/-- The original source root product is the literal UT₃(F₄) group. -/
theorem nonempty_rootEquiv (h : IsType z) :
    Nonempty (P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root) := by
  obtain ⟨F₁,F₂⟩ := P.exists_hyperbolic_frames h
  obtain ⟨α,β⟩ := P.exists_hyperbolic_actors h
  exact HyperbolicRecognition.nonempty_rootEquiv (P.hyperbolicFactors h) F₁ F₂ α β

/-- The root realization retains the original ambient conjugators and their
exact action on each of the two normal elementary sixteen-groups. -/
theorem exists_actorRootRealization (h : IsType z) :
    ∃ a ∈ core z, ∃ b ∈ P.conjugateCore,
      ∃ α : (P.hyperbolicFactors h).FirstActor,
      ∃ β : (P.hyperbolicFactors h).SecondActor,
      ∃ _e : ActorRootRealization α.aut β.aut,
        (∀ x : P.R, (α.aut x : G) = a*x*a⁻¹) ∧
        (∀ x : P.R, (β.aut x : G) = b*x*b⁻¹) := by
  obtain ⟨F₁,F₂⟩ := P.exists_hyperbolic_frames h
  obtain ⟨a,ha,b,hb,α,β,hα,hβ⟩ := P.exists_hyperbolic_actors_marked h
  obtain ⟨e⟩ := nonempty_actorRootRealization (P.hyperbolicFactors h) F₁ F₂ α β
  exact ⟨a,ha,b,hb,α,β,e,hα,hβ⟩

/-- The original root product has precisely two elementary sixteen-groups. -/
theorem exists_two_root_planes (h : IsType z) :
    ∃ E₁ E₂ : Subgroup P.R,
      IsElementaryAbelian 2 E₁ ∧ IsElementaryAbelian 2 E₂ ∧
      Nat.card E₁ = 16 ∧ Nat.card E₂ = 16 ∧ E₁.Normal ∧ E₂.Normal ∧ E₁ ≠ E₂ ∧
      (E₁ ⊓ E₂).map P.R.subtype = P.E ∧
      (∀ E : Subgroup P.R, (IsElementaryAbelian 2 E ∧ Nat.card E = 16) ↔ E = E₁ ∨ E = E₂) := by
  obtain ⟨e⟩ := P.nonempty_rootEquiv h
  refine ⟨transportedPlane₁ e,transportedPlane₂ e,inferInstance,inferInstance,
    card_transportedPlane₁ e,card_transportedPlane₂ e,inferInstance,inferInstance,
    transportedPlanes_ne e,?_,transported_elementary_sixteen_iff e⟩
  rw [transportedPlanes_inf,P.R_center h]

end Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
