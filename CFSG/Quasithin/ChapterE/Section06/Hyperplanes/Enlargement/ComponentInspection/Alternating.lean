module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection.Reduction
public import Theory.SpecificGroups.Alternating.SmallFixedComponents

/-!
# The alternating inspections in E.6.22

An order-two automorphism subgroup has the same fixed subgroup as its
nonidentity element. The intrinsic A₆ and A₇ fixed-group calculations therefore
give the exact enlargement inspection contracts, including actual A₅
isomorphisms. Their proofs establish the stronger statements for every
involution; the supplied pointwise fixed Sylow subgroup need not be used.

The A₆ exclusion also holds for its perfect central three-cover. In the
source assembly both degree-six and degree-seven central three-covers are
excluded by `not_three_cover`, using E.6.21 and relative component
subnormality. Thus no central-quotient identification is substituted for
an isomorphism of the smaller component. The final theorem discharges the
two alternating inputs of `component_lift_of_inspections` while retaining
its other source inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.22,
printed p.254 (PDF p.265).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
open ComponentBalance Components Chapter1.Section02.LocalModels
universe u
variable {Y : Type u} [Group Y] [Finite Y]

private theorem exists_fixed_involution (P : Subgroup (MulAut Y)) (hP : Nat.card P = 2) :
    ∃ a : MulAut Y, orderOf a = 2 ∧
      FixedPoints.subgroup P Y = a.fixedSubgroup := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 (by rw [hP])
  have hz : zpowers (a : MulAut Y) = P := by
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr a.property)
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ha, hP]
  refine ⟨a, (Subgroup.orderOf_coe a).trans ha, ?_⟩
  ext x
  rw [MulAut.mem_fixedSubgroup]
  constructor
  · intro hx
    exact hx a
  · intro hx
    have hle : zpowers a.val ≤ MulAction.stabilizer (MulAut Y) x :=
      zpowers_le.mpr hx
    intro b
    exact hle (hz.symm ▸ b.property)

/-- The degree-six model has no component in any Sylow-central involution fixed group. -/
theorem alternating_six_noCentralInvolutionComponent
    (hY : IsAlternating Y 6) : NoCentralInvolutionComponent Y := by
  obtain ⟨e⟩ := hY
  intro P hP _ D hD
  obtain ⟨a, ha, hf⟩ := exists_fixed_involution P hP
  rw [hf] at hD
  exact alternatingGroup.SmallFixedComponents.six_model_no_component e a ha D hD

/-- Perfect central three-covers of A₆ satisfy the same exclusion. -/
theorem alternating_six_cover_noCentralInvolutionComponent
    (hY : IsAlternatingCover Y 6) : NoCentralInvolutionComponent Y := by
  let _ : IsQuasisimple Y := hY.1
  obtain ⟨e⟩ := hY.2.2
  intro P hP _ D hD
  obtain ⟨a, ha, hf⟩ := exists_fixed_involution P hP
  rw [hf] at hD
  exact alternatingGroup.SmallFixedComponents.six_cover_no_component e a ha D hD

/-- The exceptional component is actually A₅ under the given A₇ model isomorphism. -/
theorem alternating_seven_centralInvolutionFive
    (hY : IsAlternating Y 7) : CentralInvolutionFive Y := by
  obtain ⟨e⟩ := hY
  intro P hP _ D hD
  obtain ⟨a, ha, hf⟩ := exists_fixed_involution P hP
  rw [hf] at hD
  exact alternatingGroup.SmallFixedComponents.seven_component_equiv e a ha D hD

variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V : Subgroup G}

/-- E.6.22 component lifting with both alternating inspections discharged.
The remaining source and nonalternating model inputs are explicit. -/
theorem component_lift_of_nonalternating_inspections
    [IsElementaryAbelian 2 V] (h : HypothesisE61 K T M V) (h15 : HypothesisE615 V)
    (hbalance : EarlierBalance K) (ho : OddCoreFree V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      ¬ X ≤ M ∧ ComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X)
    (hborel : ∀ (X : Subgroup G), IsQuasisimple X → ∀ n : ℕ, n ≤ 2 →
      BorelComponentModel X n → NoCentralInvolutionComponent X)
    (hsymplectic : ∀ (X : Subgroup G), IsQuasisimple X → ∀ n : ℕ, n ≤ 2 →
      SymplecticDerivedModel X n → NoCentralInvolutionComponent X)
    (hlinear : ∀ (X : Subgroup G), IsQuasisimple X →
      ClassicalGroup.IsPSL X 4 2 → NoCentralInvolutionComponent X)
    (hodd : ∀ (X : Subgroup G), IsQuasisimple X →
      ((∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL X 2 p) ∨
        ClassicalGroup.IsPSL X 3 3 ∨ Nonempty (X ≃* Sporadic.Mathieu.M11)) →
      NoCentralInvolutionComponent X) : ComponentLiftAlternative M V := by
  exact component_lift_of_inspections h h15 hbalance ho h68 hborel hsymplectic hlinear
    (fun _ _ hm => alternating_six_noCentralInvolutionComponent hm)
    (fun _ _ hm => alternating_seven_centralInvolutionFive hm) hodd

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
