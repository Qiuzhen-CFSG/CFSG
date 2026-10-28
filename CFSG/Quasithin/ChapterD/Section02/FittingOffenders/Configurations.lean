module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.LinearBudget
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.InvariantLineReduction
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.FourDimensionalMarking
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.ThreePlaneSplitting

/-!
# The reduced module configurations in D.2.14

The earlier source reductions pass to the literal generated group `P ⊔ A`
on its faithful moved module. From precisely these `Reduced` hypotheses,
the invariant-line reduction produces a moved hyperplane fixed space and
excludes proper four-dimensional supports. The full-support branch constructs
two planes and a marked isomorphism with S₃ × S₃, with the original actor
exchanging the diagonal core factors. The other branch constructs three
invariant planes, each with one moved and one fixed dimension under the actor.

`Reduced.configurations` assembles both branches, including the actual product
and sum maps and the global cubic minimum three halves. No hyperplane witness,
support decomposition, or extra ratio premise remains. The preceding core and
fixed-space reductions remain explicit in `Reduced`; their construction for
the unreduced source theorem belongs to the Fitting-offender assembly.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
D.2.14, final paragraphs on printed p.187.
-/

public section
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
open Representation.BinaryOffender
open scoped ENNReal

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The full-support case has ratio three halves on the original module. -/
theorem reduced_full_support_ratio {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hlow : 1 < cubicRatio ρ)
    (hfull : FullSupport ρ P A) :
    fixedCodim ρ A = 3 ∧ cubicRatio ρ = 3 / 2 := by
  obtain ⟨_, _, _, hd⟩ := hfull
  exact h.small_dimension_ratio ρ hlow (by omega)

omit [Finite G] in
/-- Three invariant support planes with fixed lines give the global ratio
three halves, with no additional ratio or dimension premise. -/
theorem reduced_three_support_ratio {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (d : SupportFactors ρ P s) (hs : s = 3)
    (hstable : ∀ i, A ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ (d.ambient i)))
    (hlines : ∀ i, Module.finrank (ZMod 2)
      (subspaceCommutator ρ ⊤ (d.ambient i) ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) = 1) :
    fixedCodim ρ A = 3 ∧ cubicRatio ρ = 3 / 2 := by
  have hd := (d.fixedCodim_eq_of_fixed_lines ρ A hstable hlines).trans hs
  exact ⟨hd, h.cubicRatio_eq_of_fixedCodim_three ρ hd⟩

/-- Application to the literal `PA`, whose core and actor are the original
subgroups viewed inside their join. The earlier-source owner supplies the
faithful moved representation and the noncentralized hyperplane fixed space. -/
theorem local_generated_full_support_ratio (P A B : Subgroup G)
    (σ : Representation (ZMod 2) (P ⊔ A : Subgroup G) V) {s : ℕ}
    (h : Reduced σ (P.subgroupOf (P ⊔ A)) (A.subgroupOf (P ⊔ A)) s)
    (hBA : B ≤ A) (hrB : rank (B.subgroupOf (P ⊔ A)) = 1)
    (hn : subspaceCommutator σ (fixedSpace σ (B.subgroupOf (P ⊔ A)))
      (A.subgroupOf (P ⊔ A)) ≠ ⊥)
    (hfull : FullSupport σ (P.subgroupOf (P ⊔ A)) (A.subgroupOf (P ⊔ A))) :
    fixedCodim σ (A.subgroupOf (P ⊔ A)) = 3 ∧ cubicRatio σ = 3 / 2 := by
  apply reduced_full_support_ratio σ h _ hfull
  exact h.one_lt_ratio_of_moved_hyperplane σ (fun _ hb => hBA hb) hrB hn

/-- D.2.14(3),(6),(7) after the explicit core and fixed-space reductions.
The original core is the internal product of the constructed order-three
factors, and the original module is the internal sum of their moved planes.
Their marked actions satisfy exactly the two source alternatives. -/
theorem Reduced.configurations {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) :
    ∃ d : SupportFactors ρ P s, d.Alternatives A ∧
      fixedCodim ρ A = 3 ∧ cubicRatio ρ = 3 / 2 := by
  have hlow := h.one_lt_cubicRatio ρ
  rcases h.fullSupport_or_smallInvariantSupports ρ with hfull | hsmall
  · exact h.fullSupport_configuration ρ hlow hfull
  · obtain ⟨d, hs, hd⟩ := h.three_plane_splitting ρ hlow hsmall
    refine ⟨d, Or.inr ⟨hs, fun i => ⟨(hd i).1, (hd i).2.1⟩⟩, ?_⟩
    exact reduced_three_support_ratio ρ h d hs
      (fun i => (hd i).2.2.1) (fun i => (hd i).2.2.2)

end CFSG.Quasithin.ChapterD.FittingConfigurations
