module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.Representation.BinaryOffender.Ratio
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.BinaryOffender.IrreducibleSection

/-!
# The numerical hypotheses of the full representation restrictions

The cubic ratio is the infimum over nontrivial elementary actors satisfying
[V,A,A,A]=0. We prove this commutator interpretation, attainment for finite
groups, and the comparison with the distinct quadratic ratio. The cubic
bound at one gives an offender, hence an actual best offender, on the same
representation.

The common B.4 input retains finite groups and modules, SQTK, faithfulness,
quasisimplicity of the entire generalized Fitting subgroup, and its
irreducibility. B.4.2 adds the best offender; B.4.5 adds the cubic bound.
These structures encode hypotheses only. No classification alternative,
FF exclusion or fixation assertion is assumed or proved by them.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), B.4.1--5,
printed pp.85--87, and the application in 15.3.65, p.1152.
-/

@[expose] public section

open Representation Representation.BinaryOffender Subgroup
open scoped ENNReal

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases

universe u v
variable {D : Type u} {V : Type v} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V]

/-- The displacement operator, so iterated commutators are compositions. -/
def displacement (ρ : Representation (ZMod 2) D V) (a : D) : V →ₗ[ZMod 2] V :=
  ρ a - LinearMap.id

/-- B.4.1's cubic condition is [V,A,A,A]=0. -/
def IsCubic (ρ : Representation (ZMod 2) D V) (A : Subgroup D) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ v : V,
    displacement ρ a (displacement ρ b (displacement ρ c v)) = 0

/-- The cubic ratio of B.4.1, separate from the quadratic ratio of B.1.1. -/
noncomputable def cubicRatio (ρ : Representation (ZMod 2) D V) : ℝ≥0∞ :=
  ⨅ (A : Subgroup D) (_ : IsElementaryTwo A ∧ IsCubic ρ A), actionRatio ρ A

theorem isCubic_of_isQuadratic {ρ : Representation (ZMod 2) D V} {A : Subgroup D}
    (h : IsQuadratic ρ A) : IsCubic ρ A := by
  intro a ha b hb c hc v
  have hz : displacement ρ b (displacement ρ c v) = 0 :=
    sub_eq_zero.mpr (h b hb c hc v)
  rw [hz, map_zero]

theorem cubicRatio_le_quadraticRatio (ρ : Representation (ZMod 2) D V) :
    cubicRatio ρ ≤ quadraticRatio ρ := by
  apply le_iInf
  intro A
  apply le_iInf
  intro hA
  exact iInf_le_of_le A (iInf_le_of_le ⟨hA.1, isCubic_of_isQuadratic hA.2⟩ le_rfl)

theorem isCubic_iff_commutator_eq_bot (ρ : Representation (ZMod 2) D V)
    (A : Subgroup D) : IsCubic ρ A ↔
      subspaceCommutator ρ (subspaceCommutator ρ (subspaceCommutator ρ ⊤ A) A) A = ⊥ := by
  constructor
  · intro h
    rw [subspaceCommutator_eq_bot_iff]
    intro v hv a
    have hv' : v ∈ LinearMap.ker (displacement ρ a) := by
      apply (show subspaceCommutator ρ (subspaceCommutator ρ ⊤ A) A ≤
          LinearMap.ker (displacement ρ a) from ?_) hv
      apply Submodule.span_le.mpr
      rintro _ ⟨b, hb, w, hw, rfl⟩
      have hw' : w ∈ LinearMap.ker ((displacement ρ a).comp (displacement ρ b)) := by
        apply (show subspaceCommutator ρ ⊤ A ≤
            LinearMap.ker ((displacement ρ a).comp (displacement ρ b)) from ?_) hw
        apply Submodule.span_le.mpr
        rintro _ ⟨c, hc, x, _, rfl⟩
        exact h a a.property b hb c hc x
      exact hw'
    exact sub_eq_zero.mp hv'
  · intro h a ha b hb c hc v
    have hc' : ρ c v - v ∈ subspaceCommutator ρ ⊤ A :=
      Submodule.subset_span ⟨c, hc, v, Submodule.mem_top, rfl⟩
    have hb' : displacement ρ b (ρ c v - v) ∈
        subspaceCommutator ρ (subspaceCommutator ρ ⊤ A) A :=
      Submodule.subset_span ⟨b, hb, ρ c v - v, hc', rfl⟩
    exact sub_eq_zero.mpr ((subspaceCommutator_eq_bot_iff _ _ _).mp h hb' ⟨a, ha⟩)

theorem cubicRatio_le_iff [Finite D] (ρ : Representation (ZMod 2) D V)
    {r : ℝ≥0∞} (hr : r ≠ ⊤) :
    cubicRatio ρ ≤ r ↔
      ∃ A, IsElementaryTwo A ∧ IsCubic ρ A ∧ actionRatio ρ A ≤ r := by
  classical
  constructor
  · intro h
    let S := {A : Subgroup D // IsElementaryTwo A ∧ IsCubic ρ A}
    by_cases hS : Nonempty S
    · let : Nonempty S := hS
      obtain ⟨A, hA⟩ := exists_eq_ciInf_of_finite (f := fun A : S => actionRatio ρ A.val)
      rw [iInf_subtype] at hA
      exact ⟨A.val, A.property.1, A.property.2, hA.trans_le h⟩
    · have htop : cubicRatio ρ = ⊤ := by
        apply iInf_eq_top.mpr
        intro A
        apply iInf_eq_top.mpr
        intro hA
        exact (hS ⟨⟨A, hA⟩⟩).elim
      exact (hr (top_le_iff.mp (htop ▸ h))).elim
  · rintro ⟨A, hA, hc, hle⟩
    exact (iInf_le_of_le A (iInf_le_of_le ⟨hA, hc⟩ le_rfl)).trans hle

/-- Even a cubic actor of ratio at most one is an offender. This does not
identify the quadratic and cubic ratios or require cubic actors to be quadratic. -/
theorem isFFModule_of_cubicRatio_le_one [Finite D]
    (ρ : Representation (ZMod 2) D V) (h : cubicRatio ρ ≤ 1) : IsFFModule ρ := by
  obtain ⟨A, hA, _, hr⟩ := (cubicRatio_le_iff ρ (by simp)).mp h
  exact ⟨A, hA, (actionRatio_le_one_iff ρ hA).mp hr⟩

/-- The common genuine input of B.4.2 and B.4.5. In particular the whole
generalized Fitting subgroup, rather than an arbitrary component, is quasisimple.
Finiteness of both the group and module is retained in the parameters. -/
structure B4Hypotheses [Finite D] [Finite V]
    (𝒦 : GroupClass.{u}) (ρ : Representation (ZMod 2) D V) : Prop where
  sqtk : IsSQTK 𝒦 D
  faithful : Function.Injective ρ
  quasisimple : Theory.GroupTheory.IsQuasisimple (Theory.GroupTheory.generalizedFitting D)
  irreducible : IsIrreducible (ρ.comp (Theory.GroupTheory.generalizedFitting D).subtype)

/-- B.4.2 additionally requires an actual member of P(G,V). -/
structure B42Hypotheses [Finite D] [Finite V]
    (𝒦 : GroupClass.{u}) (ρ : Representation (ZMod 2) D V) (A : Subgroup D) : Prop
    extends B4Hypotheses 𝒦 ρ where
  bestOffender : IsBestOffender ρ A

/-- B.4.5 assumes the cubic bound. Its conclusions distinguish q from q-hat. -/
structure B45Hypotheses [Finite D] [Finite V]
    (𝒦 : GroupClass.{u}) (ρ : Representation (ZMod 2) D V) : Prop
    extends B4Hypotheses 𝒦 ρ where
  cubic_bound : cubicRatio ρ ≤ 2

/-- The stronger quadratic bound in 15.3.64 discharges B.4.5's numerical input.
Faithfulness, SQTK and irreducibility must still be supplied for this exact action. -/
theorem B4Hypotheses.with_quadratic_bound [Finite D] [Finite V]
    {𝒦 : GroupClass.{u}} {ρ : Representation (ZMod 2) D V}
    (h : B4Hypotheses 𝒦 ρ) (hq : quadraticRatio ρ ≤ 2) : B45Hypotheses 𝒦 ρ :=
  ⟨h, (cubicRatio_le_quadraticRatio ρ).trans hq⟩

/-- An FF-module supplies the explicit best offender required by B.4.2. -/
theorem B4Hypotheses.exists_bestOffender [Finite D] [Finite V]
    {𝒦 : GroupClass.{u}} {ρ : Representation (ZMod 2) D V}
    (h : B4Hypotheses 𝒦 ρ) (hff : IsFFModule ρ) :
    ∃ A, B42Hypotheses 𝒦 ρ A := by
  obtain ⟨A, hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp hff
  exact ⟨A, h, hA⟩

/-- The first alternative in B.4.5 really supplies B.4.2's best-offender
hypothesis on this same finite faithful representation. -/
theorem B4Hypotheses.exists_B42_of_cubic_le_one [Finite D] [Finite V]
    {𝒦 : GroupClass.{u}} {ρ : Representation (ZMod 2) D V}
    (h : B4Hypotheses 𝒦 ρ) (hq : cubicRatio ρ ≤ 1) :
    ∃ A, B42Hypotheses 𝒦 ρ A :=
  h.exists_bestOffender (isFFModule_of_cubicRatio_le_one ρ hq)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
