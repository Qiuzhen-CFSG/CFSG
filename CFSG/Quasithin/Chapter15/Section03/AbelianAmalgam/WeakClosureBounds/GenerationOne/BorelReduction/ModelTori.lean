module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.SourceCases
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.HigherRankTori

/-!
# Tori from all the surviving E.2.2 models

Each actual model/Borel pair supplies a concrete field-unit injection. The
component lies in the two-residual by the proved conjugate-span identity.
Transport to H/J followed by cyclic lifting gives an injection into the
literal image of M ∩ O²(H) in H/O₂(H). In the unitary branch the field is
constructed as the Hermitian fixed subfield, of order 2^f, while the matrix
field has order (2^f)^2. In the symplectic branch the torus is already in Sp₄′.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.2.2,
printed pp.215–216, and the first paragraph of 15.3.65's proof on p.1152.
-/

@[expose] public section
open Subgroup
open BenderSuzuki.PFAppendixIII
noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction
variable {G : Type*} [Group G] [Finite G]

/-- A copy of the defining fixed-field unit group in the actual residual overlap. -/
def HasBorelTorus (H M : Subgroup G) (f : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ f ∧
    ∃ j : Fˣ →* borelImage H M, Function.Injective j

private theorem torus_of_pair
    {F X : Type*} [Field F] [Finite F] [Group X]
    {H M K : Subgroup G} {B : Subgroup X}
    (hcore : pCore 2 H ≤ sourceKernel H M) (hKR : K ≤ residual H)
    (hp : SourceCases.ModelBorelPair H M K B)
    (i : Fˣ →* B) (hi : Function.Injective i) :
    ∃ j : Fˣ →* borelImage H M, Function.Injective j := by
  obtain ⟨e⟩ := hp.borel_equiv
  exact lift_component_borel_torus B hcore hKR e i hi

/-- The PSL₂ and Suzuki models supply their concrete tori before any parity deduction. -/
theorem SourceCases.ExchangedModel.borel_torus
    {H M K : Subgroup G} {f : ℕ}
    (h : SourceCases.ExchangedModel H M K f)
    (hcore : pCore 2 H ≤ sourceKernel H M) (hKR : K ≤ residual H) :
    HasBorelTorus H M f := by
  rcases h with ⟨F, hF, hfin, hc, _, hcard, hp⟩ | ⟨m, hm, rfl, hp⟩
  · exact ⟨F, hF, hfin, hcard, torus_of_pair hcore hKR hp psl2Torus psl2Torus_injective⟩
  · refine ⟨BinaryGaloisField (2 * m + 1), inferInstance, inferInstance, ?_, ?_⟩
    · simpa [BinaryGaloisField] using GaloisField.card 2 (2 * m + 1) (by omega)
    · exact torus_of_pair hcore hKR hp (suzukiTorus m hm) (suzukiTorus_injective m hm)

/-- The torus uses the Hermitian fixed field, with its order proved from the matrix field. -/
theorem SourceCases.UnitaryModel.borel_torus
    {H M K : Subgroup G} {f : ℕ}
    (h : SourceCases.UnitaryModel H M K f)
    (hcore : pCore 2 H ≤ sourceKernel H M) (hKR : K ≤ residual H) :
    HasBorelTorus H M f := by
  obtain ⟨E, hE, hfin, hc, J, hJ, hf, hcard, hconj, _, hp⟩ := h
  exact ⟨unitaryFixedField J, inferInstance, inferInstance,
    unitaryFixedField_card J f (by omega) hcard hconj,
    torus_of_pair hcore hKR hp (psu3Torus J hJ) (psu3Torus_injective J hJ)⟩

/-- All three Bender families supply a torus in the actual residual overlap. -/
theorem SourceCases.BenderModel.borel_torus
    {H M K : Subgroup G} {f : ℕ}
    (h : SourceCases.BenderModel H M K f)
    (hcore : pCore 2 H ≤ sourceKernel H M) (hKR : K ≤ residual H) :
    HasBorelTorus H M f := by
  rcases h with h | h
  · exact h.borel_torus hcore hKR
  · exact h.borel_torus hcore hKR

/-- Both diagram cases supply a torus; Sp₄ retains its literal derived subgroup. -/
theorem SourceCases.DiagramModel.borel_torus
    {H M K T : Subgroup G} {f : ℕ}
    (h : SourceCases.DiagramModel H M K T f)
    (hcore : pCore 2 H ≤ sourceKernel H M) (hKR : K ≤ residual H) :
    HasBorelTorus H M f := by
  rcases h with ⟨F, hF, hfin, hc, _, hcard, e, hB, _⟩ |
      ⟨F, hF, hfin, hc, _, hcard, e, hB, _⟩
  · exact ⟨F, hF, hfin, hcard,
      torus_of_pair hcore hKR ⟨e, hB⟩ (psl3Torus F) (psl3Torus_injective F)⟩
  · exact ⟨F, hF, hfin, hcard,
      torus_of_pair hcore hKR ⟨e, hB⟩ sp4DerivedTorus sp4DerivedTorus_injective⟩

/-- The full E.2.2 reduction constructs the torus without a divisor or parity premise. -/
theorem SourceCases.Reduction.borel_torus
    {𝒦 : GroupClass} {H M K T : Subgroup G} {f : ℕ}
    (h : SourceCases.Reduction 𝒦 H M K T f) : HasBorelTorus H M f := by
  have hKR : K ≤ residual H := h.residual_eq ▸ le_conjugateSpanBy K T
  rcases h.cases with ⟨_, hm⟩ | ⟨_, hm⟩ | ⟨_, hm⟩
  · exact hm.borel_torus h.core_le hKR
  · exact hm.borel_torus h.core_le hKR
  · exact hm.borel_torus h.core_le hKR
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction
