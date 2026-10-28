module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates.FiniteGroup.Generation.RootGroup
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates.FiniteGroup.Generation.Reachability
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates.FiniteGroup.Transport
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates.Transversal
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.Model

/-!
# Full generation by the fixed SU₃(5) matrix pair

The seed, its torus conjugate and their commutator generate the full root
group; the primitive torus witness then gives the whole literal Borel. The
checked transitions along the spanning tree put all 126 representatives in
the generated subgroup. Coset separation and the supplied canonical count
make them a full right transversal, using the actual entrywise group
isomorphism and its exact Borel-membership equivalence. Thus every element of
the special-unitary group, including its center, belongs to the closure.

`certificate_of_canonical_card` applies this result to the published canonical
certificate, with precisely the count and independent separation premises.
Source data: `Coordinates/source/upper_group_data.json`; root formulas:
Huppert II.10.12. The consumer is the cubic principal-series calculation for
Guralnick–Malle Proposition 4.3 and Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public noncomputable section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FiniteGroup
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private theorem representative_zero : representative 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change rawRepresentative 0 = 1
  decide +kernel

/-- The checked transitions and Borel containment put every fixed representative in the closure. -/
theorem representative_mem_closure (i : Fin 126) :
    representative i ∈ Subgroup.closure (Set.range generator) := by
  let H := Subgroup.closure (Set.range generator)
  apply generatorTarget_induction (fun i => representative i ∈ H) ?_ ?_ i
  · rw [representative_zero]
    exact H.one_mem
  · intro a j hj
    have hb : ((principalRootIn fieldForm (root a j) *
        principalTorusIn fieldForm (parameter ^ exponent a j) : standardBorel fieldForm) :
          standardGroup fieldForm) ∈ H := borel_le_closure (Subtype.property _)
    have hm := H.mul_mem (H.inv_mem hb)
      (H.mul_mem hj (Subgroup.subset_closure (Set.mem_range_self a)))
    rw [transition, inv_mul_cancel_left] at hm
    exact hm

/-- Transport the exact canonical left-coset count to a right transversal in the explicit field. -/
theorem representatives_cover_of_canonical_card
    (hcard : Nat.card TrivialCalculation.CanonicalPoints = 126)
    (hsep : ∀ i j, representative i * (representative j)⁻¹ ∈ standardBorel fieldForm → i = j) :
    ∀ g : standardGroup fieldForm, ∃ i, ∃ b : standardBorel fieldForm,
      g = b * representative i := by
  have hsep' : ∀ i j, canonicalEquiv (representative i) *
      (canonicalEquiv (representative j))⁻¹ ∈ standardBorel modelForm → i = j := by
    intro i j h
    apply hsep i j
    apply (canonicalEquiv_borel _).mp
    simpa only [map_mul, map_inv] using h
  have hcover := RightCoordinates.cover_of_card (standardBorel modelForm)
    (fun i => canonicalEquiv (representative i)) hsep'
    (show Nat.card (standardGroup modelForm ⧸ standardBorel modelForm) = Nat.card (Fin 126) by
      simpa only [Nat.card_fin] using hcard)
  intro g
  obtain ⟨i, b, hb⟩ := hcover (canonicalEquiv g)
  have hb' : canonicalEquiv.symm (b : standardGroup modelForm) ∈ standardBorel fieldForm := by
    apply (canonicalEquiv_borel _).mp
    simpa only [MulEquiv.apply_symm_apply] using b.property
  refine ⟨i, ⟨canonicalEquiv.symm b, hb'⟩, ?_⟩
  apply canonicalEquiv.injective
  simpa only [map_mul, MulEquiv.apply_symm_apply] using hb

/-- The fixed matrix pair generates the full actual SU₃(5), including its center. -/
theorem generators_generate_of_canonical_card
    (hcard : Nat.card TrivialCalculation.CanonicalPoints = 126)
    (hsep : ∀ i j, representative i * (representative j)⁻¹ ∈ standardBorel fieldForm → i = j) :
    Subgroup.closure (Set.range generator) = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨i, b, rfl⟩ := representatives_cover_of_canonical_card hcard hsep g
  exact (Subgroup.closure (Set.range generator)).mul_mem
    (borel_le_closure b.property) (representative_mem_closure i)

/-- Specialize the published canonical transport certificate with the proved full generation.
The independent coset-separation and canonical-count inputs remain explicit. -/
def certificate_of_canonical_card
    (hcard : Nat.card TrivialCalculation.CanonicalPoints = 126)
    (hsep : ∀ i j, representative i * (representative j)⁻¹ ∈ standardBorel fieldForm → i = j) :
    GroupCertificate := certificate hsep (generators_generate_of_canonical_card hcard hsep)
end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FiniteGroup
