module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.Contracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Section
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.NormalizationObstruction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.Assembly
import Mathlib.Tactic.FinCases

/-!
# Normalization and conditional construction of compatible A₆ geometry

The two published coordinate lists agree. We bridge them before reusing
the proved generation theorem and the local centralizer order.

The current `SixLocalData` cannot be constructed: its memberships of both
pi*mu and pi*lambda in A imply that the nonidentity element mu*lambda lies
in A and in <mu,lambda>, contradicting `A_disjoint`. This obstruction is
independent of finiteness, simplicity, fusion and the normal A6 section.
It is not a proof of the intended existence theorem.

Held's printed Lemma 4.2 has **tau*lambda**, rather than pi*lambda, among
the marked elements of A. `SourceContracts` preserves the old interface
and supplies this corrected marking.

The imported `NormalizationObstruction` proves a separate issue with the
fixed-coordinate existence target: Held 2.8 requires a choice between xi
and pi*xi. A centralizer automorphism exchanges these while fixing mu,
and the two resulting isomorphisms cannot both admit source six-point data.
`SectionTransport` and `SectionPlacement` retain the valid intrinsic A₆,
dihedral decomposition and disjointness arguments from the supplied section.

`Normalization` proves the source's marking choices, preserving mu and its
actual A₆ section. `RootCentralization` proves 5.2 from a marked section and
compatible actors. `Assembly` constructs the corrected source data from
those two remaining inputs; their existence is not asserted here.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 4.2, printed p.232 (last two lines).
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry
namespace SixConstruction

public theorem modelElement_eq_noncentralGenerator (i : Fin 8) :
    modelElement i = NoncentralAnalysis.Coordinates.generators i := by
  fin_cases i <;> rfl

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

public theorem element_eq_noncentralGenerator_image (i : Fin 8) :
    element D e i = D.a10ModelEmbedding e (NoncentralAnalysis.Coordinates.generators i) := by
  rw [element, modelElement_eq_noncentralGenerator]

/-- Generation of the entire specified centralizer, in the geometry coordinates. -/
public theorem coordinates_generate :
    closure (Set.range (element D e)) = D.centralizer := by
  change closure (Set.range (fun i => D.a10ModelEmbedding e (modelElement i))) = D.centralizer
  simpa only [modelElement_eq_noncentralGenerator] using
    NoncentralAnalysis.Coordinates.ambient_generators_generate D e

public theorem centralizer_mu_intersection_card :
    Nat.card ↥(D.centralizer ⊓ centralizer ({mu D e} : Set G)) = 64 := by
  rw [mu_eq]
  exact NoncentralAnalysis.Coordinates.ambient_intersection_card D e

public theorem mu_mul_lam_ne_one : mu D e * lam D e ≠ 1 := by
  intro h
  have hm : modelElement 1 * modelElement 6 = 1 := by
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul, map_one, mu, lam, element] using h
  have hn : modelElement 1 * modelElement 6 ≠ 1 := by decide +kernel
  exact hn hm

/-- The two pi-marked memberships conflict with the disjointness clause.
The source uses tau*lambda for the second membership. -/
public theorem incompatible_pi_markings (A : Subgroup G)
    (hdisjoint : Disjoint (closure ({mu D e, lam D e} : Set G)) A)
    (hpi_mu : pi D e * mu D e ∈ A) (hpi_lam : pi D e * lam D e ∈ A) : False := by
  have hmul : (pi D e * mu D e) * (pi D e * lam D e) = mu D e * lam D e := by
    calc
      _ = pi D e * (mu D e * pi D e) * lam D e := by simp only [mul_assoc]
      _ = pi D e * (pi D e * mu D e) * lam D e := by rw [(commute_pi D e 1).eq]
      _ = mu D e * lam D e := by
        rw [← mul_assoc (pi D e), ← pow_two, element_square D e 0 (by decide), one_mul]
  have hA : mu D e * lam D e ∈ A := by
    rw [← hmul]
    exact A.mul_mem hpi_mu hpi_lam
  have hK : mu D e * lam D e ∈ closure ({mu D e, lam D e} : Set G) :=
    mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  exact mu_mul_lam_ne_one D e (disjoint_def.mp hdisjoint hK hA)

/-- A checked obstruction to the published interface, not a source theorem.
Correcting `pi_lam_mem` is required before an existence theorem can be proved. -/
public theorem not_nonempty_sixLocalData : ¬ Nonempty (SixLocalData D e) := by
  rintro ⟨L⟩
  exact incompatible_pi_markings D e L.A L.A_disjoint L.pi_mu_mem L.pi_lam_mem

end SixConstruction
end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry
