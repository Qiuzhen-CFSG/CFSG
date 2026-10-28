module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.ModelInvolutions
import Mathlib.Tactic.FinCases

/-!
# Held's local coordinates inside the given centralizer

These are the concrete permutations from Section 1 of D. Held,
*A Characterization of some multiply transitive permutation groups, I*,
Illinois J. Math. 13 (1969), 224--240, DOI 10.1215/ijm/1256053756, p.225.
Indices 0 through 7 denote pi, mu, mu-prime, tau, tau-prime, rho, lambda, xi.
The model permutations are even and centralize (01)(23)(45)(67). Transport
through the marked centralizer embedding gives elements of the arbitrary
ambient group, with pi equal to the specified central involution and mu equal
to the specified noncentral involution. Finite model checks are kernel checked.

The coordinate choices originate in the checked LocalCoordinates probe in
Scratch/HeldA10Identification of workspace 39dd19cb126147e69d85ddf77a9d920e.
This module does not assert that the coordinates generate the centralizer.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry
open Equiv Subgroup

@[expose] public def modelPermutation : Fin 8 → Perm (Fin 10) := ![
  CentralizerModels.a10Permutation,
  swap 0 1 * swap 2 3,
  swap 0 1 * swap 4 5,
  swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7,
  swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7,
  swap 0 2 * swap 0 4 * swap 1 3 * swap 1 5,
  swap 0 2 * swap 1 3,
  swap 0 1 * swap 8 9]

@[expose] public def modelElement (i : Fin 8) : CentralizerModels.a10Centralizer :=
  ⟨⟨modelPermutation i, by
    rw [Equiv.Perm.mem_alternatingGroup]
    fin_cases i <;> decide +kernel⟩, by
    apply mem_centralizer_singleton_iff.mpr
    fin_cases i <;> decide +kernel⟩

noncomputable section

@[expose] public def element {G : Type*} [Group G] (D : LocalData G)
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) (i : Fin 8) : G :=
  D.a10ModelEmbedding e (modelElement i)

public abbrev pi {G : Type*} [Group G] (D : LocalData G)
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) := element D e 0
public abbrev mu {G : Type*} [Group G] (D : LocalData G)
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) := element D e 1
public abbrev mu' {G : Type*} [Group G] (D : LocalData G)
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) := element D e 2
public abbrev tau {G : Type*} [Group G] (D : LocalData G)
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) := element D e 3
public abbrev tau' {G : Type*} [Group G] (D : LocalData G)
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) := element D e 4
public abbrev rho {G : Type*} [Group G] (D : LocalData G)
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) := element D e 5
public abbrev lam {G : Type*} [Group G] (D : LocalData G)
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) := element D e 6
public abbrev xi {G : Type*} [Group G] (D : LocalData G)
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) := element D e 7

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

public theorem pi_eq [Finite G] : pi D e = D.z := by
  exact D.a10ModelEmbedding_central e

public theorem mu_eq : mu D e = D.a10NoncentralInvolution e := rfl

public theorem element_square (i : Fin 8) (hi : i ≠ 5) : element D e i ^ 2 = 1 := by
  have h : modelElement i ^ 2 = 1 := by fin_cases i <;> first | contradiction | decide +kernel
  exact (map_pow (D.a10ModelEmbedding e) _ _).symm.trans
    ((congrArg (D.a10ModelEmbedding e) h).trans (map_one _))

public theorem element_ne_one (i : Fin 8) : element D e i ≠ 1 := by
  intro h
  have hm : modelElement i = 1 := (D.a10ModelEmbedding_injective e)
    (h.trans (map_one _).symm)
  fin_cases i <;> revert hm <;> decide +kernel

public theorem commute_pi (i : Fin 8) : Commute (pi D e) (element D e i) := by
  exact (show Commute (modelElement 0) (modelElement i) from
    Subtype.ext (mem_centralizer_singleton_iff.mp (modelElement i).property).symm).map _

public theorem mu_commute_mu' : Commute (mu D e) (mu' D e) :=
  (show Commute (modelElement 1) (modelElement 2) by change _ * _ = _ * _; decide +kernel).map _

public theorem mu_commute_lam : Commute (mu D e) (lam D e) :=
  (show Commute (modelElement 1) (modelElement 6) by change _ * _ = _ * _; decide +kernel).map _

public theorem mu_commute_xi : Commute (mu D e) (xi D e) :=
  (show Commute (modelElement 1) (modelElement 7) by change _ * _ = _ * _; decide +kernel).map _

public theorem mu'_commute_xi : Commute (mu' D e) (xi D e) :=
  (show Commute (modelElement 2) (modelElement 7) by change _ * _ = _ * _; decide +kernel).map _

end
end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry
