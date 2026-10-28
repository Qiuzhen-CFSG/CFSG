module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SourceContracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.SectionPlacement

/-!
# Separate construction problems in Held's six-point geometry

The supplied normal A₆ section already determines the ambient subgroup,
its alternating identification, relative normality, dihedral complement,
and disjointness from the marked four-group. `MarkedSection` isolates the
remaining placement and symmetric-extension statements of 4.2.

`CompatibleActors` records the order-three elements of 4.1--4.2 after
the conjugate choice of v in 5.1. Its construction may take a marked
section as input. The centralization in 5.2 is not one of its fields.
These are intermediate contracts; neither structure asserts existence.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Sections 4.1--5.2, printed pp.232--236.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The missing marked placement of the actual section, with the source's tau*lambda. -/
public structure MarkedSection
    (s : NoncentralAnalysis.AlternatingSixSection
      (centralizer ({D.a10NoncentralInvolution e} : Set G))) where
  symmetricEquiv : (s.ambientSubgroup ⊔ zpowers (mu' D e) : Subgroup G) ≃* Perm (Fin 6)
  centralizes : s.ambientSubgroup ≤ centralizer ({mu D e, lam D e} : Set G)
  pi_mu_mem : pi D e * mu D e ∈ s.ambientSubgroup
  tau_lam_mem : tau D e * lam D e ∈ s.ambientSubgroup
  mu'_xi_mem : mu' D e * xi D e ∈ s.ambientSubgroup

/-- The actual compatible actors; their existence includes the adjustment in 5.1. -/
public structure CompatibleActors where
  u : G
  v : G
  u_order : orderOf u = 3
  v_order : orderOf v = 3
  u_v_commute : Commute u v
  mu_u : u⁻¹ * mu D e * u = lam D e
  lam_u : u⁻¹ * lam D e * u = mu D e * lam D e
  u_tau'_commute : Commute u (tau' D e)
  mu'_u : mu' D e * u * mu' D e = u⁻¹
  v_mu_commute : Commute v (mu D e)
  v_lam_commute : Commute v (lam D e)
  v_xi_commute : Commute v (xi D e)
  pi_v : v⁻¹ * pi D e * v = pi D e * tau D e * lam D e
  tau_v : v⁻¹ * tau D e * v = pi D e * mu D e * lam D e
  mu'_v : mu' D e * v * mu' D e = v⁻¹

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
