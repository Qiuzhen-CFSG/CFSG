module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.Normalization
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.RootCentralization

/-!
# Assembly of Held's corrected six-point data

For the actual supplied normal A₆ section, the earlier transport and
placement lemmas give the alternating equivalence, disjointness, relative
normality and full centralizer decomposition. The marked placement supplies
the S₆ identification and the source's pi*mu, tau*lambda and mu-prime*xi
memberships. The compatible actors supply the remaining action relations;
their membership and the centralization in 5.2 are proved, not assumed.

This constructor is conditional on `MarkedSection` and `CompatibleActors`.
Their existence is still required for the source construction. Once both
are proved under the normalized nonfusion hypotheses, apply
`exists_source_normalized_section`, construct these two inputs there, and
use this constructor. The original mu and its actual A₆ remain unchanged.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Sections 4.1--5.2, pp.232--236.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (s : NoncentralAnalysis.AlternatingSixSection
    (centralizer ({D.a10NoncentralInvolution e} : Set G)))

/-- Conditional assembly, with the centralizer and root-action obligations discharged. -/
public noncomputable def sourceSixLocalDataOfMarkedSectionAndActors
    (m : MarkedSection D e s) (c : CompatibleActors D e) : Source.SixLocalData D e where
  u := c.u
  v := c.v
  A := s.ambientSubgroup
  alternatingEquiv := s.ambientAlternatingEquiv
  symmetricEquiv := m.symmetricEquiv
  u_order := c.u_order
  v_order := c.v_order
  u_v_commute := c.u_v_commute
  mu_u := c.mu_u
  lam_u := c.lam_u
  u_tau'_commute := c.u_tau'_commute
  mu'_u := c.mu'_u
  v_mu_commute := c.v_mu_commute
  v_lam_commute := c.v_lam_commute
  v_xi_commute := c.v_xi_commute
  pi_v := c.pi_v
  tau_v := c.tau_v
  mu'_v := c.mu'_v
  A_centralizes := m.centralizes
  A_disjoint := section_disjoint_four D e s
  mu'_normalizes := mu'_normalizes_section D e s
  centralizer_mu := section_centralizer_decomposition D e s
  pi_mu_mem := m.pi_mu_mem
  tau_lam_mem := m.tau_lam_mem
  v_mem := c.v_mem_section D e s
  mu'_xi_mem := m.mu'_xi_mem
  root_centralizes := c.root_centralizes_section D e s m

/-- Assembly uses exactly the supplied ambient alternating subgroup. -/
public theorem sourceSixLocalDataOfMarkedSectionAndActors_A
    (m : MarkedSection D e s) (c : CompatibleActors D e) :
    (sourceSixLocalDataOfMarkedSectionAndActors D e s m c).A = s.ambientSubgroup := by rfl

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
