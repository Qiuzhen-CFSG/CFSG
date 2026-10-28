module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction.Relations

/-!
# Intermediate elements in Held's first actor construction

`USeed` records the exact order and four actions obtained from the local
normalizer at the start of the proof on printed p.233. `UCentralizedSeed`
also records the result of conjugating by an element of the four-group
`<mu, lambda>` to centralize tau-prime. These are explicit intermediate
inputs; their existence requires the corresponding construction arguments.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 4.2, printed p.233.
The source convention is x^g = g⁻¹*x*g.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The four cyclic actions before either normalization in Held 4.2. -/
public structure USeed where
  u : G
  order : orderOf u = 3
  pi_u : u⁻¹ * pi D e * u = tau D e
  tau_u : u⁻¹ * tau D e * u = pi D e * tau D e
  mu_u : u⁻¹ * mu D e * u = lam D e
  lam_u : u⁻¹ * lam D e * u = mu D e * lam D e

/-- The same actions after choosing a conjugate centralizing tau-prime. -/
public structure UCentralizedSeed extends USeed D e where
  tau'_commute : Commute u (tau' D e)

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
