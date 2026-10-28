module

public import Theory.SpecificGroups.Monster.Construction.NOctad.Blocks
public import Theory.SpecificGroups.Monster.Construction.CInvariance

/-!
# The literal local restriction required of an octad extension

The extension equation uses `g : N1`, its literal inclusion in `N`, the
proved map `n1ToC`, and the existing Griess-space inclusion. Any genuine
representation satisfying this equation kills `K` and hence descends to the
actual `N/K`. Its restriction to `N1` preserves both actual source forms.

The coordinate-permutation condition records the incidence information on
octads needed to transport the support condition for the cubic in 29.14.
It is stronger than an arbitrary permutation of block names. No existence
of an extension, or invariance under all of `N`, is asserted here.

Source: Aschbacher, *Sporadic Groups*, 29.13(5), 29.14 and 30.1,
printed pp. 160–163. The remaining extension construction must supply the
representation and discharge these explicit hypotheses.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad
open LocalC LocalC.ShortFamilies TrialitySpin
open Atlas.Codes Atlas.Fischer

/-- Agreement with the actual local action, through the fixed inclusion. -/
def ExtendsLocal (ρ : Representation ℝ N Space) : Prop :=
  ∀ (g : N1) (v : Space), inclusion (ρ g.val v) =
    cRepresentation (n1ToC g) (inclusion v)

/-- Source block transport comes from one permutation of the 24 coordinates
for each actor, so it preserves octad sums and intersection sizes. -/
def PermutesOctadBlocks (ρ : Representation ℝ N Space) : Prop :=
  ∀ g : N, ∃ σ : Equiv.Perm Omega, ∀ c : Octad, ∃ d : Octad,
    (∀ i, d.val.val (σ i) = c.val.val i) ∧ (block c).map (ρ g) = block d

/-- The literal generator `psi_3(alpha_x)` occurring in 30.1. -/
def pointTriality (x : Omega) : N :=
  psiAut3N (parkerCocodeStandard (Submodule.Quotient.mk (pointWord x)))

/-- The defining point automorphism is exactly `alpha_x(d) = (-1)^epsilon_x(d) d`. -/
theorem pointAutomorphism_apply (x : Omega) (d : ParkerLoop) :
    (parkerCocodeStandard (Submodule.Quotient.mk (pointWord x))).val d =
      parkerSign (d.1.val x) d := by
  rw [parkerCocodeStandard_apply]
  change (d.1, d.2 + cocodeDualEquiv (Submodule.Quotient.mk (pointWord x)) d.1) = _
  rw [cocodeDualEquiv_mk]
  simp [binaryDot, pointWord, parkerSign]

theorem ExtendsLocal.killed (ρ : Representation ℝ N Space) (hρ : ExtendsLocal ρ)
    (k : N) (hk : k ∈ TrialitySpin.K) : ρ k = 1 := by
  let g : N1 := ⟨k, K_le_N1 hk⟩
  have hg : n1ToC g = 1 := by
    change g ∈ n1ToC.ker
    rw [n1ToC_kernel]
    exact hk
  apply LinearMap.ext
  intro v
  apply inclusion_injective
  change inclusion (ρ k v) = inclusion v
  rw [hρ g, hg, map_one]
  rfl

theorem ExtendsLocal.kernel (ρ : Representation ℝ N Space) (hρ : ExtendsLocal ρ) :
    TrialitySpin.K ≤ ρ.ker := fun k hk => hρ.killed ρ k hk

/-- A genuine extension descends to the literal triality quotient. -/
def quotientRepresentation (ρ : Representation ℝ N Space) (hρ : ExtendsLocal ρ) :
    Representation ℝ NQuotient Space :=
  QuotientGroup.lift TrialitySpin.K ρ (hρ.kernel ρ)

@[simp] theorem quotientRepresentation_mk (ρ : Representation ℝ N Space)
    (hρ : ExtendsLocal ρ) (g : N) :
    quotientRepresentation ρ hρ (nQuotientMap g) = ρ g := rfl

theorem ExtendsLocal.gamma_n1 (ρ : Representation ℝ N Space) (hρ : ExtendsLocal ρ)
    (g : N1) (v w : Space) : gamma (ρ g.val v) (ρ g.val w) = gamma v w := by
  rw [← gamma_inclusion, hρ g v, hρ g w, ← gamma_inclusion]
  exact cRepresentation_form (n1ToC g) (inclusion v) (inclusion w)

theorem ExtendsLocal.beta_n1 (ρ : Representation ℝ N Space) (hρ : ExtendsLocal ρ)
    (g : N1) (v w u : Space) :
    beta (ρ g.val v) (ρ g.val w) (ρ g.val u) = beta v w u := by
  rw [← beta_inclusion, hρ g v, hρ g w, hρ g u, ← beta_inclusion]
  exact CInvariance.cRepresentation_beta (n1ToC g) (inclusion v) (inclusion w) (inclusion u)

end Sporadic.Monster.Construction.NOctad
