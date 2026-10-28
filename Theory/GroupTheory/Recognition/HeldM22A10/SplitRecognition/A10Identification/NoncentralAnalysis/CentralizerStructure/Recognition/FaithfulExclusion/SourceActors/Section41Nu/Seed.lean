module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Relations

/-!
# The initial order-three actor in Held's Section 4.1

This interface states the relations constructed in the first paragraph of the
proof, including inversion by mu-prime. It does not assume that nu commutes
with xi. Its ambient existence requires the earlier normalizer analysis in
Sections 2.10--2.11. The consequences below prove the actions on pi*mu and
tau*lambda and show that mu is conjugate to the chosen lambda: conjugate by
tau-prime, nu, and mu-prime*tau-prime, successively. Thus pi--mu nonfusion
already supplies the required lambda normalization from any initial actor.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 4.1, printed p.232.
Conjugation is x^g = g⁻¹*x*g. No existence is asserted by this interface.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion

universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The first paragraph of Held 4.1, before the compatibility with xi is proved. -/
public structure NuSeedRelations (b : Bit) where
  nu : G
  cube : nu ^ 3 = 1
  mu_commute : Commute nu (D.a10ModelEmbedding e Coordinates.mu)
  lam_commute : Commute nu (D.a10ModelEmbedding e (normalizedLam b))
  pi_nu : nu⁻¹ * D.a10ModelEmbedding e Coordinates.pi * nu =
    D.a10ModelEmbedding e (Coordinates.pi * Coordinates.tau * normalizedLam b)
  tau_nu : nu⁻¹ * D.a10ModelEmbedding e Coordinates.tau * nu =
    D.a10ModelEmbedding e (Coordinates.pi * Coordinates.mu * normalizedLam b)
  mup_inverts : D.a10ModelEmbedding e Coordinates.mup * nu *
    D.a10ModelEmbedding e Coordinates.mup = nu⁻¹

variable {D e}

private theorem conj_eq_of_commute {x g : G} (h : Commute g x) : g⁻¹ * x * g = x := by
  rw [mul_assoc, ← h.eq, inv_mul_cancel_left]

/-- The initial actor already has the required action on pi*mu. -/
public theorem NuSeedRelations.corePi_conjugation {b : Bit} (n : NuSeedRelations D e b) :
    n.nu⁻¹ * D.a10ModelEmbedding e corePi * n.nu =
      D.a10ModelEmbedding e (corePi * coreTau b) := by
  let f := D.a10ModelEmbedding e
  have hlocal : ∀ b,
      (Coordinates.pi * Coordinates.tau * normalizedLam b) * Coordinates.mu =
        corePi * coreTau b := by decide +kernel
  change n.nu⁻¹ * f corePi * n.nu = _
  calc
    _ = (n.nu⁻¹ * f Coordinates.pi * n.nu) *
        (n.nu⁻¹ * f Coordinates.mu * n.nu) := by
      rw [corePi, map_mul]
      group
    _ = f (corePi * coreTau b) := by
      rw [n.pi_nu, conj_eq_of_commute n.mu_commute, ← map_mul, hlocal b]

/-- Multiplying the source action on tau by its fixed lambda gives the
required action on tau*lambda. -/
public theorem NuSeedRelations.coreTau_conjugation {b : Bit} (n : NuSeedRelations D e b) :
    n.nu⁻¹ * D.a10ModelEmbedding e (coreTau b) * n.nu =
      D.a10ModelEmbedding e corePi := by
  let f := D.a10ModelEmbedding e
  have hlocal : ∀ b,
      (Coordinates.pi * Coordinates.mu * normalizedLam b) * normalizedLam b =
        corePi := by decide +kernel
  change n.nu⁻¹ * f (coreTau b) * n.nu = _
  calc
    _ = (n.nu⁻¹ * f Coordinates.tau * n.nu) *
        (n.nu⁻¹ * f (normalizedLam b) * n.nu) := by
      rw [coreTau, map_mul]
      group
    _ = f corePi := by
      rw [n.tau_nu, conj_eq_of_commute n.lam_commute, ← map_mul, hlocal b]

/-- The chosen lambda belongs to mu's ambient conjugacy class. This uses an
explicit conjugating word, without assuming the normalizer order. -/
public theorem NuSeedRelations.mu_isConj_lam {b : Bit} (n : NuSeedRelations D e b) :
    IsConj (D.a10ModelEmbedding e Coordinates.mu)
      (D.a10ModelEmbedding e (normalizedLam b)) := by
  let f := D.a10ModelEmbedding e
  have hfirst : Coordinates.taup⁻¹ * Coordinates.mu * Coordinates.taup = corePi := by
    decide +kernel
  have hlast : ∀ b : Bit,
      (Coordinates.mup * Coordinates.taup)⁻¹ * (corePi * coreTau b) *
        (Coordinates.mup * Coordinates.taup) = normalizedLam b := by decide +kernel
  have h₁ : IsConj (f Coordinates.mu) (f corePi) :=
    isConj_iff.mpr ⟨f Coordinates.taup⁻¹, by
      simpa only [inv_inv, ← map_inv, ← map_mul] using congrArg f hfirst⟩
  have h₂ : IsConj (f corePi) (f (corePi * coreTau b)) :=
    isConj_iff.mpr ⟨n.nu⁻¹, by simpa only [inv_inv] using n.corePi_conjugation⟩
  have h₃ : IsConj (f (corePi * coreTau b)) (f (normalizedLam b)) :=
    isConj_iff.mpr ⟨(f (Coordinates.mup * Coordinates.taup))⁻¹, by
      simpa only [inv_inv, ← map_inv, ← map_mul] using congrArg f (hlast b)⟩
  exact (h₁.trans h₂).trans h₃

/-- Lambda normalization follows from a seed and the original nonfusion
hypothesis; it need not be imposed as another seed field. -/
public theorem NuSeedRelations.lambda_nonfusion {b : Bit} (n : NuSeedRelations D e b)
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) :
    ¬ IsConj D.z (D.a10ModelEmbedding e (normalizedLam b)) :=
  fun h => hfusion (h.trans n.mu_isConj_lam.symm)

/-- The nontrivial action makes the seed an element of order exactly three. -/
public theorem NuSeedRelations.orderOf_nu {b : Bit} (n : NuSeedRelations D e b) :
    orderOf n.nu = 3 := by
  apply orderOf_eq_prime
  · exact n.cube
  · intro h
    have he := n.coreTau_conjugation
    rw [h, inv_one, one_mul, mul_one] at he
    have hlocal : ∀ b, coreTau b ≠ corePi := by decide +kernel
    exact hlocal b (D.a10ModelEmbedding_injective e he)

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
