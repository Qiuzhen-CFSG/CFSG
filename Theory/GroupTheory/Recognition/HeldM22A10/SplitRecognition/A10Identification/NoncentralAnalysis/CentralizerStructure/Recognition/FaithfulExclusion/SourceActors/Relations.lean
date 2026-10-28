module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.Actors

/-!
# The two earlier normalizer constructions used by Held

These interfaces separate the ambient constructions in Sections 2.13 and 4.1
from membership in the canonical core in Section 4.2. The first construction
chooses xi and an element alpha of exponent three. The second chooses lambda
and an element nu cycling the nonidentity elements of the four-group generated
by pi*mu and tau*lambda. Neither interface assumes a core, an A6 section, or a
centralizer order. Their existence remains a separate source obligation.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Sections 2.13 and 4.1, pp.231--232.
The conjugation convention is x^g = g⁻¹*x*g.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
namespace FaithfulExclusion

universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The part of Section 2.13 used in the faithful-action argument. -/
public structure AlphaRelations (d : Bit) where
  alpha : G
  cube : alpha ^ 3 = 1
  corePi_commute : Commute alpha (D.a10ModelEmbedding e corePi)
  xi_alpha : alpha⁻¹ * D.a10ModelEmbedding e (normalizedXi d) * alpha =
    D.a10ModelEmbedding e Coordinates.mu
  pi_alpha : alpha⁻¹ * D.a10ModelEmbedding e Coordinates.pi * alpha =
    D.a10ModelEmbedding e (Coordinates.pi * normalizedXi d)

/-- The part of Section 4.1 used in the faithful-action argument. -/
public structure NuRelations (b d : Bit) where
  nu : G
  cube : nu ^ 3 = 1
  mu_commute : Commute nu (D.a10ModelEmbedding e Coordinates.mu)
  xi_commute : Commute nu (D.a10ModelEmbedding e (normalizedXi d))
  pi_nu : nu⁻¹ * D.a10ModelEmbedding e corePi * nu =
    D.a10ModelEmbedding e (corePi * coreTau b)
  tau_nu : nu⁻¹ * D.a10ModelEmbedding e (coreTau b) * nu =
    D.a10ModelEmbedding e corePi

variable {D e}

private theorem conj_eq_of_commute {x g : G} (h : Commute x g) : g⁻¹ * x * g = x := by
  rw [mul_assoc, h.eq, inv_mul_cancel_left]

public theorem AlphaRelations.mu_alpha {d : Bit} (a : AlphaRelations D e d) :
    a.alpha⁻¹ * D.a10ModelEmbedding e Coordinates.mu * a.alpha =
      D.a10ModelEmbedding e (Coordinates.mu * normalizedXi d) := by
  let f := D.a10ModelEmbedding e
  have hh := conj_eq_of_commute a.corePi_commute.symm
  have hs : a.alpha⁻¹ * f corePi * a.alpha =
      (a.alpha⁻¹ * f Coordinates.pi * a.alpha) *
      (a.alpha⁻¹ * f Coordinates.mu * a.alpha) := by
    rw [corePi, map_mul]
    group
  rw [hs, a.pi_alpha] at hh
  have hx : f (normalizedXi d) * (a.alpha⁻¹ * f Coordinates.mu * a.alpha) =
      f Coordinates.mu := by
    apply mul_left_cancel (a := f Coordinates.pi)
    simpa only [corePi, map_mul, mul_assoc] using hh
  have hlocal : ∀ d, normalizedXi d * normalizedXi d = 1 ∧
      normalizedXi d * Coordinates.mu = Coordinates.mu * normalizedXi d := by
    decide +kernel
  have hxx : f (normalizedXi d) * f (normalizedXi d) = 1 := by
    rw [← map_mul, (hlocal d).1, map_one]
  calc
    _ = f (normalizedXi d) *
        (f (normalizedXi d) * (a.alpha⁻¹ * f Coordinates.mu * a.alpha)) := by
      rw [← mul_assoc, hxx, one_mul]
    _ = f (normalizedXi d) * f Coordinates.mu := by rw [hx]
    _ = f (Coordinates.mu * normalizedXi d) := by rw [← map_mul, (hlocal d).2]

public theorem AlphaRelations.xi_isConj_mu {d : Bit} (a : AlphaRelations D e d) :
    IsConj (D.a10ModelEmbedding e (normalizedXi d))
      (D.a10ModelEmbedding e Coordinates.mu) :=
  isConj_iff.mpr ⟨a.alpha⁻¹, by simpa only [inv_inv] using a.xi_alpha⟩


end FaithfulExclusion
end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
