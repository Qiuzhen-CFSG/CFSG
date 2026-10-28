module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction.Relations
import Mathlib.Tactic.Group

/-!
# Section actions before the commuting choice

The relations of the first actor imply pi^u = tau and tau^u = pi*tau:
conjugate the two given actions on mu and lambda by tau-prime. The supplied
marked section is normalized by u because it is the solvable residual of
C_G(mu) and centralizes lambda. The second actor lies in that section
because the quotient has order eight and v has order three.

The marked dihedral relation (mu-prime * tau*lambda)² = pi*mu identifies
the element needed in the small-normalizer calculation. Conjugating v by
this element agrees with the source replacement v by v^pi, since v
centralizes mu. These statements require no commutation between the actors.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Sections 4.1--4.2 and 5.1, pp.232--236.
The section arguments use the same intrinsic residual and quotient facts
as `SixConstruction.RootCentralization`, without a compatible-actor input.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

private theorem tau'_mu :
    tau' D e * mu D e * (tau' D e)⁻¹ = pi D e * mu D e := by
  have h : modelElement 4 * modelElement 1 * (modelElement 4)⁻¹ =
      modelElement 0 * modelElement 1 := by decide +kernel
  simpa only [element, map_mul, map_inv] using congrArg (D.a10ModelEmbedding e) h

private theorem tau'_lam :
    tau' D e * lam D e * (tau' D e)⁻¹ = tau D e * lam D e := by
  have h : modelElement 4 * modelElement 6 * (modelElement 4)⁻¹ =
      modelElement 3 * modelElement 6 := by decide +kernel
  simpa only [element, map_mul, map_inv] using congrArg (D.a10ModelEmbedding e) h

private theorem UActor.conj_tau'_conj (a : UActor D e) (x : G) :
    (MulAut.conj a.u⁻¹) (tau' D e * x * (tau' D e)⁻¹) =
      tau' D e * (MulAut.conj a.u⁻¹) x * (tau' D e)⁻¹ := by
  let f := MulAut.conj a.u⁻¹
  change f (tau' D e * x * (tau' D e)⁻¹) = tau' D e * f x * (tau' D e)⁻¹
  have ht : f (tau' D e) = tau' D e := by
    simp only [f, MulAut.conj_apply, inv_inv]
    rw [mul_assoc, ← a.tau'_commute.eq, inv_mul_cancel_left]
  rw [map_mul, map_mul, map_inv, ht]

public theorem UActor.pi_mu_u (a : UActor D e) :
    a.u⁻¹ * (pi D e * mu D e) * a.u = tau D e * lam D e := by
  have h := a.conj_tau'_conj D e (mu D e)
  simpa only [tau'_mu, MulAut.conj_apply, inv_inv, a.mu_u, tau'_lam] using h

public theorem UActor.pi_u (a : UActor D e) :
    a.u⁻¹ * pi D e * a.u = tau D e := by
  apply mul_right_cancel (b := lam D e)
  calc
    _ = a.u⁻¹ * (pi D e * mu D e) * a.u := by rw [← a.mu_u]; group
    _ = _ := a.pi_mu_u D e

public theorem UActor.tau_u (a : UActor D e) :
    a.u⁻¹ * tau D e * a.u = pi D e * tau D e := by
  have h := a.conj_tau'_conj D e (lam D e)
  have h' : (a.u⁻¹ * tau D e * a.u) * (mu D e * lam D e) =
      (pi D e * mu D e) * (tau D e * lam D e) := by
    calc
      _ = (MulAut.conj a.u⁻¹) (tau D e * lam D e) := by
        simp only [map_mul, MulAut.conj_apply, inv_inv, a.lam_u]
      _ = tau' D e * (mu D e * lam D e) * (tau' D e)⁻¹ := by
        simpa only [tau'_lam, MulAut.conj_apply, inv_inv, a.lam_u] using h
      _ = (tau' D e * mu D e * (tau' D e)⁻¹) *
          (tau' D e * lam D e * (tau' D e)⁻¹) := by group
      _ = _ := by rw [tau'_mu, tau'_lam]
  have hc : Commute (mu D e) (tau D e) :=
    (show Commute (modelElement 1) (modelElement 3) from by change _ * _ = _ * _; decide +kernel).map _
  apply mul_right_cancel (b := mu D e * lam D e)
  rw [h']
  calc
    _ = pi D e * (mu D e * tau D e) * lam D e := by group
    _ = pi D e * (tau D e * mu D e) * lam D e := by rw [hc.eq]
    _ = _ := by group

/-- The central involution of the marked dihedral subgroup is pi*mu. -/
public theorem actor_dihedral_commutator :
    mu' D e * (tau D e * lam D e) * mu' D e * (tau D e * lam D e) =
      pi D e * mu D e := by
  have h : modelElement 2 * (modelElement 3 * modelElement 6) * modelElement 2 *
      (modelElement 3 * modelElement 6) = modelElement 0 * modelElement 1 := by decide +kernel
  simpa only [element, map_mul] using congrArg (D.a10ModelEmbedding e) h

public theorem actor_core_square : (pi D e * mu D e) ^ 2 = 1 := by
  have h : (modelElement 0 * modelElement 1) ^ 2 = 1 := by decide +kernel
  simpa only [element, map_mul, map_pow, map_one] using congrArg (D.a10ModelEmbedding e) h

public theorem actor_core_ne_one : pi D e * mu D e ≠ 1 := by
  intro h
  have hmodel : modelElement 0 * modelElement 1 = 1 := by
    apply D.a10ModelEmbedding_injective e
    simpa only [element, map_mul, map_one] using h
  exact (show modelElement 0 * modelElement 1 ≠ 1 from by decide +kernel) hmodel

public theorem actor_second_square : (tau D e * lam D e) ^ 2 = 1 := by
  have h : (modelElement 3 * modelElement 6) ^ 2 = 1 := by decide +kernel
  simpa only [element, map_mul, map_pow, map_one] using congrArg (D.a10ModelEmbedding e) h

/-- Conjugating v by pi is the same as conjugating by the element pi*mu of A. -/
public theorem VActor.conjugatePi_eq_core_conjugate (b : VActor D e) :
    (b.conjugatePi D e).v = (pi D e * mu D e)⁻¹ * b.v * (pi D e * mu D e) := by
  rw [VActor.conjugatePi_v, (commute_pi D e 1).eq]
  calc
    _ = (pi D e)⁻¹ * ((mu D e)⁻¹ * b.v * mu D e) * pi D e := by
      rw [mul_assoc (mu D e)⁻¹, b.mu_commute.eq, inv_mul_cancel_left]
    _ = _ := by group

variable (s : NoncentralAnalysis.AlternatingSixSection
    (centralizer ({D.a10NoncentralInvolution e} : Set G)))

public theorem VActor.mem_section (b : VActor D e) : b.v ∈ s.ambientSubgroup :=
  s.mem_ambientSubgroup_of_cube_eq_one b.v
    (mem_centralizer_singleton_iff.mpr b.mu_commute.eq)
    (b.order ▸ pow_orderOf_eq_one b.v)

public theorem UActor.normalizes_section (m : MarkedSection D e s) (a : UActor D e) :
    a.u ∈ normalizer (s.ambientSubgroup : Set G) := by
  apply s.normalizes_ambientSubgroup_of_conj_le
  rintro y ⟨x, hx, rfl⟩
  have hc : Commute x (lam D e) :=
    (mem_centralizer_iff.mp (m.centralizes hx) (lam D e) (by simp)).symm
  have he : a.u * lam D e * a.u⁻¹ = mu D e := by rw [← a.mu_u]; group
  have h := hc.map (MulAut.conj a.u).toMonoidHom
  change Commute (a.u * x * a.u⁻¹) (a.u * lam D e * a.u⁻¹) at h
  rw [he] at h
  exact mem_centralizer_singleton_iff.mpr h.eq

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
