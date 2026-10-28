module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.Inputs
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
import Mathlib.Tactic.Group

/-!
# The product of the compatible actors centralizes the canonical A₆

The section is the solvable residual of C_G(mu). Since it centralizes
lambda and mu^u = lambda, conjugation by u carries it back into C_G(mu),
hence normalizes it. The cube-one element v belongs to the section because
its quotient has order eight.

Commutation of u with tau-prime transports mu^u = lambda to
(pi*mu)^u = tau*lambda. The action of v then makes u*v fix pi*mu.
A cube-one automorphism of A₆ fixing an involution is trivial: that
involution's stabilizer in Aut(A₆) has order 32. This proves Held 5.2
without adding root centralization as a construction premise. The product
also has order exactly three, since it takes mu to the distinct lambda.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemmas 5.1--5.2, printed pp.235--236.
The order-32 stabilizer theorem uses the actual six-point alternating group.
The existence of the marked section and compatible actors remains separate.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction

private theorem cube_aut_eq_one_of_fix_involution
    (f : MulAut (alternatingGroup (Fin 6))) (hf : f ^ 3 = 1)
    (t : alternatingGroup (Fin 6)) (ht : orderOf t = 2) (hfix : f t = t) : f = 1 := by
  let F := MulAction.stabilizer (MulAut (alternatingGroup (Fin 6))) t
  have hc : Nat.card F = 32 := by
    change Nat.card (MulAction.stabilizer (MulAut (alternatingGroup (Fin 6))) t) = 32
    rw [← AlternatingSix.ShadowLocal.centralizer_inner_eq_stabilizer]
    exact AlternatingSix.ShadowLocal.inner_involution_centralizer_card t ht
  let a : F := ⟨f, hfix⟩
  have ha3 : a ^ 3 = 1 := Subtype.ext hf
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha3) (orderOf_dvd_natCard a)
  rw [hc] at hd
  norm_num at hd
  exact congrArg Subtype.val hd

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (s : NoncentralAnalysis.AlternatingSixSection
    (centralizer ({D.a10NoncentralInvolution e} : Set G)))

public theorem centralizes_section_of_cube_and_fixed_involution
    (w : G) (hw : w ∈ normalizer (s.ambientSubgroup : Set G)) (hw3 : w ^ 3 = 1)
    (t : G) (ht : t ∈ s.ambientSubgroup) (ht2 : orderOf t = 2)
    (hfix : Commute w t) : ∀ a ∈ s.ambientSubgroup, Commute w a := by
  let j := s.ambientAlternatingEquiv
  let f := (MulAut.congr j).toMonoidHom.comp s.ambientSubgroup.normalizerMonoidHom
  let n : normalizer (s.ambientSubgroup : Set G) := ⟨w, hw⟩
  let t' : s.ambientSubgroup := ⟨t, ht⟩
  have hf3 : (f n) ^ 3 = 1 := by
    rw [← map_pow, show n ^ 3 = 1 from Subtype.ext hw3, map_one]
  have ht' : orderOf (j t') = 2 := by
    rw [j.orderOf_eq, ← orderOf_injective s.ambientSubgroup.subtype Subtype.val_injective]
    exact ht2
  have hfix' : f n (j t') = j t' := by
    change j (s.ambientSubgroup.normalizerMonoidHom n (j.symm (j t'))) = j t'
    rw [j.symm_apply_apply]
    apply congrArg j
    apply Subtype.ext
    change w * t * w⁻¹ = t
    exact mul_inv_eq_iff_eq_mul.mpr hfix.eq
  have hf := cube_aut_eq_one_of_fix_involution (f n) hf3 (j t') ht' hfix'
  have ha : s.ambientSubgroup.normalizerMonoidHom n = 1 :=
    (MulAut.congr j).injective (hf.trans (map_one _).symm)
  intro a haA
  have he := congrArg (fun k : MulAut s.ambientSubgroup => (k ⟨a, haA⟩ : G)) ha
  change w * a * w⁻¹ = a at he
  exact mul_inv_eq_iff_eq_mul.mp he

variable (m : MarkedSection D e s) (c : CompatibleActors D e)

public theorem CompatibleActors.v_mem_section : c.v ∈ s.ambientSubgroup :=
  s.mem_ambientSubgroup_of_cube_eq_one c.v
    (mem_centralizer_singleton_iff.mpr c.v_mu_commute.eq)
    (c.v_order ▸ pow_orderOf_eq_one c.v)

include m in
public theorem CompatibleActors.u_normalizes_section :
    c.u ∈ normalizer (s.ambientSubgroup : Set G) := by
  apply s.normalizes_ambientSubgroup_of_conj_le
  rintro y ⟨a, ha, rfl⟩
  have hc : Commute a (lam D e) :=
    (mem_centralizer_iff.mp (m.centralizes ha) (lam D e) (by simp)).symm
  have he : c.u * lam D e * c.u⁻¹ = mu D e := by
    rw [← c.mu_u]
    group
  have h := hc.map (MulAut.conj c.u).toMonoidHom
  change Commute (c.u * a * c.u⁻¹) (c.u * lam D e * c.u⁻¹) at h
  rw [he] at h
  exact mem_centralizer_singleton_iff.mpr h.eq

public theorem CompatibleActors.root_cube : (c.u * c.v) ^ 3 = 1 := by
  rw [c.u_v_commute.mul_pow]
  rw [show c.u ^ 3 = 1 from c.u_order ▸ pow_orderOf_eq_one _,
    show c.v ^ 3 = 1 from c.v_order ▸ pow_orderOf_eq_one _, one_mul]

public theorem CompatibleActors.mu_root :
    (c.u * c.v)⁻¹ * mu D e * (c.u * c.v) = lam D e := by
  calc
    _ = c.v⁻¹ * (c.u⁻¹ * mu D e * c.u) * c.v := by group
    _ = _ := by
      rw [c.mu_u, mul_assoc, ← c.v_lam_commute.eq, inv_mul_cancel_left]

public theorem CompatibleActors.root_order : orderOf (c.u * c.v) = 3 := by
  apply orderOf_eq_prime (c.root_cube D e)
  intro h
  have he : mu D e = lam D e := by simpa only [h, inv_one, one_mul, mul_one] using c.mu_root D e
  have hm := D.a10ModelEmbedding_injective e he
  exact (show modelElement 1 ≠ modelElement 6 from by decide +kernel) hm

private theorem pi_mu_tau' :
    pi D e * mu D e = tau' D e * mu D e * (tau' D e)⁻¹ := by
  have h : modelElement 0 * modelElement 1 =
      modelElement 4 * modelElement 1 * (modelElement 4)⁻¹ := by decide +kernel
  simpa only [element, map_mul, map_inv] using congrArg (D.a10ModelEmbedding e) h

private theorem tau_lam_tau' :
    tau D e * lam D e = tau' D e * lam D e * (tau' D e)⁻¹ := by
  have h : modelElement 3 * modelElement 6 =
      modelElement 4 * modelElement 6 * (modelElement 4)⁻¹ := by decide +kernel
  simpa only [element, map_mul, map_inv] using congrArg (D.a10ModelEmbedding e) h

public theorem CompatibleActors.pi_mu_u :
    c.u⁻¹ * (pi D e * mu D e) * c.u = tau D e * lam D e := by
  rw [pi_mu_tau' D e, tau_lam_tau' D e]
  let f := MulAut.conj c.u⁻¹
  have ht : f (tau' D e) = tau' D e := by
    change c.u⁻¹ * tau' D e * (c.u⁻¹)⁻¹ = tau' D e
    rw [inv_inv, mul_assoc, ← c.u_tau'_commute.eq, inv_mul_cancel_left]
  have hmu : f (mu D e) = lam D e := by simpa only [f, MulAut.conj_apply, inv_inv] using c.mu_u
  calc
    _ = f (tau' D e * mu D e * (tau' D e)⁻¹) := by
      simp only [f, MulAut.conj_apply, inv_inv]
    _ = _ := by rw [map_mul, map_mul, map_inv, ht, hmu]

public theorem CompatibleActors.tau_lam_v :
    c.v⁻¹ * (tau D e * lam D e) * c.v = pi D e * mu D e := by
  calc
    _ = (c.v⁻¹ * tau D e * c.v) * (c.v⁻¹ * lam D e * c.v) := by group
    _ = (pi D e * mu D e * lam D e) * lam D e := by
      rw [c.tau_v]
      congr 1
      rw [mul_assoc, ← c.v_lam_commute.eq, inv_mul_cancel_left]
    _ = _ := by
      rw [mul_assoc, ← pow_two, element_square D e 6 (by decide), mul_one]

public theorem CompatibleActors.root_fixes_pi_mu : Commute (c.u * c.v) (pi D e * mu D e) := by
  have h : (c.u * c.v)⁻¹ * (pi D e * mu D e) * (c.u * c.v) = pi D e * mu D e := by
    calc
      _ = c.v⁻¹ * (c.u⁻¹ * (pi D e * mu D e) * c.u) * c.v := by group
      _ = _ := by rw [c.pi_mu_u D e, c.tau_lam_v D e]
  have h' := congrArg (fun x => (c.u * c.v) * x) h
  change (c.u * c.v) * (pi D e * mu D e) = (pi D e * mu D e) * (c.u * c.v)
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using h'.symm

include m in
public theorem CompatibleActors.root_centralizes_section :
    ∀ a ∈ s.ambientSubgroup, Commute (c.u * c.v) a := by
  apply centralizes_section_of_cube_and_fixed_involution D e s (c.u * c.v)
  · exact mul_mem (c.u_normalizes_section D e s m)
      (s.ambientSubgroup.le_normalizer (c.v_mem_section D e s))
  · exact c.root_cube D e
  · exact m.pi_mu_mem
  · have h : orderOf (modelElement 0 * modelElement 1) = 2 :=
      orderOf_eq_prime (by decide +kernel) (by decide +kernel)
    change orderOf (D.a10ModelEmbedding e (modelElement 0) *
      D.a10ModelEmbedding e (modelElement 1)) = 2
    rw [← map_mul, orderOf_injective _ (D.a10ModelEmbedding_injective e)]
    exact h
  · exact c.root_fixes_pi_mu D e

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
