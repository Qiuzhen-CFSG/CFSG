module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction.VConstruction.Parity
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction.VConstruction.Permutation
import Mathlib.Tactic.Group

/-!
# The fusion exclusion needed by the second actor

The two marked involutions pi*mu and mu-prime*xi are conjugate in the supplied
S6 extension, whose elements centralize mu. Multiplying this conjugacy by mu
and applying tau-prime proves that pi*mu*xi is conjugate to pi. Since mu-prime
is conjugate to mu by rho, pi--mu nonfusion separates mu-prime from pi*mu*xi.
This is precisely the cycle-type exclusion used by the permutation actor.
No order-three actor or later recognition theorem is used.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemmas 4.1--4.2, printed pp.232--235.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
namespace VConstruction
variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (s : NoncentralAnalysis.AlternatingSixSection
    (centralizer ({D.a10NoncentralInvolution e} : Set G))) (m : MarkedSection D e s)

include m in
private theorem marked_involutions_conjugate (a b : G)
    (haA : a ∈ s.ambientSubgroup) (hbA : b ∈ s.ambientSubgroup)
    (ha : a ^ 2 = 1) (hane : a ≠ 1) (hb : b ^ 2 = 1) (hbne : b ≠ 1) :
    ∃ g ∈ s.ambientSubgroup ⊔ zpowers (mu' D e), g * a * g⁻¹ = b := by
  let X : Subgroup G := s.ambientSubgroup ⊔ zpowers (mu' D e)
  let r : X := ⟨a, (show s.ambientSubgroup ≤ X from le_sup_left) haA⟩
  let q : X := ⟨b, (show s.ambientSubgroup ≤ X from le_sup_left) hbA⟩
  let j := m.symmetricEquiv
  have ht (y : X) (hy : (y : G) ^ 2 = 1) (hne : (y : G) ≠ 1)
      (hA : (y : G) ∈ s.ambientSubgroup) : (j y).cycleType = {2, 2} := by
    apply even_involution_cycleType
    · rw [← map_pow, show y ^ 2 = 1 from Subtype.ext hy, map_one]
    · intro h
      exact hne (congrArg Subtype.val (j.injective (h.trans (map_one j).symm)))
    · exact (marked_even_iff D e s m y).mpr hA
  obtain ⟨g, hg⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr
    ((ht r ha hane haA).trans (ht q hb hbne hbA).symm))
  refine ⟨j.symm g, (j.symm g).property, ?_⟩
  have hh : j.symm g * r * (j.symm g)⁻¹ = q := by
    apply j.injective
    simpa only [map_mul, map_inv, j.apply_symm_apply] using hg
  exact congrArg Subtype.val hh

include m in
public theorem marked_pi_fusion : IsConj (pi D e) (pi D e * mu D e * xi D e) := by
  have hc2 : (mu' D e * xi D e) ^ 2 = 1 := by
    have h : (modelElement 2 * modelElement 7) ^ 2 = 1 := by decide +kernel
    simpa only [element, map_pow, map_mul, map_one] using congrArg (D.a10ModelEmbedding e) h
  have hcne : mu' D e * xi D e ≠ 1 := by
    intro h
    apply (show modelElement 2 * modelElement 7 ≠ 1 from by decide +kernel)
    apply D.a10ModelEmbedding_injective e
    simpa only [element, map_mul, map_one] using h
  obtain ⟨g, hg, hgc⟩ := marked_involutions_conjugate D e s m
    (pi D e * mu D e) (mu' D e * xi D e) m.pi_mu_mem m.mu'_xi_mem
    (actor_core_square D e) (actor_core_ne_one D e) hc2 hcne
  have hgm : Commute g (mu D e) :=
    mem_centralizer_singleton_iff.mp (extension_le_centralizer D e s hg)
  let f := MulAut.conj g
  have hfm : f (mu D e) = mu D e := by
    change g * mu D e * g⁻¹ = mu D e
    rw [hgm.eq, mul_inv_cancel_right]
  have hfa : f (pi D e * mu D e) = mu' D e * xi D e := hgc
  have hpi : f (pi D e) = mu D e * (mu' D e * xi D e) := by
    have he : pi D e = mu D e * (pi D e * mu D e) := by
      have h : modelElement 0 = modelElement 1 * (modelElement 0 * modelElement 1) := by decide +kernel
      simpa only [element, map_mul] using congrArg (D.a10ModelEmbedding e) h
    calc
      _ = f (mu D e * (pi D e * mu D e)) := congrArg f he
      _ = _ := by rw [map_mul, hfm, hfa]
  have hfirst : IsConj (pi D e) (mu D e * (mu' D e * xi D e)) :=
    isConj_iff.mpr ⟨g, hpi⟩
  apply hfirst.trans
  apply isConj_iff.mpr
  refine ⟨tau' D e, ?_⟩
  have h : modelElement 4 * (modelElement 1 * (modelElement 2 * modelElement 7)) *
      (modelElement 4)⁻¹ = modelElement 0 * modelElement 1 * modelElement 7 := by decide +kernel
  simpa only [element, map_mul, map_inv] using congrArg (D.a10ModelEmbedding e) h

include m in
public theorem marked_not_isConj_mu'_core_xi [Finite G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) :
    ¬ IsConj (mu' D e) (pi D e * mu D e * xi D e) := by
  intro h
  have hmd : IsConj (mu D e) (mu' D e) := by
    apply isConj_iff.mpr
    refine ⟨rho D e, ?_⟩
    have hm : modelElement 5 * modelElement 1 * (modelElement 5)⁻¹ = modelElement 2 := by decide +kernel
    simpa only [element, map_mul, map_inv] using congrArg (D.a10ModelEmbedding e) hm
  apply hfusion
  simpa only [pi_eq, mu_eq] using ((marked_pi_fusion D e s m).trans h.symm).trans hmd.symm
end VConstruction
end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
