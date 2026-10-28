module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction.VConstruction.Fusion
import Mathlib.Tactic.Group

/-!
# Constructing Held's second actor from the marked section

The marked A6 and its symmetric extension determine the parity of the local
involutions. Pi--mu nonfusion excludes the wrong central involution in the
six-point permutation calculation. Transporting its order-three actor through
the supplied equivalence gives an element of C_G(mu); the dihedral quotient
places it in A6, hence it also centralizes lambda. The marked four-group
actions then give the required individual pi and tau actions.

This constructs every field of `VActor` without the first actor or any
commuting-choice hypothesis. In fact the marked section and pi--mu nonfusion
suffice: simplicity and the additional lambda and xi separations are not
needed for this specialized route.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemmas 4.1--4.2, printed pp.232--235.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
open VConstruction
variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The actual order-three actor of Held 4.1, constructed from the explicit
marked symmetric extension and pi--mu nonfusion. -/
public theorem exists_vActor_of_markedSection [Finite G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (s : NoncentralAnalysis.AlternatingSixSection
      (centralizer ({D.a10NoncentralInvolution e} : Set G))) (m : MarkedSection D e s) :
    Nonempty (VActor D e) := by
  let X : Subgroup G := s.ambientSubgroup ⊔ zpowers (mu' D e)
  let j := m.symmetricEquiv
  let f : Perm (Fin 6) →* G := X.subtype.comp j.symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp j.symm.injective
  let a₀ : X := ⟨pi D e * mu D e, (show s.ambientSubgroup ≤ X from le_sup_left) m.pi_mu_mem⟩
  let b₀ : X := ⟨tau D e * lam D e, (show s.ambientSubgroup ≤ X from le_sup_left) m.tau_lam_mem⟩
  let d₀ : X := ⟨mu' D e, (show zpowers (mu' D e) ≤ X from le_sup_right) (mem_zpowers _)⟩
  let x₀ : X := ⟨xi D e, marked_xi_mem_extension D e s m⟩
  let a := j a₀
  let b := j b₀
  let d := j d₀
  let x := j x₀
  have fa : f a = pi D e * mu D e := congrArg Subtype.val (j.symm_apply_apply a₀)
  have fb : f b = tau D e * lam D e := congrArg Subtype.val (j.symm_apply_apply b₀)
  have fd : f d = mu' D e := congrArg Subtype.val (j.symm_apply_apply d₀)
  have fx : f x = xi D e := congrArg Subtype.val (j.symm_apply_apply x₀)
  have ha : a ^ 2 = 1 := hf (by simpa only [map_pow, map_one, fa] using actor_core_square D e)
  have hane : a ≠ 1 := by
    intro h
    exact actor_core_ne_one D e (by rw [← fa, h, map_one])
  have has : Perm.sign a = 1 := (marked_even_iff D e s m a₀).mpr m.pi_mu_mem
  have hb : b ^ 2 = 1 := hf (by simpa only [map_pow, map_one, fb] using actor_second_square D e)
  have hbs : Perm.sign b = 1 := (marked_even_iff D e s m b₀).mpr m.tau_lam_mem
  have hd : d ^ 2 = 1 := hf (by simpa only [map_pow, map_one, fd] using element_square D e 2 (by decide))
  have hds : Perm.sign d ≠ 1 := by
    intro h
    exact marked_mu'_not_mem D e s m ((marked_even_iff D e s m d₀).mp h)
  have hx : x ^ 2 = 1 := hf (by simpa only [map_pow, map_one, fx] using element_square D e 7 (by decide))
  have hcs : Perm.sign (d * x) = 1 := by
    have hcA : ((j.symm (d * x) : X) : G) ∈ s.ambientSubgroup := by
      change f (d * x) ∈ _
      rw [map_mul, fd, fx]
      exact m.mu'_xi_mem
    simpa only [j, MulEquiv.apply_symm_apply] using (marked_even_iff D e s m (j.symm (d * x))).mpr hcA
  have hxs : Perm.sign x ≠ 1 := by
    intro h
    apply hds
    simpa only [map_mul, h, mul_one] using hcs
  have hab : Commute a b := by
    apply Commute.of_map hf
    rw [fa, fb]
    have h : Commute (modelElement 0 * modelElement 1) (modelElement 3 * modelElement 6) := by
      change _ * _ = _ * _
      decide +kernel
    simpa only [element, map_mul] using h.map (D.a10ModelEmbedding e)
  have had : Commute a d := by
    apply Commute.of_map hf
    rw [fa, fd]
    exact (commute_pi D e 2).mul_left (mu_commute_mu' D e)
  have hax : Commute a x := by
    apply Commute.of_map hf
    rw [fa, fx]
    exact (commute_pi D e 7).mul_left (mu_commute_xi D e)
  have hdx : Commute d x := by
    apply Commute.of_map hf
    rw [fd, fx]
    exact mu'_commute_xi D e
  have hbx : Commute b x := by
    apply Commute.of_map hf
    rw [fb, fx]
    have h : Commute (modelElement 3 * modelElement 6) (modelElement 7) := by
      change _ * _ = _ * _
      decide +kernel
    simpa only [element, map_mul] using h.map (D.a10ModelEmbedding e)
  have hdi : d * b * d * b = a := hf (by
    simpa only [map_mul, fd, fb, fa] using actor_dihedral_commutator D e)
  have hnot : ¬ IsConj d (a * x) := by
    intro h
    apply marked_not_isConj_mu'_core_xi D e s m hfusion
    simpa only [map_mul, fd, fa, fx] using f.map_isConj h
  obtain ⟨w, hw3, hwa, hwb, hwd, hwx⟩ := exists_permutation_actor a b d x
    ha hane has hb hbs hd hds hx hxs hab had hax hdx hbx hdi hnot
  let v := f w
  have hv3 : v ^ 3 = 1 := by
    simpa only [map_pow, map_one] using congrArg f hw3
  have hvmu : Commute v (mu D e) :=
    mem_centralizer_singleton_iff.mp (extension_le_centralizer D e s (j.symm w).property)
  have hvA : v ∈ s.ambientSubgroup := s.mem_ambientSubgroup_of_cube_eq_one v
    (mem_centralizer_singleton_iff.mpr hvmu.eq) hv3
  have hvlam : Commute v (lam D e) :=
    (mem_centralizer_iff.mp (m.centralizes hvA) (lam D e) (by simp)).symm
  have hvxi : Commute v (xi D e) := by
    simpa only [fx] using hwx.map f
  have hva : v⁻¹ * (pi D e * mu D e) * v =
      (pi D e * mu D e) * (tau D e * lam D e) := by
    simpa only [map_mul, map_inv, fa, fb] using congrArg f hwa
  have hvb : v⁻¹ * (tau D e * lam D e) * v = pi D e * mu D e := by
    simpa only [map_mul, map_inv, fa, fb] using congrArg f hwb
  have hvd : mu' D e * v * mu' D e = v⁻¹ := by
    simpa only [map_mul, map_inv, fd] using congrArg f hwd
  have hvne : v ≠ 1 := by
    intro hv
    have he : tau D e * lam D e = pi D e * mu D e := by simpa only [hv, inv_one, one_mul, mul_one] using hvb
    have hn : modelElement 3 * modelElement 6 ≠ modelElement 0 * modelElement 1 := by decide +kernel
    exact hn (D.a10ModelEmbedding_injective e (by simpa only [element, map_mul] using he))
  have hvpi : v⁻¹ * pi D e * v = pi D e * tau D e * lam D e := by
    apply mul_right_cancel (b := mu D e)
    have hm : v⁻¹ * mu D e * v = mu D e := by
      rw [hvmu.inv_left.eq, inv_mul_cancel_right]
    calc
      _ = v⁻¹ * (pi D e * mu D e) * v := by
        conv_lhs => rw [← hm]
        group
      _ = (pi D e * mu D e) * (tau D e * lam D e) := hva
      _ = (pi D e * tau D e * lam D e) * mu D e := by
        have h : (modelElement 0 * modelElement 1) * (modelElement 3 * modelElement 6) =
            (modelElement 0 * modelElement 3 * modelElement 6) * modelElement 1 := by decide +kernel
        simpa only [element, map_mul] using congrArg (D.a10ModelEmbedding e) h
  have hvtau : v⁻¹ * tau D e * v = pi D e * mu D e * lam D e := by
    apply mul_right_cancel (b := lam D e)
    have hl : v⁻¹ * lam D e * v = lam D e := by
      rw [hvlam.inv_left.eq, inv_mul_cancel_right]
    calc
      _ = v⁻¹ * (tau D e * lam D e) * v := by
        conv_lhs => rw [← hl]
        group
      _ = pi D e * mu D e := hvb
      _ = (pi D e * mu D e * lam D e) * lam D e := by
        have hll : lam D e * lam D e = 1 := by simpa only [pow_two] using element_square D e 6 (by decide)
        rw [mul_assoc, hll, mul_one]
  exact ⟨{
    v := v
    order := orderOf_eq_prime hv3 hvne
    mu_commute := hvmu
    lam_commute := hvlam
    xi_commute := hvxi
    pi_v := hvpi
    tau_v := hvtau
    mu'_inverts := hvd }⟩
end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
