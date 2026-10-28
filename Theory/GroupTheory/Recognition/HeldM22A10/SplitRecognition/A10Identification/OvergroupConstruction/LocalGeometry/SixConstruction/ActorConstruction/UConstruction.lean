module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction.UConstruction.Seed
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction.UConstruction.InitialSeed
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction.UConstruction.TauPrime
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
import Mathlib.Tactic.Group

/-!
# Construction of Held's first normalized order-three actor

The supplied marked A₆ gives the four-action element through `InitialSeed`.
The construction in `TauPrime` conjugates it by an element of <mu, lambda>
to centralize tau-prime, preserving its exact order and all four actions.

Let u have the four cyclic actions of the first paragraph on printed p.233
and centralize tau-prime. Set k = u⁻¹*mu-prime*u⁻¹. Its actions put k inside
the known centralizer of pi. A kernel-checked calculation in its 384 normal
forms gives four possibilities. The relation between k and u excludes the
pi*mu-prime and tau*mu-prime cases, leaving mu-prime or pi*tau*mu-prime.
In the second case replace u by pi*u. The proof verifies its exact order
three and all the actions, including inversion by mu-prime.

`exists_uActor_of_centralizedSeed` supplies the final normalization.
`exists_uActor_of_markedSection` combines all three constructions, proving
actor existence from the source hypotheses and the explicit marked section
without any additional seed or normalization premise.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 4.2, printed p.233.
The source convention is x^g = g⁻¹*x*g.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

private theorem square_inv (i : Fin 8) (hi : i ≠ 5) : (element D e i)⁻¹ = element D e i := by
  exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using element_square D e i hi)

private theorem local_b_actions :
    mu' D e * pi D e * mu' D e = pi D e ∧
    mu' D e * mu D e * mu' D e = mu D e ∧
    mu' D e * tau D e * mu' D e = pi D e * tau D e ∧
    mu' D e * lam D e * mu' D e = mu D e * lam D e ∧
    mu' D e * tau' D e * mu' D e = tau' D e := by
  have h : modelElement 2 * modelElement 0 * modelElement 2 = modelElement 0 ∧
      modelElement 2 * modelElement 1 * modelElement 2 = modelElement 1 ∧
      modelElement 2 * modelElement 3 * modelElement 2 = modelElement 0 * modelElement 3 ∧
      modelElement 2 * modelElement 6 * modelElement 2 = modelElement 1 * modelElement 6 ∧
      modelElement 2 * modelElement 4 * modelElement 2 = modelElement 4 := by decide +kernel
  rcases h with ⟨h0, h1, h3, h6, h4⟩
  exact ⟨by simpa only [element, map_mul] using congrArg (D.a10ModelEmbedding e) h0,
    by simpa only [element, map_mul] using congrArg (D.a10ModelEmbedding e) h1,
    by simpa only [element, map_mul] using congrArg (D.a10ModelEmbedding e) h3,
    by simpa only [element, map_mul] using congrArg (D.a10ModelEmbedding e) h6,
    by simpa only [element, map_mul] using congrArg (D.a10ModelEmbedding e) h4⟩

private theorem local_products :
    lam D e * (mu D e * lam D e) = mu D e ∧
    tau D e * (pi D e * tau D e) = pi D e := by
  have h : modelElement 6 * (modelElement 1 * modelElement 6) = modelElement 1 ∧
      modelElement 3 * (modelElement 0 * modelElement 3) = modelElement 0 := by decide +kernel
  exact ⟨by simpa only [element, map_mul] using congrArg (D.a10ModelEmbedding e) h.1,
    by simpa only [element, map_mul] using congrArg (D.a10ModelEmbedding e) h.2⟩

private theorem k_conj (a : UCentralizedSeed D e) (x : G) :
    (MulAut.conj (a.u⁻¹ * mu' D e * a.u⁻¹)) x =
      (MulAut.conj a.u⁻¹) ((MulAut.conj (mu' D e)) ((MulAut.conj a.u⁻¹) x)) := by
  simp only [MulAut.conj_apply]
  group

private theorem k_actions (a : UCentralizedSeed D e) :
    let k := a.u⁻¹ * mu' D e * a.u⁻¹
    Commute k (pi D e) ∧ Commute k (mu D e) ∧ Commute k (tau' D e) ∧
      k * lam D e * k⁻¹ = mu D e * lam D e := by
  let f := MulAut.conj a.u⁻¹
  let b := MulAut.conj (mu' D e)
  have hf0 : f (pi D e) = tau D e := by
    simpa only [f, MulAut.conj_apply, inv_inv] using a.pi_u
  have hf1 : f (mu D e) = lam D e := by
    simpa only [f, MulAut.conj_apply, inv_inv] using a.mu_u
  have hf3 : f (tau D e) = pi D e * tau D e := by
    simpa only [f, MulAut.conj_apply, inv_inv] using a.tau_u
  have hf6 : f (lam D e) = mu D e * lam D e := by
    simpa only [f, MulAut.conj_apply, inv_inv] using a.lam_u
  have hf4 : f (tau' D e) = tau' D e := by
    simp only [f, MulAut.conj_apply, inv_inv]
    rw [mul_assoc, ← a.tau'_commute.eq, inv_mul_cancel_left]
  have hb1 : b (mu D e) = mu D e := by
    simpa only [b, MulAut.conj_apply, square_inv D e 2 (by decide)] using (local_b_actions D e).2.1
  have hb3 : b (tau D e) = pi D e * tau D e := by
    simpa only [b, MulAut.conj_apply, square_inv D e 2 (by decide)] using (local_b_actions D e).2.2.1
  have hb6 : b (lam D e) = mu D e * lam D e := by
    simpa only [b, MulAut.conj_apply, square_inv D e 2 (by decide)] using (local_b_actions D e).2.2.2.1
  have hb4 : b (tau' D e) = tau' D e := by
    simpa only [b, MulAut.conj_apply, square_inv D e 2 (by decide)] using (local_b_actions D e).2.2.2.2
  have hc (x : G) : (MulAut.conj (a.u⁻¹ * mu' D e * a.u⁻¹)) x = f (b (f x)) := k_conj D e a x
  have hc0 : (MulAut.conj (a.u⁻¹ * mu' D e * a.u⁻¹)) (pi D e) = pi D e := by
    rw [hc, hf0, hb3, map_mul, hf0, hf3, (local_products D e).2]
  have hc1 : (MulAut.conj (a.u⁻¹ * mu' D e * a.u⁻¹)) (mu D e) = mu D e := by
    rw [hc, hf1, hb6, map_mul, hf1, hf6, (local_products D e).1]
  have hc4 : (MulAut.conj (a.u⁻¹ * mu' D e * a.u⁻¹)) (tau' D e) = tau' D e := by
    rw [hc, hf4, hb4, hf4]
  have hc6 : (MulAut.conj (a.u⁻¹ * mu' D e * a.u⁻¹)) (lam D e) = mu D e * lam D e := by
    rw [hc, hf6, map_mul, hb1, hb6]
    have h : mu D e * (mu D e * lam D e) = lam D e := by
      rw [← mul_assoc, ← pow_two, element_square D e 1 (by decide), one_mul]
    rw [h, hf6]
  exact ⟨(mul_inv_eq_iff_eq_mul.mp hc0), (mul_inv_eq_iff_eq_mul.mp hc1),
    (mul_inv_eq_iff_eq_mul.mp hc4), hc6⟩

private instance modelDecidableEq : DecidableEq CentralizerModels.a10Centralizer := inferInstance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem model_k_classification (x : CentralizerModels.a10Centralizer)
    (hm : Commute x (modelElement 1)) (ht : Commute x (modelElement 4))
    (hl : x * modelElement 6 * x⁻¹ = modelElement 1 * modelElement 6) :
    x = modelElement 2 ∨ x = modelElement 0 * modelElement 2 ∨
      x = modelElement 3 * modelElement 2 ∨ x = modelElement 0 * modelElement 3 * modelElement 2 := by
  obtain ⟨c, rfl⟩ := NoncentralAnalysis.Coordinates.word_bijective.surjective x
  have table : ∀ c : NoncentralAnalysis.Coordinates.Code,
      let x := NoncentralAnalysis.Coordinates.word c
      x * modelElement 1 = modelElement 1 * x →
      x * modelElement 4 = modelElement 4 * x →
      x * modelElement 6 * x⁻¹ = modelElement 1 * modelElement 6 →
      x = modelElement 2 ∨ x = modelElement 0 * modelElement 2 ∨
        x = modelElement 3 * modelElement 2 ∨ x = modelElement 0 * modelElement 3 * modelElement 2 := by
    dsimp only
    decide +kernel
  exact table c hm.eq ht.eq hl

private theorem k_classification [Finite G] (a : UCentralizedSeed D e) :
    let k := a.u⁻¹ * mu' D e * a.u⁻¹
    k = mu' D e ∨ k = pi D e * mu' D e ∨
      k = tau D e * mu' D e ∨ k = pi D e * tau D e * mu' D e := by
  let k := a.u⁻¹ * mu' D e * a.u⁻¹
  obtain ⟨hp, hm, ht, hl⟩ := k_actions D e a
  have hk : k ∈ (D.a10ModelEmbedding e).range := by
    rw [D.a10ModelEmbedding_range]
    apply mem_centralizer_singleton_iff.mpr
    simpa only [← pi_eq D e] using hp.eq
  obtain ⟨x, hx⟩ := hk
  have inject := D.a10ModelEmbedding_injective e
  have hm' : Commute x (modelElement 1) := by
    apply show Function.Injective (D.a10ModelEmbedding e) from inject
    simpa only [map_mul, hx, k, element] using hm.eq
  have ht' : Commute x (modelElement 4) := by
    apply show Function.Injective (D.a10ModelEmbedding e) from inject
    simpa only [map_mul, hx, k, element] using ht.eq
  have hl' : x * modelElement 6 * x⁻¹ = modelElement 1 * modelElement 6 := by
    apply inject
    simpa only [map_mul, map_inv, hx, k, element] using hl
  rcases model_k_classification x hm' ht' hl' with h | h | h | h
  · exact Or.inl (hx.symm.trans (congrArg (D.a10ModelEmbedding e) h))
  · apply Or.inr; apply Or.inl
    simpa only [map_mul, k, element] using hx.symm.trans (congrArg (D.a10ModelEmbedding e) h)
  · apply Or.inr; apply Or.inr; apply Or.inl
    simpa only [map_mul, k, element] using hx.symm.trans (congrArg (D.a10ModelEmbedding e) h)
  · apply Or.inr; apply Or.inr; apply Or.inr
    simpa only [map_mul, k, element] using hx.symm.trans (congrArg (D.a10ModelEmbedding e) h)

private theorem u_forward (a : USeed D e) :
    a.u * pi D e * a.u⁻¹ = pi D e * tau D e ∧
      a.u * tau D e * a.u⁻¹ = pi D e := by
  have ht : a.u * tau D e * a.u⁻¹ = pi D e := by rw [← a.pi_u]; group
  have hpt : a.u * (pi D e * tau D e) * a.u⁻¹ = tau D e := by rw [← a.tau_u]; group
  refine ⟨?_, ht⟩
  calc
    _ = (a.u * (pi D e * tau D e) * a.u⁻¹) * (a.u * tau D e * a.u⁻¹)⁻¹ := by group
    _ = tau D e * (pi D e)⁻¹ := by rw [hpt, ht]
    _ = pi D e * tau D e := by rw [square_inv D e 0 (by decide), (commute_pi D e 3).eq]

private theorem k_constraint (a : UCentralizedSeed D e) :
    let k := a.u⁻¹ * mu' D e * a.u⁻¹
    a.u * (k * mu' D e) * a.u⁻¹ = mu' D e * (k * mu' D e) * mu' D e := by
  dsimp only
  have hb : mu' D e * mu' D e = 1 := by simpa only [pow_two] using element_square D e 2 (by decide)
  calc
    _ = mu' D e * a.u⁻¹ * mu' D e * a.u⁻¹ := by group
    _ = _ := by simp only [mul_assoc, hb, mul_one]

private theorem k_two_cases [Finite G] (a : UCentralizedSeed D e) :
    a.u⁻¹ * mu' D e * a.u⁻¹ = mu' D e ∨
      a.u⁻¹ * mu' D e * a.u⁻¹ = pi D e * tau D e * mu' D e := by
  have hc := k_constraint D e a
  have hb : mu' D e * mu' D e = 1 := by simpa only [pow_two] using element_square D e 2 (by decide)
  rcases k_classification D e a with h | h | h | h
  · exact Or.inl h
  · rw [h] at hc
    simp only [mul_assoc, hb, mul_one] at hc
    have he : pi D e * tau D e = pi D e := by
      calc
        _ = a.u * pi D e * a.u⁻¹ := (u_forward D e a.toUSeed).1.symm
        _ = mu' D e * pi D e * mu' D e := by simpa only [mul_assoc] using hc
        _ = pi D e := (local_b_actions D e).1
    have ht : tau D e = 1 := mul_left_cancel (he.trans (mul_one _).symm)
    exact False.elim (element_ne_one D e 3 ht)
  · rw [h] at hc
    simp only [mul_assoc, hb, mul_one] at hc
    have he : pi D e = pi D e * tau D e := by
      calc
        _ = a.u * tau D e * a.u⁻¹ := (u_forward D e a.toUSeed).2.symm
        _ = mu' D e * tau D e * mu' D e := by simpa only [mul_assoc] using hc
        _ = pi D e * tau D e := (local_b_actions D e).2.2.1
    have ht : tau D e = 1 := mul_left_cancel (he.symm.trans (mul_one _).symm)
    exact False.elim (element_ne_one D e 3 ht)
  · exact Or.inr h

private theorem pi_mul_u_cube (a : USeed D e) : (pi D e * a.u) ^ 3 = 1 := by
  have hu : a.u ^ 3 = 1 := a.order ▸ pow_orderOf_eq_one a.u
  have hp : a.u * pi D e * a.u⁻¹ = pi D e * tau D e := (u_forward D e a).1
  have hpp : a.u ^ 2 * pi D e * (a.u ^ 2)⁻¹ = tau D e := by
    calc
      _ = a.u * (a.u * pi D e * a.u⁻¹) * a.u⁻¹ := by simp only [pow_two]; group
      _ = a.u * (pi D e * tau D e) * a.u⁻¹ := by rw [hp]
      _ = tau D e := by rw [← a.tau_u]; group
  calc
    _ = pi D e * (a.u * pi D e * a.u⁻¹) *
        (a.u ^ 2 * pi D e * (a.u ^ 2)⁻¹) * a.u ^ 3 := by
      simp only [pow_succ, pow_zero, one_mul]; group
    _ = pi D e * (pi D e * tau D e) * tau D e := by rw [hp, hpp, hu, mul_one]
    _ = 1 := by
      have h : modelElement 0 * (modelElement 0 * modelElement 3) * modelElement 3 = 1 := by decide +kernel
      simpa only [element, map_mul, map_one] using congrArg (D.a10ModelEmbedding e) h

private theorem pi_mul_u_mu (a : USeed D e) :
    (pi D e * a.u)⁻¹ * mu D e * (pi D e * a.u) = lam D e := by
  calc
    _ = a.u⁻¹ * ((pi D e)⁻¹ * mu D e * pi D e) * a.u := by group
    _ = a.u⁻¹ * mu D e * a.u := by
      rw [mul_assoc (pi D e)⁻¹, ← (commute_pi D e 1).eq, inv_mul_cancel_left]
    _ = _ := a.mu_u

private theorem pi_mul_u_lam (a : USeed D e) :
    (pi D e * a.u)⁻¹ * lam D e * (pi D e * a.u) = mu D e * lam D e := by
  calc
    _ = a.u⁻¹ * ((pi D e)⁻¹ * lam D e * pi D e) * a.u := by group
    _ = a.u⁻¹ * lam D e * a.u := by
      rw [mul_assoc (pi D e)⁻¹, ← (commute_pi D e 6).eq, inv_mul_cancel_left]
    _ = _ := a.lam_u

private theorem pi_mul_u_order (a : USeed D e) : orderOf (pi D e * a.u) = 3 := by
  have hn : pi D e * a.u ≠ 1 := by
    intro h
    have hm := pi_mul_u_mu D e a
    rw [h, inv_one, one_mul, mul_one] at hm
    have hmodel : modelElement 1 = modelElement 6 := D.a10ModelEmbedding_injective e hm
    exact (show modelElement 1 ≠ modelElement 6 from by decide +kernel) hmodel
  exact orderOf_eq_prime_iff.mpr ⟨pi_mul_u_cube D e a, hn⟩

/-- The last normalization in Held 4.2: choose u or pi*u to obtain inversion
by mu-prime, preserving exact order three and every required action.
The initial element and its tau-prime normalization are explicit inputs. -/
public theorem exists_uActor_of_centralizedSeed [Finite G] (a : UCentralizedSeed D e) :
    Nonempty (UActor D e) := by
  have hb : (mu' D e)⁻¹ = mu' D e := square_inv D e 2 (by decide)
  have hb2 : mu' D e * mu' D e = 1 := by simpa only [pow_two] using element_square D e 2 (by decide)
  rcases k_two_cases D e a with h | h
  · refine ⟨{
      u := a.u
      order := a.order
      mu_u := a.mu_u
      lam_u := a.lam_u
      tau'_commute := a.tau'_commute
      mu'_inverts := ?_ }⟩
    calc
      _ = mu' D e * a.u * (a.u⁻¹ * mu' D e * a.u⁻¹) := by rw [h]
      _ = mu' D e * mu' D e * a.u⁻¹ := by group
      _ = a.u⁻¹ := by rw [hb2, one_mul]
  · refine ⟨{
      u := pi D e * a.u
      order := pi_mul_u_order D e a.toUSeed
      mu_u := pi_mul_u_mu D e a.toUSeed
      lam_u := pi_mul_u_lam D e a.toUSeed
      tau'_commute := (commute_pi D e 4).mul_left a.tau'_commute
      mu'_inverts := ?_ }⟩
    have hinv : mu' D e * a.u * mu' D e = (pi D e * tau D e)⁻¹ * a.u⁻¹ := by
      calc
        _ = mu' D e * (a.u⁻¹ * mu' D e * a.u⁻¹)⁻¹ * a.u⁻¹ := by
          simp only [mul_inv_rev, inv_inv, hb, mul_assoc, mul_inv_cancel, mul_one]
        _ = mu' D e * (pi D e * tau D e * mu' D e)⁻¹ * a.u⁻¹ := by rw [h]
        _ = _ := by group
    calc
      _ = mu' D e * pi D e * (mu' D e * mu' D e) * a.u * mu' D e := by
        rw [hb2, mul_one]; group
      _ = (mu' D e * pi D e * mu' D e) * (mu' D e * a.u * mu' D e) := by group
      _ = pi D e * ((pi D e * tau D e)⁻¹ * a.u⁻¹) := by rw [(local_b_actions D e).1, hinv]
      _ = tau D e * a.u⁻¹ := by
        rw [(commute_pi D e 3).eq, mul_inv_rev, square_inv D e 3 (by decide)]
        group
      _ = a.u⁻¹ * pi D e := by rw [← a.pi_u]; group
      _ = (pi D e * a.u)⁻¹ := by rw [mul_inv_rev, square_inv D e 0 (by decide)]

/-- Held's first normalized actor, constructed from the supplied marked A₆.
The initial four actions, tau-prime centralization, and mu-prime inversion
are all established by the construction, including the replacement by pi*u
when required. -/
public theorem exists_uActor_of_markedSection [Finite G] [IsSimpleGroup G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj (pi D e) (lam D e))
    (hxi : ¬ IsConj (pi D e) (xi D e))
    (s : NoncentralAnalysis.AlternatingSixSection
      (centralizer ({D.a10NoncentralInvolution e} : Set G)))
    (m : MarkedSection D e s) : Nonempty (UActor D e) := by
  obtain ⟨a⟩ := exists_uSeed_of_markedSection D e hfusion hlam hxi s m
  obtain ⟨a'⟩ := exists_uCentralizedSeed_of_seed D e a
  exact exists_uActor_of_centralizedSeed D e a'

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
