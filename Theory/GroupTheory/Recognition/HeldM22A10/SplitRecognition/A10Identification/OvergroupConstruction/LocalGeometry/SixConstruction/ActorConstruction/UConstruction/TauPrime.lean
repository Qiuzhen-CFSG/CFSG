module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction.UConstruction.Seed
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
import Mathlib.Tactic.Group

/-!
# Centralizing tau-prime in Held's first actor construction

Given an initial order-three seed, put x = (tau-prime)^u. The seed actions
show that x centralizes pi and tau, that x² = 1, and that (lambda*x)² = tau.
Inside the known centralizer of pi, its 384 normal forms restrict x to
{tau-prime, tau*tau-prime, pi*tau-prime, pi*tau*tau-prime}.

Conjugation by u permutes these four points and its cube is the identity,
so it fixes one of them. The elements 1, lambda, mu, mu*lambda move each
point to tau-prime and centralize all four seed marks. Conjugating u by
the corresponding element therefore preserves its exact order and all
four actions, while making it centralize tau-prime. The finite model
calculations and the four-point fixed-point argument are kernel checked.

This proves the normalization from an explicit `USeed`; construction of
that initial seed is a separate argument.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 4.2, printed p.233.
The source convention is x^g = g⁻¹*x*g.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction

private instance modelDecidableEq : DecidableEq CentralizerModels.a10Centralizer := inferInstance

private def modelPoint (i : Fin 4) : CentralizerModels.a10Centralizer :=
  ![modelElement 4, modelElement 3 * modelElement 4,
    modelElement 0 * modelElement 4, modelElement 0 * modelElement 3 * modelElement 4] i

private def modelAdjuster (i : Fin 4) : CentralizerModels.a10Centralizer :=
  ![1, modelElement 6, modelElement 1, modelElement 1 * modelElement 6] i

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem model_classification (x : CentralizerModels.a10Centralizer)
    (ht : x * modelElement 3 = modelElement 3 * x)
    (hl : (modelElement 6 * x) ^ 2 = modelElement 3) (hx : x ^ 2 = 1) :
    ∃ i, x = modelPoint i := by
  obtain ⟨c, rfl⟩ := NoncentralAnalysis.Coordinates.word_bijective.surjective x
  have table : ∀ c : NoncentralAnalysis.Coordinates.Code,
      let x := NoncentralAnalysis.Coordinates.word c
      x * modelElement 3 = modelElement 3 * x →
      (modelElement 6 * x) ^ 2 = modelElement 3 →
      x ^ 2 = 1 → ∃ i, x = modelPoint i := by
    dsimp only
    decide +kernel
  exact table c ht hl hx

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

private noncomputable def point (i : Fin 4) : G :=
  ![tau' D e, tau D e * tau' D e, pi D e * tau' D e,
    pi D e * tau D e * tau' D e] i

private theorem point_eq (i : Fin 4) :
    D.a10ModelEmbedding e (modelPoint i) = point D e i := by
  fin_cases i <;> simp [point, modelPoint, element]

private theorem point_injective : Function.Injective (point D e) := by
  intro i j h
  have hi : Function.Injective modelPoint := by decide +kernel
  apply hi
  apply D.a10ModelEmbedding_injective e
  simpa only [point_eq] using h

private theorem point_classification [Finite G] (x : G)
    (hp : Commute x (pi D e)) (ht : Commute x (tau D e))
    (hl : (lam D e * x) ^ 2 = tau D e) (hx : x ^ 2 = 1) :
    ∃ i, x = point D e i := by
  have hxH : x ∈ (D.a10ModelEmbedding e).range := by
    rw [D.a10ModelEmbedding_range]
    apply mem_centralizer_singleton_iff.mpr
    simpa only [← pi_eq D e] using hp.eq
  obtain ⟨y, rfl⟩ := hxH
  have ht' : y * modelElement 3 = modelElement 3 * y := by
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul, element] using ht.eq
  have hl' : (modelElement 6 * y) ^ 2 = modelElement 3 := by
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul, map_pow, element] using hl
  have hy : y ^ 2 = 1 := by
    apply D.a10ModelEmbedding_injective e
    simpa only [map_pow, map_one] using hx
  obtain ⟨i, rfl⟩ := model_classification y ht' hl' hy
  exact ⟨i, point_eq D e i⟩

private theorem tau_product : tau D e * (pi D e * tau D e) = pi D e := by
  have h : modelElement 3 * (modelElement 0 * modelElement 3) = modelElement 0 := by
    decide +kernel
  simpa only [map_mul, element] using congrArg (D.a10ModelEmbedding e) h

private theorem first_image [Finite G] (a : USeed D e) :
    ∃ i, (MulAut.conj a.u⁻¹) (tau' D e) = point D e i := by
  let f := MulAut.conj a.u⁻¹
  have hp : f (pi D e) = tau D e := by
    simpa only [f, MulAut.conj_apply, inv_inv] using a.pi_u
  have ht : f (tau D e) = pi D e * tau D e := by
    simpa only [f, MulAut.conj_apply, inv_inv] using a.tau_u
  have hm : f (mu D e) = lam D e := by
    simpa only [f, MulAut.conj_apply, inv_inv] using a.mu_u
  have hpt : f (pi D e * tau D e) = pi D e := by
    rw [map_mul, hp, ht, tau_product D e]
  have hcomm : Commute (tau' D e) (pi D e * tau D e) := by
    have h : modelElement 4 * (modelElement 0 * modelElement 3) =
        (modelElement 0 * modelElement 3) * modelElement 4 := by decide +kernel
    change _ * _ = _ * _
    simpa only [map_mul, element] using congrArg (D.a10ModelEmbedding e) h
  have hsquare : (mu D e * tau' D e) ^ 2 = pi D e := by
    have h : (modelElement 1 * modelElement 4) ^ 2 = modelElement 0 := by decide +kernel
    simpa only [map_mul, map_pow, element] using congrArg (D.a10ModelEmbedding e) h
  apply point_classification D e (f (tau' D e))
  · simpa only [MulEquiv.coe_toMonoidHom, hpt] using hcomm.map f.toMonoidHom
  · simpa only [MulEquiv.coe_toMonoidHom, hp] using
      ((commute_pi D e 4).symm.map f.toMonoidHom)
  · simpa only [map_pow, map_mul, hm, hp] using congrArg f hsquare
  · simpa only [map_pow, map_one] using congrArg f (element_square D e 4 (by decide))

private theorem point_multiplication (i : Fin 4) :
    (∃ j, pi D e * point D e i = point D e j) ∧
    (∃ j, tau D e * point D e i = point D e j) ∧
    (∃ j, pi D e * tau D e * point D e i = point D e j) := by
  have table : ∀ i : Fin 4,
      (∃ j, modelElement 0 * modelPoint i = modelPoint j) ∧
      (∃ j, modelElement 3 * modelPoint i = modelPoint j) ∧
      (∃ j, modelElement 0 * modelElement 3 * modelPoint i = modelPoint j) := by
    decide +kernel
  obtain ⟨⟨j, hj⟩, ⟨k, hk⟩, ⟨l, hl⟩⟩ := table i
  exact ⟨⟨j, by simpa only [map_mul, point_eq, element] using congrArg (D.a10ModelEmbedding e) hj⟩,
    ⟨k, by simpa only [map_mul, point_eq, element] using congrArg (D.a10ModelEmbedding e) hk⟩,
    ⟨l, by simpa only [map_mul, point_eq, element] using congrArg (D.a10ModelEmbedding e) hl⟩⟩

private theorem point_invariance [Finite G] (a : USeed D e) (i : Fin 4) :
    ∃ j, (MulAut.conj a.u⁻¹) (point D e i) = point D e j := by
  let f := MulAut.conj a.u⁻¹
  have hp : f (pi D e) = tau D e := by
    simpa only [f, MulAut.conj_apply, inv_inv] using a.pi_u
  have ht : f (tau D e) = pi D e * tau D e := by
    simpa only [f, MulAut.conj_apply, inv_inv] using a.tau_u
  obtain ⟨j, hj⟩ := first_image D e a
  change f (tau' D e) = point D e j at hj
  fin_cases i
  · exact ⟨j, hj⟩
  · change ∃ k, f (tau D e * tau' D e) = point D e k
    rw [map_mul, ht, hj]
    exact (point_multiplication D e j).2.2
  · change ∃ k, f (pi D e * tau' D e) = point D e k
    rw [map_mul, hp, hj]
    exact (point_multiplication D e j).2.1
  · change ∃ k, f (pi D e * tau D e * tau' D e) = point D e k
    rw [map_mul, map_mul, hp, ht, hj, tau_product D e]
    exact (point_multiplication D e j).1

private theorem conj_cube (a : USeed D e) (x : G) :
    (MulAut.conj a.u⁻¹) ((MulAut.conj a.u⁻¹) ((MulAut.conj a.u⁻¹) x)) = x := by
  have hu : a.u ^ 3 = 1 := a.order ▸ pow_orderOf_eq_one a.u
  simp only [MulAut.conj_apply, inv_inv]
  calc
    _ = (a.u ^ 3)⁻¹ * x * a.u ^ 3 := by
      simp only [pow_succ, pow_zero]
      group
    _ = x := by rw [hu]; simp

private theorem point_permutation [Finite G] (a : USeed D e) :
    ∃ f : Perm (Fin 4),
      (∀ i, (MulAut.conj a.u⁻¹) (point D e i) = point D e (f i)) ∧
      (∀ i, f (f (f i)) = i) := by
  classical
  choose f hf using point_invariance D e a
  have hf3 (i) : f (f (f i)) = i := by
    apply point_injective D e
    calc
      point D e (f (f (f i))) =
          (MulAut.conj a.u⁻¹) ((MulAut.conj a.u⁻¹) ((MulAut.conj a.u⁻¹) (point D e i))) := by
        rw [hf, hf, hf]
      _ = point D e i := conj_cube D e a _
  exact ⟨⟨f, (fun i => f (f i)), hf3, hf3⟩, hf, hf3⟩

private theorem point_fixed [Finite G] (a : USeed D e) :
    ∃ i, Commute a.u (point D e i) := by
  obtain ⟨f, hf, hf3⟩ := point_permutation D e a
  have four_fixed : ∀ f : Fin 4 → Fin 4,
      (∀ i, f (f (f i)) = i) → ∃ i, f i = i := by decide +kernel
  obtain ⟨i, hi⟩ := four_fixed f hf3
  have hfix : a.u⁻¹ * point D e i * a.u = point D e i := by
    simpa only [hi, MulAut.conj_apply, inv_inv] using hf i
  refine ⟨i, ?_⟩
  change a.u * point D e i = point D e i * a.u
  calc
    _ = a.u * (a.u⁻¹ * point D e i * a.u) := by rw [hfix]
    _ = _ := by group

private theorem point_transitivity (i : Fin 4) :
    ∃ q : G, q ∈ closure ({mu D e, lam D e} : Set G) ∧
      q * point D e i * q⁻¹ = tau' D e ∧
      q * pi D e * q⁻¹ = pi D e ∧
      q * tau D e * q⁻¹ = tau D e ∧
      q * mu D e * q⁻¹ = mu D e ∧
      q * lam D e * q⁻¹ = lam D e := by
  have table : ∀ i : Fin 4,
      modelAdjuster i * modelPoint i * (modelAdjuster i)⁻¹ = modelElement 4 ∧
      modelAdjuster i * modelElement 0 * (modelAdjuster i)⁻¹ = modelElement 0 ∧
      modelAdjuster i * modelElement 3 * (modelAdjuster i)⁻¹ = modelElement 3 ∧
      modelAdjuster i * modelElement 1 * (modelAdjuster i)⁻¹ = modelElement 1 ∧
      modelAdjuster i * modelElement 6 * (modelAdjuster i)⁻¹ = modelElement 6 := by
    decide +kernel
  let q := D.a10ModelEmbedding e (modelAdjuster i)
  refine ⟨q, ?_, ?_⟩
  · have hm : mu D e ∈ closure ({mu D e, lam D e} : Set G) := subset_closure (by simp)
    have hl : lam D e ∈ closure ({mu D e, lam D e} : Set G) := subset_closure (by simp)
    fin_cases i
    · change D.a10ModelEmbedding e 1 ∈ _
      rw [map_one]
      exact (closure ({mu D e, lam D e} : Set G)).one_mem
    · exact hl
    · exact hm
    · change D.a10ModelEmbedding e (modelElement 1 * modelElement 6) ∈ _
      rw [map_mul]
      exact (closure ({mu D e, lam D e} : Set G)).mul_mem hm hl
  · obtain ⟨hi, hp, ht, hm, hl⟩ := table i
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | simpa only [map_mul, map_inv, point_eq, element, q] using congrArg (D.a10ModelEmbedding e) hi
      | simpa only [map_mul, map_inv, point_eq, element, q] using congrArg (D.a10ModelEmbedding e) hp
      | simpa only [map_mul, map_inv, point_eq, element, q] using congrArg (D.a10ModelEmbedding e) ht
      | simpa only [map_mul, map_inv, point_eq, element, q] using congrArg (D.a10ModelEmbedding e) hm
      | simpa only [map_mul, map_inv, point_eq, element, q] using congrArg (D.a10ModelEmbedding e) hl

/-- The first normalization in Held 4.2: a conjugate of the supplied seed
centralizes tau-prime, with exact order three and all four seed actions. -/
public theorem exists_uCentralizedSeed_of_seed [Finite G] (a : USeed D e) :
    Nonempty (UCentralizedSeed D e) := by
  obtain ⟨i, hi⟩ := point_fixed D e a
  obtain ⟨q, _, hq, hp, ht, hm, hl⟩ := point_transitivity D e i
  let f := MulAut.conj q
  have fp : f (pi D e) = pi D e := hp
  have ft : f (tau D e) = tau D e := ht
  have fm : f (mu D e) = mu D e := hm
  have fl : f (lam D e) = lam D e := hl
  have fq : f (point D e i) = tau' D e := hq
  refine ⟨{
    u := f a.u
    order := (f.orderOf_eq a.u).trans a.order
    pi_u := ?_
    tau_u := ?_
    mu_u := ?_
    lam_u := ?_
    tau'_commute := ?_ }⟩
  · simpa only [map_mul, map_inv, fp, ft] using congrArg f a.pi_u
  · simpa only [map_mul, map_inv, fp, ft] using congrArg f a.tau_u
  · simpa only [map_mul, map_inv, fm, fl] using congrArg f a.mu_u
  · simpa only [map_mul, map_inv, fm, fl] using congrArg f a.lam_u
  · simpa only [MulEquiv.coe_toMonoidHom, fq] using hi.map f.toMonoidHom

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
