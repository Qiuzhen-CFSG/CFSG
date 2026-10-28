module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.Actors
/-!
# Faithfulness from Held's normalized actors

The actual subgroup X = A<mu'> acts on the canonical normal subgroup A by
conjugation. A kernel element is in one of the two cosets of A. The eight
words for C_A(pi*mu) reduce it to 1, pi*mu, xi, or pi*mu*xi. The actor nu
excludes the two possibilities involving pi*mu. If xi centralizes
(tau')*alpha*(tau'), the source relations force
alpha⁻¹*mu'*alpha = mu'*xi*mu. This fuses mu with pi, contrary to nonfusion.
Thus the action is faithful once the separately specified actors exist.

The finite local calculations cover both allowed lambda and xi choices.
No recognition theorem or order of the full centralizer is used.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 4.2, pp.234--235.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
namespace FaithfulExclusion

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem local_kernel_cases : ∀ b d i (j : Bit),
    (coreWord b d i * Coordinates.mup ^ j.val) * coreTau b =
      coreTau b * (coreWord b d i * Coordinates.mup ^ j.val) →
    (coreWord b d i * Coordinates.mup ^ j.val) * coreSwap d =
      coreSwap d * (coreWord b d i * Coordinates.mup ^ j.val) →
    coreWord b d i * Coordinates.mup ^ j.val = 1 ∨
    coreWord b d i * Coordinates.mup ^ j.val = corePi ∨
    coreWord b d i * Coordinates.mup ^ j.val = normalizedXi d ∨
    coreWord b d i * Coordinates.mup ^ j.val = corePi * normalizedXi d := by
  intro b d ⟨i, j, k⟩ l
  fin_cases b <;> fin_cases d <;> fin_cases i <;> fin_cases j <;>
    fin_cases k <;> fin_cases l <;> decide +kernel

private theorem taup_xi : ∀ d : Bit,
    Coordinates.taup * normalizedXi d * Coordinates.taup =
      Coordinates.mup * normalizedXi d := by decide +kernel

private theorem local_fusion : ∀ d : Bit,
    (Coordinates.tau * Coordinates.taup)⁻¹ *
      (Coordinates.pi * normalizedXi d) * (Coordinates.tau * Coordinates.taup) =
      Coordinates.mu * Coordinates.mup * normalizedXi d := by decide +kernel

private theorem conj_eq_of_commute {G : Type*} [Group G] {a b : G}
    (h : Commute a b) : b⁻¹ * a * b = a := by
  rw [mul_assoc, h.eq, inv_mul_cancel_left]

variable {G : Type*} [Group G] {D : LocalData G}
  {e : D.centralizer ≃* CentralizerModels.a10Centralizer}
  {c : QuotientCore D e}

private theorem pi_not_commute_nu (a : Actors c) :
    ¬ Commute (D.a10ModelEmbedding e corePi) a.nu := by
  intro h
  have he : D.a10ModelEmbedding e (corePi * coreTau a.lamChoice) =
      D.a10ModelEmbedding e corePi := a.pi_nu.symm.trans (conj_eq_of_commute h)
  have ht : coreTau a.lamChoice = 1 := by
    have := D.a10ModelEmbedding_injective e he
    exact mul_left_cancel (this.trans (mul_one corePi).symm)
  have hn : ∀ b, coreTau b ≠ 1 := by decide +kernel
  exact hn _ ht

private theorem xi_centralizes_beta_fusion (a : Actors c)
    (h : Commute (D.a10ModelEmbedding e (normalizedXi a.xiChoice))
      (D.a10ModelEmbedding e Coordinates.taup * a.alpha *
        D.a10ModelEmbedding e Coordinates.taup)) :
    IsConj (D.a10ModelEmbedding e Coordinates.mu)
      (D.a10ModelEmbedding e Coordinates.pi) := by
  let f := D.a10ModelEmbedding e
  let x := f (normalizedXi a.xiChoice)
  let m := f Coordinates.mup
  let t := f Coordinates.taup
  have ht : t * t = 1 := by
    rw [← map_mul]
    have hl : Coordinates.taup * Coordinates.taup = 1 := by decide +kernel
    rw [hl, map_one]
  have htx : t * x * t = m * x := by
    simpa only [t, x, m, ← map_mul] using congrArg f (taup_xi a.xiChoice)
  have hc : Commute (m * x) a.alpha := by
    have hc := congrArg (fun z => t * z * t) h.eq
    change t * (x * (t * a.alpha * t)) * t =
      t * ((t * a.alpha * t) * x) * t at hc
    have he : (t * x * t) * a.alpha = a.alpha * (t * x * t) := by
      have htt (z : G) : t * (t * z) = z := by rw [← mul_assoc, ht, one_mul]
      simpa only [mul_assoc, ht, mul_one, one_mul, htt] using hc
    rwa [htx] at he
  have hconj : a.alpha⁻¹ * m * a.alpha = m * x * f Coordinates.mu := by
    have hc' := conj_eq_of_commute hc
    have hsplit : a.alpha⁻¹ * (m * x) * a.alpha =
        (a.alpha⁻¹ * m * a.alpha) * (a.alpha⁻¹ * x * a.alpha) := by group
    rw [hsplit, show a.alpha⁻¹ * x * a.alpha = f Coordinates.mu from a.xi_alpha] at hc'
    have hm : f Coordinates.mu * f Coordinates.mu = 1 := by
      rw [← map_mul]
      have hl : Coordinates.mu * Coordinates.mu = 1 := by decide +kernel
      rw [hl, map_one]
    have hc'' := congrArg (fun z => z * f Coordinates.mu) hc'
    simpa only [mul_assoc, hm, mul_one] using hc''
  have hr : IsConj (f Coordinates.mup) (f Coordinates.mu) := by
    apply f.map_isConj
    exact isConj_iff.mpr ⟨Coordinates.rho⁻¹, by decide +kernel⟩
  have hma : IsConj (f Coordinates.mup)
      (f (Coordinates.mu * Coordinates.mup * normalizedXi a.xiChoice)) := by
    refine isConj_iff.mpr ⟨a.alpha⁻¹, ?_⟩
    rw [inv_inv]
    change a.alpha⁻¹ * m * a.alpha = _
    rw [hconj]
    have hl : ∀ d, Coordinates.mup * normalizedXi d * Coordinates.mu =
        Coordinates.mu * Coordinates.mup * normalizedXi d := by decide +kernel
    simpa only [m, x, ← map_mul] using congrArg f (hl a.xiChoice)
  have hp : IsConj (f Coordinates.pi)
      (f (Coordinates.pi * normalizedXi a.xiChoice)) :=
    isConj_iff.mpr ⟨a.alpha⁻¹, by simpa only [inv_inv] using a.pi_alpha⟩
  have hl : IsConj (f (Coordinates.pi * normalizedXi a.xiChoice))
      (f (Coordinates.mu * Coordinates.mup * normalizedXi a.xiChoice)) := by
    apply f.map_isConj
    exact isConj_iff.mpr ⟨(Coordinates.tau * Coordinates.taup)⁻¹,
      by simpa only [inv_inv] using local_fusion a.xiChoice⟩
  exact hr.symm.trans (hma.trans (hp.trans hl).symm)

private theorem centralizing_coset_eq_one [Finite G] (a : Actors c)
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (y : G) (hy : y ∈ ambientCore c) (j : Bit)
    (hx : ∀ z ∈ ambientCore c,
      Commute (y * D.a10ModelEmbedding e (Coordinates.mup ^ j.val)) z) :
    y * D.a10ModelEmbedding e (Coordinates.mup ^ j.val) = 1 := by
  let f := D.a10ModelEmbedding e
  have hz : Commute (f (Coordinates.mup ^ j.val)) (f corePi) := by
    have hl : ∀ k : Bit, Coordinates.mup ^ k.val * corePi =
        corePi * Coordinates.mup ^ k.val := by decide +kernel
    exact show _ = _ from by simpa only [map_mul] using congrArg f (hl j)
  have hyc : Commute y (f corePi) := by
    have h := (hx _ a.pi_mem).mul_left hz.inv_left
    simpa only [f, mul_inv_cancel_right] using h
  obtain ⟨i, rfl⟩ := a.centralizer_words y hy hyc
  let w := coreWord a.lamChoice a.xiChoice i * Coordinates.mup ^ j.val
  have hw : ∀ z ∈ ambientCore c, Commute (f w) z := by
    simpa only [w, map_mul] using hx
  have ht : w * coreTau a.lamChoice = coreTau a.lamChoice * w := by
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul] using (hw _ a.tau_mem).eq
  have hs : w * coreSwap a.xiChoice = coreSwap a.xiChoice * w := by
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul] using (hw _ a.swap_mem).eq
  have hnotxi : ¬ Commute (f (normalizedXi a.xiChoice))
      (f Coordinates.taup * a.alpha * f Coordinates.taup) := by
    intro hh
    apply hfusion
    have hf := (xi_centralizes_beta_fusion a hh).symm
    simpa only [Coordinates.pi, LocalData.a10ModelEmbedding_central,
      Coordinates.mu, LocalData.a10NoncentralInvolution] using hf
  have h1 : f w = 1 := by
    rcases local_kernel_cases a.lamChoice a.xiChoice i j ht hs with h | h | h | h
    · simp only [show w = 1 from h, map_one]
    · exact (pi_not_commute_nu a (h ▸ hw a.nu a.nu_mem)).elim
    · exact (hnotxi (h ▸ hw _ a.beta_mem)).elim
    · have hh : Commute (f corePi * f (normalizedXi a.xiChoice)) a.nu := by
        simpa only [w, h, map_mul] using hw a.nu a.nu_mem
      have hp := hh.mul_left a.nu_xi.symm.inv_left
      have hp' : Commute (f corePi) a.nu := by
        simpa only [f, mul_inv_cancel_right] using hp
      exact (pi_not_commute_nu a hp').elim
  simpa only [w, map_mul] using h1

noncomputable section

@[expose] public def muPrime (D : LocalData G)
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) : C D e :=
  ⟨D.a10ModelEmbedding e Coordinates.mup, mem_centralizer_singleton_iff.mpr (by
    change D.a10ModelEmbedding e Coordinates.mup * D.a10ModelEmbedding e Coordinates.mu =
      D.a10ModelEmbedding e Coordinates.mu * D.a10ModelEmbedding e Coordinates.mup
    rw [← map_mul, ← map_mul]
    congr 1
    decide +kernel)⟩

public theorem muPrime_order : orderOf (muPrime D e) = 2 := by
  rw [muPrime, Subgroup.orderOf_mk,
    orderOf_injective (D.a10ModelEmbedding e) (D.a10ModelEmbedding_injective e)]
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

@[expose] public def extension (c : QuotientCore D e) : Subgroup (C D e) :=
  c.derivedLift ⊔ zpowers (muPrime D e)

@[expose] public def extensionCore (c : QuotientCore D e) : Subgroup (extension c) :=
  c.derivedLift.subgroupOf (extension c)

public instance extensionCore_normal : (extensionCore c).Normal :=
  inferInstanceAs (c.derivedLift.subgroupOf (extension c)).Normal

public def extensionCoreEquiv (c : QuotientCore D e) : extensionCore c ≃* c.derivedLift :=
  subgroupOfEquivOfLe le_sup_left

@[expose] public def coreAction (c : QuotientCore D e) : extension c →* MulAut c.derivedLift :=
  (MulAut.conjNormal (H := c.derivedLift)).comp (extension c).subtype

public theorem coreAction_injective_of_actors [Finite G] (a : Actors c)
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) :
    Function.Injective (coreAction c) := by
  classical
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hx' : coreAction c x = 1 := hx
  have hcentral : ∀ z ∈ ambientCore c, Commute (x.1 : G) z := by
    rintro _ ⟨z, hz, rfl⟩
    have hh := congrArg (fun b : c.derivedLift => (b.1 : G))
      (DFunLike.congr_fun hx' ⟨z, hz⟩)
    change (x.1 : G) * z * (x.1 : G)⁻¹ = z at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨y, hy, z, hz, hyz⟩ := mem_sup_of_normal_left.mp x.property
  rw [mem_zpowers_iff_mem_range_orderOf, muPrime_order] at hz
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
  have hj' : j < 2 := Finset.mem_range.mp hj
  have he : (x.1 : G) = (y : G) * D.a10ModelEmbedding e (Coordinates.mup ^ j) := by
    rw [← hyz]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, muPrime, map_pow]
  have ho := centralizing_coset_eq_one a hfusion (y : G)
    (mem_map_of_mem (C D e).subtype hy) ⟨j, hj'⟩ (by
      simpa only [he] using hcentral)
  have hxone : (x.1 : G) = 1 := he.trans ho
  exact Subtype.ext (Subtype.ext hxone)

public theorem extensionCore_centralizer_eq_bot_of_actors [Finite G] (a : Actors c)
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) :
    centralizer (extensionCore c : Set (extension c)) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have he : coreAction c x = 1 := by
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    change x.1 * y.1 * x.1⁻¹ = y.1
    have hy : y.1 ∈ extension c := mem_sup_left y.property
    have hh := (mem_centralizer_iff.mp hx) ⟨y.1, hy⟩ y.property
    have hh' : y.1 * x.1 = x.1 * y.1 := congrArg Subtype.val hh
    rw [← hh', mul_inv_cancel_right]
  exact (coreAction_injective_of_actors a hfusion) (he.trans (map_one _).symm)

end
end FaithfulExclusion
end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
