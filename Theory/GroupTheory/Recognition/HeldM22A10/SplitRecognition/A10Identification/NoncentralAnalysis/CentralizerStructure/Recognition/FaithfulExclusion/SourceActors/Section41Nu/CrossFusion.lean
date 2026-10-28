module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Relations
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section41Nu.Seed
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section41Nu.Commutator
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section41Nu.CrossFusion.Local

/-!
# Crossing fusion for the supplied Section 4.1 actors

Put t = tau*lambda and let A be conjugation by the supplied alpha. The
centralizer Q of pi, mu and the marked xi has order 32. The alpha relations
normalize Q. Its two involutive noncentral cosets and A^3 = 1 restrict A(t)
to t, t*mu, t*xi or t*mu*xi; `CrossFusion.Local` checks this on binary words.

The seed gives t conjugate to mu, and g = nu*mu-prime sends the ordered
pair (pi,t) to (t*mu,pi*mu). In particular t*mu is conjugate to pi. Nonfusion
excludes A(t) = t*mu and A(t) = t*mu*xi. If A(t) = t*xi, alpha centralizes
both t*mu and pi*mu. Conjugating back by g would put this nontrivial actor
of exponent three in C_H(t), which has no nontrivial three-torsion. Thus
A(t) = t, and (t*xi)^alpha = t*mu proves the required crossing fusion.

This proof uses the seed constructed before the last paragraph of Held 4.1.
It replaces the L2-normalizer and Sylow argument of 2.14 in this conditional
setting. It neither assumes nor uses nu's eventual commutation with xi,
any total order for C_G(mu), or an alternating-six section. Both supplied
markings are preserved. Existence of the seed remains with its assembly owner.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Sections 2.13--2.15 and 4.1, pp.231--232.
Conjugation is x^g = g^-1*x*g.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
open Coordinates CrossFusion
local instance : DecidableEq H := inferInstance

universe u
variable {G : Type u} [Group G] [Finite G] {D : LocalData G}
  {e : D.centralizer ≃* CentralizerModels.a10Centralizer}

private theorem exists_qWord (b d : Bit) (y : G)
    (hp : Commute y (D.a10ModelEmbedding e Coordinates.pi))
    (hm : Commute y (D.a10ModelEmbedding e Coordinates.mu))
    (hx : Commute y (D.a10ModelEmbedding e (normalizedXi d))) :
    ∃ v, D.a10ModelEmbedding e (qWord b d v) = y := by
  have hy : y ∈ D.centralizer := mem_centralizer_singleton_iff.mpr (by
    simpa only [D.a10ModelEmbedding_central e] using hp.eq)
  rw [← D.a10ModelEmbedding_range e] at hy
  obtain ⟨w, rfl⟩ := hy
  obtain ⟨c, rfl⟩ := word_bijective.surjective w
  have hm' : word c * Coordinates.mu = Coordinates.mu * word c := by
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul] using hm.eq
  have hx' : word c * normalizedXi d = normalizedXi d * word c := by
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul] using hx.eq
  refine ⟨qRecode b d (qRead c), ?_⟩
  rw [recode_table, centralizer_table d c hm' hx']

private theorem alpha_image_in_Q {b d : Bit} (a : AlphaRelations D e d) (y : H)
    (hp : Commute y Coordinates.pi) (hm : Commute y Coordinates.mu)
    (hx : Commute y (normalizedXi d)) :
    ∃ v, D.a10ModelEmbedding e (qWord b d v) =
      (MulAut.conj a.alpha⁻¹) (D.a10ModelEmbedding e y) := by
  let f := D.a10ModelEmbedding e
  let A := MulAut.conj a.alpha⁻¹
  have hAp : A (f Coordinates.pi) = f (Coordinates.pi * normalizedXi d) := by
    simpa only [A, MulAut.conj_apply, inv_inv] using a.pi_alpha
  have hAm : A (f Coordinates.mu) = f (Coordinates.mu * normalizedXi d) := by
    simpa only [A, MulAut.conj_apply, inv_inv] using a.mu_alpha
  have hAx : A (f (normalizedXi d)) = f Coordinates.mu := by
    simpa only [A, MulAut.conj_apply, inv_inv] using a.xi_alpha
  have h₁ := (hp.map f).map A
  have h₂ := (hm.map f).map A
  have h₃ := (hx.map f).map A
  rw [hAp] at h₁
  rw [hAm] at h₂
  rw [hAx] at h₃
  have hlocal : ∀ d,
      (Coordinates.mu * normalizedXi d) * Coordinates.mu = normalizedXi d ∧
      (Coordinates.pi * normalizedXi d) * normalizedXi d = Coordinates.pi := by
    decide +kernel
  have hξ : Commute (A (f y)) (f (normalizedXi d)) := by
    simpa only [← map_mul, (hlocal d).1] using h₂.mul_right h₃
  have hπ : Commute (A (f y)) (f Coordinates.pi) := by
    simpa only [← map_mul, (hlocal d).2] using h₁.mul_right hξ
  exact exists_qWord b d _ hπ h₃ hξ

omit [Finite G] in
private theorem cube_conj (g : G) (hg : g ^ 3 = 1) (x : G) :
    (MulAut.conj g⁻¹) ((MulAut.conj g⁻¹) ((MulAut.conj g⁻¹) x)) = x := by
  have he : g * g * g = 1 := by simpa only [pow_succ, pow_zero, one_mul] using hg
  simp only [MulAut.conj_apply, inv_inv]
  calc
    _ = (g * g * g)⁻¹ * x * (g * g * g) := by group
    _ = x := by rw [he]; group

private theorem alpha_tau_alternatives {b d : Bit} (a : AlphaRelations D e d) :
    (MulAut.conj a.alpha⁻¹) (D.a10ModelEmbedding e (coreTau b)) =
        D.a10ModelEmbedding e (coreTau b) ∨
    (MulAut.conj a.alpha⁻¹) (D.a10ModelEmbedding e (coreTau b)) =
        D.a10ModelEmbedding e (coreTau b * Coordinates.mu) ∨
    (MulAut.conj a.alpha⁻¹) (D.a10ModelEmbedding e (coreTau b)) =
        D.a10ModelEmbedding e (coreTau b * normalizedXi d) ∨
    (MulAut.conj a.alpha⁻¹) (D.a10ModelEmbedding e (coreTau b)) =
        D.a10ModelEmbedding e (coreTau b * Coordinates.mu * normalizedXi d) := by
  let f := D.a10ModelEmbedding e
  let A := MulAut.conj a.alpha⁻¹
  have ht : ∀ b d, Commute (coreTau b) Coordinates.pi ∧
      Commute (coreTau b) Coordinates.mu ∧ Commute (coreTau b) (normalizedXi d) := by
    unfold Commute SemiconjBy
    decide +kernel
  have hm : ∀ d, Commute mup Coordinates.pi ∧ Commute mup Coordinates.mu ∧
      Commute mup (normalizedXi d) := by
    unfold Commute SemiconjBy
    decide +kernel
  obtain ⟨s, hs⟩ := alpha_image_in_Q (b := b) a (coreTau b)
    (ht b d).1 (ht b d).2.1 (ht b d).2.2
  obtain ⟨r, hr⟩ := alpha_image_in_Q (b := b) a mup (hm d).1 (hm d).2.1 (hm d).2.2
  have hAp : A (f Coordinates.pi) = f (Coordinates.pi * normalizedXi d) := by
    simpa only [A, MulAut.conj_apply, inv_inv] using a.pi_alpha
  have hAm : A (f Coordinates.mu) = f (Coordinates.mu * normalizedXi d) := by
    simpa only [A, MulAut.conj_apply, inv_inv] using a.mu_alpha
  have hAx : A (f (normalizedXi d)) = f Coordinates.mu := by
    simpa only [A, MulAut.conj_apply, inv_inv] using a.xi_alpha
  have ha (v : QCode) : A (f (qWord b d v)) = f (qWord b d (qAction s r v)) := by
    rw [qWord_action]
    conv_lhs => rw [qWord]
    simp only [qImage, map_mul, map_pow, hAp, hAm, hAx]
    rw [hs, hr]
  have hcube (y : G) : A (A (A y)) = y := cube_conj a.alpha a.cube y
  have hzero : qWord b d 0 = 1 := by simp [qWord]
  have hst : qWord b d (0,0,0,1,0) = coreTau b := by simp [qWord]
  have hrt : qWord b d (0,0,0,0,1) = mup := by simp [qWord]
  have hsq (v : QCode) (x : H) (hv : f (qWord b d v) = A (f x)) (hx : x * x = 1) :
      qMul v v = 0 := by
    apply qWord_injective b d
    apply D.a10ModelEmbedding_injective e
    change f _ = f _
    rw [qWord_mul, map_mul, hv, ← map_mul, ← map_mul, hx, map_one, map_one,
      hzero, map_one]
  have htt : ∀ b, coreTau b * coreTau b = 1 := by decide +kernel
  have hs2 : qMul s s = 0 := hsq s _ hs (htt b)
  have hr2 : qMul r r = 0 := hsq r _ hr (by decide +kernel)
  have hsc : qAction s r (qAction s r s) = (0,0,0,1,0) := by
    apply qWord_injective b d
    apply D.a10ModelEmbedding_injective e
    change f _ = f _
    rw [← ha, ← ha, hs, hcube, hst]
  have hrc : qAction s r (qAction s r r) = (0,0,0,0,1) := by
    apply qWord_injective b d
    apply D.a10ModelEmbedding_injective e
    change f _ = f _
    rw [← ha, ← ha, hr, hcube, hrt]
  have hwords : ∀ b d,
      qWord b d (0,1,0,1,0) = coreTau b * Coordinates.mu ∧
      qWord b d (0,0,1,1,0) = coreTau b * normalizedXi d ∧
      qWord b d (0,1,1,1,0) = coreTau b * Coordinates.mu * normalizedXi d := by
    decide +kernel
  rcases action_table s r hs2 hr2 hsc hrc with h | h | h | h
  · exact Or.inl (hs.symm.trans (congrArg f (h ▸ hst)))
  · exact Or.inr (Or.inl (hs.symm.trans (congrArg f (h ▸ (hwords b d).1))))
  · exact Or.inr (Or.inr (Or.inl (hs.symm.trans (congrArg f (h ▸ (hwords b d).2.1)))))
  · exact Or.inr (Or.inr (Or.inr (hs.symm.trans (congrArg f (h ▸ (hwords b d).2.2)))))

omit [Finite G] in
private theorem seed_pair {b : Bit} (n : NuSeedRelations D e b) :
    (MulAut.conj (n.nu * D.a10ModelEmbedding e mup)⁻¹)
        (D.a10ModelEmbedding e Coordinates.pi) =
      D.a10ModelEmbedding e (coreTau b * Coordinates.mu) ∧
    (MulAut.conj (n.nu * D.a10ModelEmbedding e mup)⁻¹)
        (D.a10ModelEmbedding e (coreTau b)) = D.a10ModelEmbedding e corePi := by
  let f := D.a10ModelEmbedding e
  have hlocal : ∀ b,
      mup⁻¹ * (Coordinates.pi * tau * normalizedLam b) * mup = coreTau b * Coordinates.mu ∧
      mup⁻¹ * corePi * mup = corePi := by decide +kernel
  simp only [MulAut.conj_apply, inv_inv]
  constructor
  · change (n.nu * f mup)⁻¹ * f Coordinates.pi * (n.nu * f mup) = _
    calc
      _ = (f mup)⁻¹ * (n.nu⁻¹ * f Coordinates.pi * n.nu) * f mup := by group
      _ = f (mup⁻¹ * (Coordinates.pi * tau * normalizedLam b) * mup) := by
        rw [n.pi_nu]
        simp only [f, map_mul, map_inv]
      _ = _ := congrArg f (hlocal b).1
  · change (n.nu * f mup)⁻¹ * f (coreTau b) * (n.nu * f mup) = _
    calc
      _ = (f mup)⁻¹ * (n.nu⁻¹ * f (coreTau b) * n.nu) * f mup := by group
      _ = f (mup⁻¹ * corePi * mup) := by
        rw [n.coreTau_conjugation]
        simp only [f, map_mul, map_inv]
      _ = _ := congrArg f (hlocal b).2

private theorem seed_pi_isConj_tau_mu {b : Bit} (n : NuSeedRelations D e b) :
    IsConj D.z (D.a10ModelEmbedding e (coreTau b * Coordinates.mu)) := by
  rw [← D.a10ModelEmbedding_central e]
  exact isConj_iff.mpr ⟨(n.nu * D.a10ModelEmbedding e mup)⁻¹, (seed_pair n).1⟩

omit [Finite G] in
private theorem seed_tau_isConj_mu {b : Bit} (n : NuSeedRelations D e b) :
    IsConj (D.a10ModelEmbedding e (coreTau b)) (D.a10ModelEmbedding e Coordinates.mu) := by
  have ht : IsConj (D.a10ModelEmbedding e (coreTau b)) (D.a10ModelEmbedding e corePi) :=
    isConj_iff.mpr ⟨n.nu⁻¹, by simpa only [inv_inv] using n.coreTau_conjugation⟩
  apply ht.trans
  have he : taup⁻¹ * corePi * taup = Coordinates.mu := by decide +kernel
  exact isConj_iff.mpr ⟨(D.a10ModelEmbedding e taup)⁻¹, by
    simpa only [inv_inv, ← map_inv, ← map_mul] using congrArg (D.a10ModelEmbedding e) he⟩

omit [Finite G] in
private theorem alpha_ne_one {d : Bit} (a : AlphaRelations D e d) : a.alpha ≠ 1 := by
  intro h
  have he := a.xi_alpha
  rw [h, inv_one, one_mul, mul_one] at he
  have hlocal : ∀ d, normalizedXi d ≠ Coordinates.mu := by decide +kernel
  exact hlocal d (D.a10ModelEmbedding_injective e he)

private theorem alpha_not_commute_tau_mu {b d : Bit} (a : AlphaRelations D e d)
    (n : NuSeedRelations D e b) :
    ¬ Commute a.alpha (D.a10ModelEmbedding e (coreTau b * Coordinates.mu)) := by
  intro h
  let f := D.a10ModelEmbedding e
  let g := n.nu * f mup
  let B := MulAut.conj g
  have hp : B (f (coreTau b * Coordinates.mu)) = f Coordinates.pi := by
    rw [← (seed_pair n).1]
    simp only [B, g, f, MulAut.conj_apply, inv_inv]
    group
  have ht : B (f corePi) = f (coreTau b) := by
    rw [← (seed_pair n).2]
    simp only [B, g, f, MulAut.conj_apply, inv_inv]
    group
  have h₁ := h.map B
  have h₂ := a.corePi_commute.map B
  rw [hp] at h₁
  rw [ht] at h₂
  have hmem : B a.alpha ∈ D.centralizer := mem_centralizer_singleton_iff.mpr (by
    simpa only [f, D.a10ModelEmbedding_central e] using h₁.eq)
  rw [← D.a10ModelEmbedding_range e] at hmem
  obtain ⟨w, hw⟩ := hmem
  obtain ⟨c, rfl⟩ := word_bijective.surjective w
  have hc : word c * coreTau b = coreTau b * word c := by
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul, hw] using h₂.eq
  have hcub : (word c) ^ 3 = 1 := by
    apply D.a10ModelEmbedding_injective e
    rw [map_pow, hw, ← map_pow, a.cube, map_one, map_one]
  have ha : a.alpha = 1 := by
    apply B.injective
    rw [map_one, ← hw, local_cube b c hc hcub, map_one]
  exact alpha_ne_one a ha

omit [Finite G] in
private theorem commute_of_conj_eq {g x : G} (h : (MulAut.conj g⁻¹) x = x) : Commute g x := by
  change g * x = x * g
  simp only [MulAut.conj_apply, inv_inv] at h
  calc
    _ = g * (g⁻¹ * x * g) := by rw [h]
    _ = _ := by group

private theorem alpha_commutes_tau {b d : Bit} (a : AlphaRelations D e d)
    (n : NuSeedRelations D e b)
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) :
    Commute a.alpha (D.a10ModelEmbedding e (coreTau b)) := by
  let f := D.a10ModelEmbedding e
  let A := MulAut.conj a.alpha⁻¹
  have hmu : A (f Coordinates.mu) = f (Coordinates.mu * normalizedXi d) := by
    simpa only [A, MulAut.conj_apply, inv_inv] using a.mu_alpha
  have htm := seed_pi_isConj_tau_mu n
  have ht := seed_tau_isConj_mu n
  rcases alpha_tau_alternatives (b := b) a with h | h | h | h
  · exact commute_of_conj_eq h
  · have hc : IsConj (f (coreTau b)) (f (coreTau b * Coordinates.mu)) :=
      isConj_iff.mpr ⟨a.alpha⁻¹, h⟩
    exact (hfusion ((htm.trans hc.symm).trans ht)).elim
  · have he : A (f (coreTau b * Coordinates.mu)) = f (coreTau b * Coordinates.mu) := by
      have hl : ∀ b d, (coreTau b * normalizedXi d) *
          (Coordinates.mu * normalizedXi d) = coreTau b * Coordinates.mu := by decide +kernel
      rw [map_mul, map_mul, h, hmu, ← map_mul, hl b d]
      simp only [f, map_mul]
    exact (alpha_not_commute_tau_mu a n (commute_of_conj_eq he)).elim
  · have he : A (f (coreTau b * Coordinates.mu)) = f (coreTau b) := by
      have hl : ∀ b d, (coreTau b * Coordinates.mu * normalizedXi d) *
          (Coordinates.mu * normalizedXi d) = coreTau b := by decide +kernel
      rw [map_mul, map_mul, h, hmu, ← map_mul, hl b d]
    have hc : IsConj (f (coreTau b * Coordinates.mu)) (f (coreTau b)) :=
      isConj_iff.mpr ⟨a.alpha⁻¹, he⟩
    exact (hfusion ((htm.trans hc).trans ht)).elim

/-- Held 2.14 crossing fusion for both supplied markings, conditional only
on the earlier alpha and nu seed relations. Simplicity is unnecessary for this
conditional conclusion. The seed is not assumed to commute with xi. -/
public theorem crossingFusion_of_seed {b d : Bit} (a : AlphaRelations D e d)
    (n : NuSeedRelations D e b)
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) :
    IsConj D.z (D.a10ModelEmbedding e (coreTau b * normalizedXi d)) := by
  let f := D.a10ModelEmbedding e
  let A := MulAut.conj a.alpha⁻¹
  have ht : A (f (coreTau b)) = f (coreTau b) := by
    simp only [A, MulAut.conj_apply, inv_inv]
    rw [mul_assoc, ← (alpha_commutes_tau a n hfusion).eq, inv_mul_cancel_left]
  have hxi : A (f (normalizedXi d)) = f Coordinates.mu := by
    simpa only [A, MulAut.conj_apply, inv_inv] using a.xi_alpha
  have h : A (f (coreTau b * normalizedXi d)) = f (coreTau b * Coordinates.mu) := by
    rw [map_mul, map_mul, ht, hxi, ← map_mul]
  exact (seed_pi_isConj_tau_mu n).trans (isConj_iff.mpr ⟨a.alpha⁻¹, h⟩).symm

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
