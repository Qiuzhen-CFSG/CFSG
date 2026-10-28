module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AmbientGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Bounds
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.SNormalizer.Overgroups

/-!
# Excluding the pi-lambda alternative in Held's Lemma 2.6

Assume pi is fused to mu but not to lambda. If pi were also fused to
pi*lambda, its centralizer would contain an order-64 group P containing
Q = C_H(pi*lambda), of order 32. Thus Q is normal in P.

The only nonidentity square in Q is pi*mu, so every automorphism of Q fixes
pi*mu. Its center consists of the eight words in pi, mu and lambda.
Conjugation by an element of P also fixes pi*lambda and preserves ambient
conjugacy classes. These constraints and lambda nonfusion force it to fix pi:
the possible images mu and pi*mu*lambda would send lambda into the pi class,
and the other five alternatives are excluded by injectivity or nonfusion.
Hence P lies in H and in C_G(pi*lambda), contradicting |Q| = 32.

This proves the pi-lambda case directly, using the same order-64 overgroup
as the source. The tau case still requires the ambient normalizer analysis.
All finite checks concern the 384 local words or the sixteen words in S;
none assumes an ambient recognition or centralizer order for mu.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.6, printed p.228.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates
local instance codeDecidableEq : DecidableEq BaseCode := inferInstance
local instance modelDecidableEq : DecidableEq H := inferInstance

private theorem piLambda_square_cases (x : sCaseCentralizer 1) :
    (x : H) ^ 2 = 1 ∨ (x : H) ^ 2 = Coordinates.pi * mu := by
  obtain ⟨b, hb⟩ := word_bijective.surjective (x : H)
  have hx := mem_centralizer_singleton_iff.mp x.property
  rw [← hb] at hx ⊢
  have ht : ∀ b : Code, word b * (Coordinates.pi * lam) = (Coordinates.pi * lam) * word b →
      word b ^ 2 = 1 ∨ word b ^ 2 = Coordinates.pi * mu := by decide +kernel
  exact ht b hx

private theorem piLambda_center_cases (x : sCaseCentralizer 1)
    (hx : x ∈ center (sCaseCentralizer 1)) :
    (x : H) = 1 ∨ (x : H) = Coordinates.pi ∨ (x : H) = mu ∨ (x : H) = Coordinates.pi * mu ∨
    (x : H) = lam ∨ (x : H) = Coordinates.pi * lam ∨ (x : H) = mu * lam ∨
    (x : H) = Coordinates.pi * mu * lam := by
  have hS : (x : H) ∈ modelS := by
    change (x : H) ∈ elementary 1
    rw [← elementary_selfCentralizing 1]
    exact mem_centralizer_iff.mpr (fun y hy => congrArg Subtype.val
      (mem_center_iff.mp hx ⟨y, modelS_le_sCaseCentralizer 1 hy⟩))
  obtain ⟨b, hb⟩ := (mem_elementary 1 _).mp hS
  have ht := congrArg Subtype.val (mem_center_iff.mp hx ⟨sCaseExtra 1, sCaseExtra_mem 1⟩)
  change sCaseExtra 1 * (x : H) = (x : H) * sCaseExtra 1 at ht
  rw [← hb] at ht ⊢
  have hf : ∀ b : BaseCode,
      sCaseExtra 1 * elementaryWord 1 b = elementaryWord 1 b * sCaseExtra 1 →
      elementaryWord 1 b = 1 ∨ elementaryWord 1 b = Coordinates.pi ∨
      elementaryWord 1 b = mu ∨ elementaryWord 1 b = Coordinates.pi * mu ∨
      elementaryWord 1 b = lam ∨ elementaryWord 1 b = Coordinates.pi * lam ∨
      elementaryWord 1 b = mu * lam ∨ elementaryWord 1 b = Coordinates.pi * mu * lam := by
    decide +kernel
  exact hf b ht

private def qPi : sCaseCentralizer 1 := ⟨Coordinates.pi, modelS_le_sCaseCentralizer 1 (pi_mem_elementary 1)⟩
private def qMu : sCaseCentralizer 1 := ⟨mu, modelS_le_sCaseCentralizer 1 (mu_mem_elementary 1)⟩
private def qLam : sCaseCentralizer 1 := ⟨lam, modelS_le_sCaseCentralizer 1 (elementaryGenerators_mem 1 3)⟩

private theorem qPi_central : qPi ∈ center (sCaseCentralizer 1) := by
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact mem_center_iff.mp modelCentralInvolution_mem_center y

private theorem automorphism_fixes_piMu (a : MulAut (sCaseCentralizer 1)) :
    a (qPi * qMu) = qPi * qMu := by
  let r : sCaseCentralizer 1 :=
    ⟨tau * sCaseExtra 1, (sCaseCentralizer 1).mul_mem
      (modelS_le_sCaseCentralizer 1 (elementaryGenerators_mem 1 2)) (sCaseExtra_mem 1)⟩
  have hr : r ^ 2 = qPi * qMu := by apply Subtype.ext; decide +kernel
  have hn : qPi * qMu ≠ 1 := by
    intro h
    have hv := congrArg Subtype.val h
    have hne : Coordinates.pi * mu ≠ 1 := by decide +kernel
    exact hne hv
  have hs := piLambda_square_cases (a r)
  change ((a r) ^ 2 : sCaseCentralizer 1).val = 1 ∨
    ((a r) ^ 2 : sCaseCentralizer 1).val = (qPi * qMu).val at hs
  rw [← map_pow, hr] at hs
  rcases hs with h | h
  · exact (hn (a.injective (by simpa using (Subtype.ext h : a (qPi * qMu) = 1)))).elim
  · exact Subtype.ext h

private theorem automorphism_fixes_pi (a : MulAut (sCaseCentralizer 1))
    (ha : a (qPi * qLam) = qPi * qLam)
    (p : H → Prop) (hp : ∀ y : sCaseCentralizer 1, p (a y : H) ↔ p (y : H))
    (hpi : p Coordinates.pi) (hmu : p mu) (hprod : p (Coordinates.pi * mu * lam))
    (hlam : ¬ p lam) (hmulam : ¬ p (mu * lam)) : a qPi = qPi := by
  have hc : a qPi ∈ center (sCaseCentralizer 1) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨t, rfl⟩ := a.surjective y
    simpa only [map_mul] using congrArg a (mem_center_iff.mp qPi_central t)
  have hfix := automorphism_fixes_piMu a
  have hpa : p (a qPi : H) := (hp qPi).mpr hpi
  have hna : ¬ p (a qLam : H) := fun h => hlam ((hp qLam).mp h)
  have he : (a qLam : H) = (a qPi : H)⁻¹ * (Coordinates.pi * lam) := by
    have h := congrArg Subtype.val ha
    change (a (qPi * qLam) : H) = Coordinates.pi * lam at h
    rw [map_mul] at h
    exact (eq_inv_mul_iff_mul_eq).mpr h
  rcases piLambda_center_cases (a qPi) hc with h | h | h | h | h | h | h | h
  · have h1 : a qPi = a 1 := by simpa using (Subtype.ext h : a qPi = 1)
    have hv := congrArg Subtype.val (a.injective h1)
    exact (show Coordinates.pi ≠ (1 : H) by decide +kernel) hv |>.elim
  · exact Subtype.ext h
  · have hv : (a qLam : H) = Coordinates.pi * mu * lam := by
      rw [he, h]
      decide +kernel
    exact (hna (hv ▸ hprod)).elim
  · have h1 : a qPi = a (qPi * qMu) := (Subtype.ext h).trans hfix.symm
    have hv := congrArg Subtype.val (a.injective h1)
    exact (show Coordinates.pi ≠ Coordinates.pi * mu by decide +kernel) hv |>.elim
  · exact (hlam (h ▸ hpa)).elim
  · have h1 : a qPi = a (qPi * qLam) := (Subtype.ext h).trans ha.symm
    have hv := congrArg Subtype.val (a.injective h1)
    exact (show Coordinates.pi ≠ Coordinates.pi * lam by decide +kernel) hv |>.elim
  · exact (hmulam (h ▸ hpa)).elim
  · have hv : (a qLam : H) = mu := by
      rw [he, h]
      decide +kernel
    exact (hna (hv ▸ hmu)).elim

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The pi-lambda alternative in the middle of Held 2.6 is impossible. -/
public theorem piLambda_nonfusion_of_mu
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam)) :
    ¬ IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * lam)) := by
  intro hpiLam
  obtain ⟨P, hP, hQP, hPC⟩ := exists_sCase_centralizer_overgroup D e 1 hpiLam
  let Q := ambientSCaseCentralizer D e 1
  let f := D.a10ModelEmbedding e
  let p (y : H) : Prop := IsConj D.z (f y)
  have hconj (g x : H) : IsConj (f x) (f (g * x * g⁻¹)) := by
    apply isConj_iff.mpr
    exact ⟨f g, by simp only [map_mul, map_inv]⟩
  have hprod : p (Coordinates.pi * mu * lam) := by
    have hx : xi * (Coordinates.pi * lam) * xi⁻¹ = Coordinates.pi * mu * lam := by
      decide +kernel
    have h := hpiLam.trans (hconj xi (Coordinates.pi * lam))
    rwa [hx] at h
  have hmulam : ¬ p (mu * lam) := by
    have hx : xi * lam * xi⁻¹ = mu * lam := by decide +kernel
    intro h
    apply hlam
    exact h.trans (hx ▸ hconj xi lam).symm
  have hpi : p Coordinates.pi := by
    change IsConj D.z (D.a10ModelEmbedding e Coordinates.pi)
    rw [D.a10ModelEmbedding_central e]
  have hQN : P ≤ normalizer (Q : Set G) := by
    have hi : (Q.subgroupOf P).index = 2 := by
      have h := (Q.subgroupOf P).index_mul_card
      rw [Nat.card_congr (subgroupOfEquivOfLe hQP).toEquiv,
        ambientSCaseCentralizer_card, hP] at h
      omega
    exact (normal_subgroupOf_iff_le_normalizer hQP).mp (normal_of_index_eq_two hi)
  have hPH : P ≤ D.centralizer := by
    intro g hg
    let b := Q.normalizerMonoidHom ⟨g, hQN hg⟩
    let c := (sCaseCentralizer 1).equivMapOfInjective f (D.a10ModelEmbedding_injective e)
    let a : MulAut (sCaseCentralizer 1) := c.trans (b.trans c.symm)
    have he (y : sCaseCentralizer 1) : f (a y : H) = g * f (y : H) * g⁻¹ := by
      have hh := congrArg Subtype.val (c.apply_symm_apply (b (c y)))
      exact hh
    have ha : a (qPi * qLam) = qPi * qLam := by
      apply Subtype.ext
      apply D.a10ModelEmbedding_injective e
      rw [he]
      have hh := mem_centralizer_singleton_iff.mp (hPC hg)
      change g * f (Coordinates.pi * lam) = f (Coordinates.pi * lam) * g at hh
      change g * f (Coordinates.pi * lam) * g⁻¹ = f (Coordinates.pi * lam)
      rw [hh, mul_inv_cancel_right]
    have hp (y : sCaseCentralizer 1) : p (a y : H) ↔ p (y : H) := by
      have hy : IsConj (f (y : H)) (f (a y : H)) := isConj_iff.mpr ⟨g, (he y).symm⟩
      exact ⟨fun h => h.trans hy.symm, fun h => h.trans hy⟩
    have hfix := automorphism_fixes_pi a ha p hp hpi hmu hprod hlam hmulam
    have hh := he qPi
    rw [hfix] at hh
    change f Coordinates.pi = g * f Coordinates.pi * g⁻¹ at hh
    rw [D.a10ModelEmbedding_central e] at hh
    exact mem_centralizer_singleton_iff.mpr ((mul_inv_eq_iff_eq_mul).mp hh.symm)
  have hPQ : P ≤ Q := by
    change P ≤ ambientSCaseCentralizer D e 1
    rw [ambientSCaseCentralizer_eq]
    exact le_inf hPH hPC
  have hd := card_dvd_of_le hPQ
  rw [hP, ambientSCaseCentralizer_card] at hd
  norm_num at hd

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
