module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Relations
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha.Geometry

/-!
# Extracting Held's Section 2.13 actor

Given the earlier fusion of a choice of xi with mu and the geometric overgroup
L, Cauchy's theorem supplies an element of order three. It moves pi because
L intersects H in a group of order 64. Nonfusion of pi and mu restricts the
pi orbit in the eight-group to pi, pi*xi and pi*mu*xi. Choosing the element
or its inverse gives pi^alpha = pi*xi; its cube then forces xi^alpha = mu.
Centralization of pi*mu is inherited from L.

The unconditional construction still needs the earlier xi-fusion theorem
and the Sylow/normalizer construction of L. These are explicit premises here;
no A6 section, core, global recognition or order of C_G(mu) is assumed.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Sections 2.9--2.13, pp.229--231.
Conjugation means x^g = g⁻¹*x*g.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
namespace FaithfulExclusion
open Coordinates

universe u
variable {G : Type u} [Group G] {D : LocalData G}
  {e : D.centralizer ≃* CentralizerModels.a10Centralizer}

private theorem conj_isConj (g x : G) : IsConj x (g⁻¹ * x * g) :=
  isConj_iff.mpr ⟨g⁻¹, by simp only [inv_inv]⟩

private theorem pi_conjugate_choices [Finite G] (d : Bit)
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hxi : IsConj (D.a10ModelEmbedding e (normalizedXi d)) (D.a10NoncentralInvolution e))
    (g : G) (hn : g ∈ normalizer (section213Eight D e : Set G))
    (hm : g⁻¹ * D.a10ModelEmbedding e Coordinates.pi * g ≠ D.a10ModelEmbedding e Coordinates.pi) :
    g⁻¹ * D.a10ModelEmbedding e Coordinates.pi * g = D.a10ModelEmbedding e (Coordinates.pi * normalizedXi d) ∨
    g⁻¹ * D.a10ModelEmbedding e Coordinates.pi * g = D.a10ModelEmbedding e (corePi * normalizedXi d) := by
  let f := D.a10ModelEmbedding e
  have hnot : ¬ IsConj (f Coordinates.pi) (f Coordinates.mu) := by
    simpa only [f, Coordinates.pi, Coordinates.mu, LocalData.a10NoncentralInvolution, D.a10ModelEmbedding_central e] using hfusion
  have hpi : f Coordinates.pi ∈ section213Eight D e := by
    rw [mem_section213Eight_iff D e 0]
    exact ⟨(1, 0, 0), by simp [section213Word, f]⟩
  have hmem : g⁻¹ * f Coordinates.pi * g ∈ section213Eight D e := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp ((normalizer _).inv_mem hn) (f Coordinates.pi)).mp hpi
  obtain ⟨i, hi⟩ := (mem_section213Eight_iff D e d _).mp hmem
  have hc : IsConj (f Coordinates.pi) (f (section213Word d i)) := by
    rw [hi]
    exact conj_isConj g (f Coordinates.pi)
  have hcases : ∀ d i, section213Word d i = 1 ∨ section213Word d i = Coordinates.pi ∨
      section213Word d i = Coordinates.mu ∨ section213Word d i = corePi ∨
      section213Word d i = normalizedXi d ∨ section213Word d i = Coordinates.mu * normalizedXi d ∨
      section213Word d i = Coordinates.pi * normalizedXi d ∨
      section213Word d i = corePi * normalizedXi d := by decide +kernel
  have hp : IsConj (f corePi) (f Coordinates.mu) := by
    apply f.map_isConj
    apply isConj_iff.mpr
    exact ⟨taup, by decide +kernel⟩
  have hx : IsConj (f (Coordinates.mu * normalizedXi d)) (f Coordinates.mu) := by
    apply IsConj.trans (b := f (normalizedXi d)) _ hxi
    apply f.map_isConj
    apply isConj_iff.mpr
    refine ⟨tau, ?_⟩
    have hl : ∀ d, tau * (Coordinates.mu * normalizedXi d) * tau⁻¹ = normalizedXi d := by
      decide +kernel
    exact hl d
  rcases hcases d i with h | h | h | h | h | h | h | h
  · rw [h, map_one] at hc
    have he : f Coordinates.pi = f 1 := (isConj_one_left.mp hc).trans f.map_one.symm
    have : Coordinates.pi = (1 : H) := (D.a10ModelEmbedding_injective e) he
    exact False.elim ((by decide +kernel : Coordinates.pi ≠ (1 : H)) this)
  · exact False.elim (hm (hi.symm.trans (congrArg f h)))
  · exact False.elim (hnot (by simpa only [h] using hc))
  · rw [h] at hc
    exact False.elim (hnot (hc.trans hp))
  · rw [h] at hc
    exact False.elim (hnot (hc.trans hxi))
  · rw [h] at hc
    exact False.elim (hnot (hc.trans hx))
  · exact Or.inl (hi.symm.trans (congrArg f h))
  · exact Or.inr (hi.symm.trans (congrArg f h))

private theorem cubic_conj_ne_inverse (g x : G) (hc : g ^ 3 = 1)
    (hm : g⁻¹ * x * g ≠ x) : g⁻¹ * x * g ≠ g * x * g⁻¹ := by
  intro h
  have htwo : g⁻¹ * (g⁻¹ * x * g) * g = x := by rw [h]; group
  have hthree : g⁻¹ * (g⁻¹ * (g⁻¹ * x * g) * g) * g = x := by
    calc
      _ = (g ^ 3)⁻¹ * x * g ^ 3 := by simp only [pow_succ, pow_zero]; group
      _ = x := by rw [hc]; group
  rw [htwo] at hthree
  exact hm hthree

private theorem cubic_conj_twice (g x : G) (hc : g ^ 3 = 1) :
    g⁻¹ * (g⁻¹ * x * g) * g = g * x * g⁻¹ := by
  calc
    _ = (g ^ 3)⁻¹ * (g * x * g⁻¹) * g ^ 3 := by
      simp only [pow_succ, pow_zero]
      group
    _ = g * x * g⁻¹ := by rw [hc]; group

private theorem xi_action_of_pi_actions {d : Bit} (g : G) (hc : g ^ 3 = 1)
    (hp : g⁻¹ * D.a10ModelEmbedding e Coordinates.pi * g =
      D.a10ModelEmbedding e (Coordinates.pi * normalizedXi d))
    (hp' : g * D.a10ModelEmbedding e Coordinates.pi * g⁻¹ =
      D.a10ModelEmbedding e (corePi * normalizedXi d)) :
    g⁻¹ * D.a10ModelEmbedding e (normalizedXi d) * g =
      D.a10ModelEmbedding e Coordinates.mu := by
  let f := D.a10ModelEmbedding e
  have htwice := cubic_conj_twice g (f Coordinates.pi) hc
  rw [hp, hp'] at htwice
  have hm : (g⁻¹ * f Coordinates.pi * g) * (g⁻¹ * f (normalizedXi d) * g) =
      f (corePi * normalizedXi d) := by
    calc
      _ = g⁻¹ * f (Coordinates.pi * normalizedXi d) * g := by rw [map_mul]; group
      _ = _ := htwice
  rw [hp] at hm
  have hlocal : ∀ d, (Coordinates.pi * normalizedXi d) * Coordinates.mu =
      corePi * normalizedXi d := by decide +kernel
  apply mul_left_cancel (a := f (Coordinates.pi * normalizedXi d))
  rw [hm, ← map_mul, hlocal d]

/-- An order-three element in the eight-group normalizer that moves pi
has one of the two orientations of Held's required action. -/
public theorem alphaRelations_of_cubic_normalizer [Finite G] {d : Bit}
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hxi : IsConj (D.a10ModelEmbedding e (normalizedXi d)) (D.a10NoncentralInvolution e))
    (g : G) (hc : g ^ 3 = 1)
    (hn : g ∈ normalizer (section213Eight D e : Set G))
    (hcentral : Commute g (D.a10ModelEmbedding e corePi))
    (hm : g⁻¹ * D.a10ModelEmbedding e Coordinates.pi * g ≠
      D.a10ModelEmbedding e Coordinates.pi) : Nonempty (AlphaRelations D e d) := by
  have hinv : g * D.a10ModelEmbedding e Coordinates.pi * g⁻¹ ≠
      D.a10ModelEmbedding e Coordinates.pi := by
    intro h
    apply hm
    calc
      _ = g⁻¹ * (g * D.a10ModelEmbedding e Coordinates.pi * g⁻¹) * g := by rw [h]
      _ = _ := by group
  have hs := pi_conjugate_choices d hfusion hxi g hn hm
  have hs' := pi_conjugate_choices d hfusion hxi g⁻¹ ((normalizer _).inv_mem hn)
    (by simpa only [inv_inv] using hinv)
  simp only [inv_inv] at hs'
  have hne := cubic_conj_ne_inverse g (D.a10ModelEmbedding e Coordinates.pi) hc hm
  have hci : (g⁻¹) ^ 3 = 1 := by rw [inv_pow, hc, inv_one]
  rcases hs with hp | hp
  · have hp' : g * D.a10ModelEmbedding e Coordinates.pi * g⁻¹ =
        D.a10ModelEmbedding e (corePi * normalizedXi d) := by
      rcases hs' with h | h
      · exact False.elim (hne (hp.trans h.symm))
      · exact h
    exact ⟨⟨g, hc, hcentral, xi_action_of_pi_actions g hc hp hp', hp⟩⟩
  · have hp' : g * D.a10ModelEmbedding e Coordinates.pi * g⁻¹ =
        D.a10ModelEmbedding e (Coordinates.pi * normalizedXi d) := by
      rcases hs' with h | h
      · exact h
      · exact False.elim (hne (hp.trans h.symm))
    refine ⟨⟨g⁻¹, hci, hcentral.inv_left, ?_, ?_⟩⟩
    · apply xi_action_of_pi_actions g⁻¹ hci
      · simpa only [inv_inv] using hp'
      · simpa only [inv_inv] using hp
    · simpa only [inv_inv] using hp'

/-- Cauchy's theorem supplies a genuine ambient actor from the source overgroup.
Its order-three elements cannot centralize pi because the intersection with H
has order 64. The eight-group action then fixes the orientation of alpha. -/
public theorem Section213Overgroup.alphaRelations [Finite G] (L : Section213Overgroup D e)
    {d : Bit} (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hxi : IsConj (D.a10ModelEmbedding e (normalizedXi d)) (D.a10NoncentralInvolution e)) :
    Nonempty (AlphaRelations D e d) := by
  have hthree : 3 ∣ Nat.card L.subgroup := by rw [L.card]; norm_num
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := L.subgroup) 3 hthree
  have hgo : orderOf (g : G) = 3 := (Subgroup.orderOf_coe g).trans hg
  have hcube : (g : G) ^ 3 = 1 := by rw [← hgo]; exact pow_orderOf_eq_one _
  have hm : (g : G)⁻¹ * D.a10ModelEmbedding e Coordinates.pi * g ≠
      D.a10ModelEmbedding e Coordinates.pi := by
    intro h
    have hpi : D.a10ModelEmbedding e Coordinates.pi = D.z := D.a10ModelEmbedding_central e
    have hgH : (g : G) ∈ D.centralizer := by
      apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg (fun x => (g : G) * x) h
      simpa only [hpi, ← mul_assoc, mul_inv_cancel, one_mul] using hh.symm
    let y : ↥(L.subgroup ⊓ D.centralizer) := ⟨g, g.property, hgH⟩
    have hyo : orderOf y = 3 := (Subgroup.orderOf_mk _ _).trans hgo
    have hdiv := orderOf_dvd_natCard y
    rw [hyo, L.intersection_card] at hdiv
    norm_num at hdiv
  apply alphaRelations_of_cubic_normalizer hfusion hxi (g : G) hcube
    (L.normalizes_eight g.property) _ hm
  exact mem_centralizer_singleton_iff.mp (L.centralizes_corePi g.property)

/-- Conditional assembly of the actor construction from the two earlier
geometric inputs. The source theorem must still discharge both inputs. -/
public theorem exists_alphaRelations_of_xi_fusion_and_overgroups [Finite G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hxi : ∃ d : Bit, IsConj (D.a10ModelEmbedding e (normalizedXi d))
      (D.a10NoncentralInvolution e))
    (hL : ∀ d : Bit, IsConj (D.a10ModelEmbedding e (normalizedXi d))
      (D.a10NoncentralInvolution e) → Nonempty (Section213Overgroup D e)) :
    ∃ d : Bit, Nonempty (AlphaRelations D e d) := by
  obtain ⟨d, hd⟩ := hxi
  obtain ⟨L⟩ := hL d hd
  exact ⟨d, L.alphaRelations hfusion hd⟩

end FaithfulExclusion
end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
