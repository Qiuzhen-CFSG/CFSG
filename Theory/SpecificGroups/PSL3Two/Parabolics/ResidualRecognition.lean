module

public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Recognizing Sylow-normalized cubic residuals in SL₃(2)

Let A be two-perfect, with A/O₂(A) of order three, and normalized by a Sylow
two-subgroup S of the actual binary matrix group. Then N(A) is a parabolic of
order 24 and A is its embedded two-residual. One conjugation carries N(A), A
and S to a standard point or line parabolic, its full residual and its Borel.

The cubic quotient forces |A| = 3 · 2ⁿ. The existing simplicity theorem excludes
N(A) = SL₃(2); Bruhat's Sylow-overgroup classification and divisibility then give
|N(A)| = 24. Since A is normal in N(A), its quotient has two-power order, and
two-perfectness identifies A with O²(N(A)). Functoriality of residuals supplies
the compatible conjugation without passing A to its intrinsic cubic quotient.

This is the intrinsic model recognition used in the covered paragraph of
Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
of 1 March 2004, proof of 13.8.21(1), printed p.957. The application must supply
the actual image of L₀* and the three displayed hypotheses.
-/

public section

open Subgroup
open scoped Pointwise
namespace Matrix.PSL3Two.ResidualRecognition

private theorem card_eq_three_mul_two_pow (A : Subgroup SL)
    (hc : Nat.card (A ⧸ pCore 2 A) = 3) :
    ∃ n : ℕ, Nat.card A = 3 * 2 ^ n := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  exact ⟨n, by rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 A), hc, hn]⟩

private theorem three_dvd_card (A : Subgroup SL)
    (hc : Nat.card (A ⧸ pCore 2 A) = 3) : 3 ∣ Nat.card A := by
  simpa only [hc] using Subgroup.card_quotient_dvd_card (pCore 2 A)

private theorem normalizer_ne_top (A : Subgroup SL)
    (hc : Nat.card (A ⧸ pCore 2 A) = 3) : normalizer (A : Set SL) ≠ ⊤ := by
  let : IsSimpleGroup PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup SL := equiv.isSimpleGroup
  intro hn
  have hA : A.Normal := normalizer_eq_top_iff.mp hn
  rcases hA.eq_bot_or_eq_top with ha | ha
  · have hd := three_dvd_card A hc
    rw [ha, Subgroup.card_bot] at hd
    norm_num at hd
  · obtain ⟨n, hc⟩ := card_eq_three_mul_two_pow A hc
    rw [ha, Nat.card_congr Subgroup.topEquiv.toEquiv, card_SL] at hc
    have h7 : 7 ∣ 2 ^ n := by
      have he : 2 ^ n = 56 := by omega
      rw [he]
      decide
    have := (show Nat.Prime 7 by decide).dvd_of_dvd_pow h7
    norm_num at this

private theorem normalizer_not_two (A : Subgroup SL)
    (hc : Nat.card (A ⧸ pCore 2 A) = 3) :
    ¬ IsPGroup 2 (normalizer (A : Set SL)) := by
  intro hp
  have hd := (three_dvd_card A hc).trans (Subgroup.card_dvd_of_le A.le_normalizer)
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn] at hd
  have := (show Nat.Prime 3 by decide).dvd_of_dvd_pow hd
  norm_num at this

private theorem exists_conj_borel (S : Sylow 2 SL) :
    ∃ g : SL, (S : Subgroup SL).map (MulAut.conj g).toMonoidHom = borelSL := by
  let B : Sylow 2 SL := Sylow.ofCard borelSL (by
    rw [card_borelSL, card_SL]
    decide +kernel)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL S B
  refine ⟨g, ?_⟩
  change ((g • S : Sylow 2 SL) : Subgroup SL) = borelSL
  rw [hg]
  rfl

private theorem normalizer_marking (A : Subgroup SL) (S : Sylow 2 SL)
    (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hn : (S : Subgroup SL) ≤ normalizer (A : Set SL)) :
    ∃ (g : SL) (P₀ : Subgroup SL),
      (P₀ = pointParabolicSL ∨ P₀ = lineParabolicSL) ∧
      (normalizer (A : Set SL)).map (MulAut.conj g).toMonoidHom = P₀ ∧
      (S : Subgroup SL).map (MulAut.conj g).toMonoidHom = borelSL ∧
      borelSL ≤ P₀ := by
  obtain ⟨g, hg⟩ := exists_conj_borel S
  let e := MulAut.conj g
  let P := normalizer (A : Set SL)
  have hb : borelSL ≤ e.mapSubgroup P := by
    rw [← hg]
    exact Subgroup.map_mono hn
  have hp : e.mapSubgroup P ≠ ⊤ := by
    intro h
    exact normalizer_ne_top A hc (e.mapSubgroup.injective
      (h.trans e.mapSubgroup.map_top.symm))
  have h₂ : ¬ IsPGroup 2 (e.mapSubgroup P) := fun h =>
    normalizer_not_two A hc (h.of_equiv (e.subgroupMap P).symm)
  exact ⟨g, e.mapSubgroup P, parabolic_of_borel_le_of_not_two _ hb hp h₂, rfl, hg, hb⟩

private theorem residual_eq (A P : Subgroup SL) (hAP : A ≤ P)
    (hn : P ≤ normalizer (A : Set SL))
    (hA : IsPPerfect 2 A) (h3 : 3 ∣ Nat.card A) (hP : Nat.card P = 24) :
    (pResidual 2 P).map P.subtype = A := by
  let B := A.subgroupOf P
  let : B.Normal := normal_subgroupOf_of_le_normalizer hn
  have he : Nat.card B = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe hAP).toEquiv
  have hb : IsPPerfect 2 B := hA.of_surjective
    (subgroupOfEquivOfLe hAP).symm.toMonoidHom
    (subgroupOfEquivOfLe hAP).symm.surjective
  have hq : IsPGroup 2 (P ⧸ B) := by
    apply IsPGroup.of_card_dvd_pow (n := 3)
    change B.index ∣ 8
    obtain ⟨k, hk⟩ := h3
    have hm := B.index_mul_card
    rw [he, hP, hk] at hm
    exact ⟨k, by nlinarith⟩
  rw [pResidual_eq_of_isPPerfect B hb hq]
  exact map_subgroupOf_eq_of_le hAP

/-- A two-perfect subgroup with cubic quotient by its two-core, normalized by
an ambient Sylow two-subgroup, is the full two-residual of its normalizer.
That normalizer is a maximal parabolic of order 24. A single inner automorphism
marks the normalizer, residual and Sylow subgroup simultaneously at the standard
point or line parabolic, its embedded residual, and the standard Borel. -/
theorem recognize (A : Subgroup SL) (S : Sylow 2 SL)
    (hA : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hn : (S : Subgroup SL) ≤ normalizer (A : Set SL)) :
    IsCoatom (normalizer (A : Set SL)) ∧
    Nat.card (normalizer (A : Set SL)) = 24 ∧
    (S : Subgroup SL) ≤ normalizer (A : Set SL) ∧
    A = (pResidual 2 (normalizer (A : Set SL))).map
      (normalizer (A : Set SL)).subtype ∧
    ∃ (g : SL) (P₀ : Subgroup SL),
      (P₀ = pointParabolicSL ∨ P₀ = lineParabolicSL) ∧
      (normalizer (A : Set SL)).map (MulAut.conj g).toMonoidHom = P₀ ∧
      A.map (MulAut.conj g).toMonoidHom = (pResidual 2 P₀).map P₀.subtype ∧
      (S : Subgroup SL).map (MulAut.conj g).toMonoidHom = borelSL ∧
      borelSL ≤ P₀ := by
  obtain ⟨g, P₀, hP₀, hP, hS, hB⟩ := normalizer_marking A S hc hn
  let P := normalizer (A : Set SL)
  have hcard₀ : Nat.card P₀ = 24 := by
    rcases hP₀ with rfl | rfl
    · exact card_pointParabolicSL
    · exact card_lineParabolicSL
  have hcard : Nat.card P = 24 := by
    rw [Nat.card_congr ((MulAut.conj g).subgroupMap P).toEquiv]
    change Nat.card (P.map (MulAut.conj g).toMonoidHom) = 24
    rw [hP]
    exact hcard₀
  have hmax₀ : IsCoatom P₀ := by
    rcases hP₀ with rfl | rfl
    · exact isCoatom_pointParabolicSL
    · exact isCoatom_lineParabolicSL
  have hmax : IsCoatom P := by
    apply ((MulAut.conj g).mapSubgroup.isCoatom_iff P).mp
    change IsCoatom (P.map (MulAut.conj g).toMonoidHom)
    rw [hP]
    exact hmax₀
  have hr : (pResidual 2 P).map P.subtype = A :=
    residual_eq A P A.le_normalizer le_rfl hA (three_dvd_card A hc) hcard
  refine ⟨hmax, hcard, hn, hr.symm, g, P₀, hP₀, hP, ?_, hS, hB⟩
  rw [← hr, map_embedded_pResidual, hP]

end Matrix.PSL3Two.ResidualRecognition
