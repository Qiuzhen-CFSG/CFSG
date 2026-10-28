module

public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.SymmetricModels
public import Theory.GroupTheory.SymmetricFourModelCoreData

/-!
# Residual images forced into the line parabolic

Suppose a finite group maps onto S₃ with two-group kernel, and a second
map to SL₃(2) sends a specified subgroup onto the standard Borel. If the
second image of O²(X) fails to normalize the marked point A₄, then that
residual image is exactly the marked line A₄. The specified subgroup
cannot lie in the kernel of the first map.

The first quotient gives |X| = 6 · 2ⁿ, excluding a full SL₃(2) image.
Bruhat's Borel overgroup theorem and the orders eight and 24 force the
second image to be the line parabolic. Surjective residual transport
identifies its embedded O². Finally, the actual S₄ equivalence gives a
two-core of order four, which cannot contain the order-eight Borel image
of a normal two-subgroup.

Source application: Aschbacher–Smith, combined manuscript, 1 March 2004,
proof of Lemma 14.7.70, printed p.1074 (PDF p.1091). The point and line
marks here are the embedded residuals, not the full parabolics.
-/

public section

open Subgroup
namespace Matrix.PSL3Two.ProjectionResidualImage
open MarkedAutomorphisms

private theorem range_ne_top {X : Type*} [Group X] [Finite X]
    (f : X →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (π : X →* SL) : π.range ≠ ⊤ := by
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  have hq : Nat.card (X ⧸ f.ker) = 6 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hc : Nat.card X = 6 * 2 ^ n := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker, hq, hn]
  intro ht
  have hd := card_range_dvd π
  rw [ht, Nat.card_congr Subgroup.topEquiv.toEquiv, card_SL, hc] at hd
  have h7 : 7 ∣ 6 * 2 ^ n := dvd_trans (by decide : 7 ∣ 168) hd
  rcases (show Nat.Prime 7 by decide).dvd_mul.mp h7 with h | h
  · norm_num at h
  · have := (show Nat.Prime 7 by decide).dvd_of_dvd_pow h
    norm_num at this

private theorem range_eq_line {X : Type*} [Group X]
    (π : X →* SL) (hproper : π.range ≠ ⊤) (hB : borelSL ≤ π.range)
    (hescape : ¬ (pResidual 2 X).map π ≤ normalizer (pointA : Set SL)) :
    π.range = lineParabolicSL := by
  have hp : pointParabolicSL ≤ normalizer (pointA : Set SL) :=
    le_normalizer_iff.mpr pointA_conj
  rcases overgroup_borelSL π.range hB hproper with hpoint | hline
  · exact (hescape ((map_le_range π (pResidual 2 X)).trans (hpoint.trans hp))).elim
  · have hd₁ := card_dvd_of_le hB
    have hd₂ := card_dvd_of_le hline
    rw [card_borelSL] at hd₁
    rw [card_lineParabolicSL] at hd₂
    have hb : Nat.card π.range ≤ 24 := Nat.le_of_dvd (by decide) hd₂
    have hc : Nat.card π.range = 8 ∨ Nat.card π.range = 24 := by
      have hn : Nat.card π.range ≠ 0 := Nat.card_pos.ne'
      have h16 : Nat.card π.range ≠ 16 := by
        intro h
        rw [h] at hd₂
        norm_num at hd₂
      omega
    rcases hc with hc | hc
    · have he : borelSL = π.range :=
        eq_of_le_of_card_ge hB (by rw [card_borelSL, hc])
      exact (hescape ((map_le_range π (pResidual 2 X)).trans (he ▸ (inf_le_left.trans hp)))).elim
    · exact eq_of_le_of_card_ge hline (by rw [card_lineParabolicSL, hc])

private theorem borel_not_le_normal_two (N : Subgroup lineParabolicSL) [N.Normal]
    (hN : IsPGroup 2 N) : ¬ borelSL ≤ N.map lineParabolicSL.subtype := by
  have hcore : N ≤ pCore 2 lineParabolicSL := le_sSup ⟨inferInstance, hN⟩
  have hc : Nat.card (pCore 2 lineParabolicSL) = 4 := by
    have h := (symmetric_four_model_twoCore_data
      (Or.inl ⟨lineEquivSymmetric⟩)).2
    rcases h with h | h
    · exact h.1
    · have := card_lineParabolicSL
      omega
  intro hB
  have hd := card_dvd_of_le (hB.trans (map_mono hcore))
  rw [card_borelSL,
    ← Nat.card_congr ((pCore 2 lineParabolicSL).equivMapOfInjective
      lineParabolicSL.subtype lineParabolicSL.subtype_injective).toEquiv,
    hc] at hd
  norm_num at hd

/-- The literal image of the two-residual is the marked line A₄, and the
subgroup covering the Borel acts nontrivially through the S₃ quotient. -/
theorem parabolic_residual_image {X : Type*} [Group X] [Finite X]
    (f : X →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (π : X →* SL) (A : Subgroup X)
    (hA : A.map π = borelSL)
    (hescape : ¬ (pResidual 2 X).map π ≤ normalizer (pointA : Set SL)) :
    (pResidual 2 X).map π = lineA ∧ ¬ A ≤ f.ker := by
  have hB : borelSL ≤ π.range := hA ▸ map_le_range π A
  have hline := range_eq_line π (range_ne_top f hf hk π) hB hescape
  let q : X →* lineParabolicSL :=
    (MulEquiv.subgroupCongr hline).toMonoidHom.comp π.rangeRestrict
  have hqsurj : Function.Surjective q :=
    (MulEquiv.subgroupCongr hline).surjective.comp π.rangeRestrict_surjective
  have hq : lineParabolicSL.subtype.comp q = π := rfl
  constructor
  · rw [← hq, ← Subgroup.map_map, map_pResidual_of_surjective 2 q hqsurj]
    exact line_residual
  · intro hker
    let N := f.ker.map q
    let : N.Normal := Normal.map inferInstance q hqsurj
    apply borel_not_le_normal_two N (hk.map q)
    change borelSL ≤ (f.ker.map q).map lineParabolicSL.subtype
    rw [Subgroup.map_map, hq, ← hA]
    exact map_mono hker

end Matrix.PSL3Two.ProjectionResidualImage
