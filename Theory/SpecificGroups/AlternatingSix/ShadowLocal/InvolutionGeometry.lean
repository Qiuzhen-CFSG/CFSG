module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.NaturalFixed
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.ExceptionalFixed
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers

/-!
# Involution geometry in the actual automorphism group of A₆

The inner-involution centralizers and their Sylow containment criterion are
proved in `InvolutionGeometry.Inner`. The genuine S₄ and D₁₀ fixed-subgroup
identifications exclude the remaining containment cases: their orders cannot
divide 32. Thus an involution's fixed subgroup has inner image in P exactly
when the involution lies in the inner image of the center of P ∩ Inn(A₆).

The transposition fixed-subgroup model also discharges the remaining premises
in the four-group normalizer calculations. We obtain the S₄ normalizers, their
order-48 automorphism normalizers, and the scalar transitivity and coboundary
facts for the crossing-square argument. The imported compatible product and
four-group selection theorems retain the actual inner and permutation actions;
selection concerns the four-group appropriate to the given transposition.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed pp.567–570, especially Lemma 2.5.26.
-/

public section

open Subgroup GLS3.Chapter5
namespace AlternatingSix.ShadowLocal

/-- Conditional assembly from the two genuine outer fixed-subgroup models.
The order obstruction excludes both outer cases and the inner calculation
applies. The unconditional theorem below supplies both models. -/
theorem involution_fixed_le_sylow_iff_of_models (P : Sylow 2 AutA6)
    (β : AutA6) (hβ : orderOf β = 2)
    (hS4 : β ∈ natural → β ∉ inner →
      Nonempty (automorphismFixedSubgroup β ≃* Equiv.Perm (Fin 4)))
    (hD10 : β ∉ natural →
      Nonempty (automorphismFixedSubgroup β ≃* DihedralGroup 5)) :
    (automorphismFixedSubgroup β).map (MulAut.conj : A6 →* AutA6) ≤
      (P : Subgroup AutA6) ↔ β ∈ innerSylowCenter P := by
  classical
  by_cases hi : β ∈ inner
  · exact inner_involution_fixed_le_sylow_iff P β hβ hi
  · have hncenter : β ∉ innerSylowCenter P := fun h => hi (innerSylowCenter_le_inner P h)
    refine iff_of_false ?_ hncenter
    intro hle
    have hd := fixed_inner_card_dvd_sylow P β hle
    by_cases hn : β ∈ natural
    · obtain ⟨e⟩ := hS4 hn hi
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm] at hd
      norm_num [Nat.factorial] at hd
    · obtain ⟨e⟩ := hD10 hn
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at hd
      norm_num at hd

/-- An involution fixes a subgroup with inner image contained in P exactly
when it lies in the inner image of the center of the inner Sylow intersection.
In particular, the forward implication does not require a separate β ∈ P
hypothesis. This is the local noncontainment criterion used in 2.5.26. -/
theorem involution_fixed_le_sylow_iff (P : Sylow 2 AutA6)
    (β : AutA6) (hβ : orderOf β = 2) :
    (automorphismFixedSubgroup β).map (MulAut.conj : A6 →* AutA6) ≤
      (P : Subgroup AutA6) ↔ β ∈ innerSylowCenter P :=
  involution_fixed_le_sylow_iff_of_models P β hβ
    (natural_outer_involution_fixed_equiv_symmetricFour β hβ)
    (outside_natural_involution_fixed_equiv_dihedral β hβ)

/-- The form of the containment criterion used to find fixed elements
outside the Sylow subgroup in the proof of 2.5.26. -/
theorem involution_fixed_not_le_sylow (P : Sylow 2 AutA6)
    (β : AutA6) (hβ : orderOf β = 2) (hc : β ∉ innerSylowCenter P) :
    ¬ (automorphismFixedSubgroup β).map (MulAut.conj : A6 →* AutA6) ≤
      (P : Subgroup AutA6) :=
  fun h => hc ((involution_fixed_le_sylow_iff P β hβ).mp h)

/-- The uniform transposition model needed by the four-group calculations. -/
theorem swap_fixed_equiv_symmetricFour (σ : Equiv.Perm (Fin 6)) (hσ : σ.IsSwap) :
    Nonempty (automorphismFixedSubgroup (permutationAction σ) ≃* Equiv.Perm (Fin 4)) :=
  ⟨swapFixedEquiv σ hσ⟩

/-- Every actual A₆ four-group has normalizer S₄, with no fixed-group model
premise remaining. -/
theorem four_normalizer_equiv_symmetric (F : Subgroup A6) [IsKleinFour F] :
    Nonempty (normalizer (F : Set A6) ≃* Equiv.Perm (Fin 4)) :=
  FourNormalizers.normalizer_equiv_symmetric swap_fixed_equiv_symmetricFour F

theorem four_normalizer_card (F : Subgroup A6) [IsKleinFour F] :
    Nat.card (normalizer (F : Set A6)) = 24 := by
  obtain ⟨e⟩ := four_normalizer_equiv_symmetric F
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num [Nat.factorial]

/-- The normalizer of the specified inner image of a four-group has order 48. -/
theorem four_aut_normalizer_card (F : Subgroup A6) [IsKleinFour F] :
    Nat.card (normalizer (F.map (MulAut.conj : A6 →* AutA6) : Set AutA6)) = 48 :=
  FourNormalizers.aut_normalizer_card swap_fixed_equiv_symmetricFour F

/-- The abstract S₄ × C₂ model, obtained from the compatible product
`FourNormalizers.exists_compatible_product` with the actual inner embedding. -/
theorem four_aut_normalizer_equiv_symmetric_prod (F : Subgroup A6) [IsKleinFour F] :
    Nonempty (normalizer (F.map (MulAut.conj : A6 →* AutA6) : Set AutA6) ≃*
      (Equiv.Perm (Fin 4) × Multiplicative (ZMod 2))) :=
  FourNormalizers.aut_normalizer_equiv_symmetric_prod swap_fixed_equiv_symmetricFour F

/-- Scalar normalizer transitivity, with the explicit four-group hypothesis
used by source consumers. The conjugating element belongs to the actual A₆. -/
theorem four_transitive (F : Subgroup A6) (hF : IsKleinFour F)
    (a : A6) (ha : a ∈ F) (ha1 : a ≠ 1)
    (b : A6) (hb : b ∈ F) (hb1 : b ≠ 1) :
    ∃ k ∈ normalizer (F : Set A6), k * a * k⁻¹ = b := by
  let := hF
  exact FourNormalizers.four_transitive F a ha ha1 b hb hb1

/-- Every outside involution in a four-group normalizer is an actual
coboundary for any involution fixing that normalizer pointwise. -/
theorem four_normalizer_outside_coboundary (F : Subgroup A6) [IsKleinFour F]
    (β : AutA6) (hβ2 : β ^ 2 = 1) (hβ1 : β ≠ 1)
    (hfix : ∀ k ∈ normalizer (F : Set A6), β k = k)
    (f : A6) (hfn : f ∈ normalizer (F : Set A6)) (hf2 : f ^ 2 = 1) (hf : f ∉ F) :
    ∃ k : A6, k * (β k)⁻¹ = f :=
  FourNormalizers.normalizer_outside_coboundary swap_fixed_equiv_symmetricFour
    F β hβ2 hβ1 hfix f hfn hf2 hf

/-- The scalar coboundary identity for a four-group inside a dihedral
subgroup of order eight. Together with `four_transitive`, this supplies the
two actual A₆ model facts used by the crossing-square fusion argument. -/
theorem outside_coboundary (D F : Subgroup A6)
    (hD : Nonempty (D ≃* DihedralGroup 4)) (hF : IsKleinFour F) (hFD : F ≤ D)
    (β : AutA6) (hβ2 : β ^ 2 = 1) (hβ1 : β ≠ 1)
    (hfix : ∀ k ∈ normalizer (F : Set A6), β k = k)
    (f : A6) (hfD : f ∈ D) (hf2 : f ^ 2 = 1) (hf : f ∉ F) :
    ∃ k : A6, k * (β k)⁻¹ = f := by
  let := hF
  exact FourNormalizers.outside_coboundary swap_fixed_equiv_symmetricFour
    D F hD hFD β hβ2 hβ1 hfix f hfD hf2 hf

end AlternatingSix.ShadowLocal
