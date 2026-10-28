module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFixed
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryAutomizer

/-!
# Actual binary doubled four-group centralizers

The full automizer marking attains two-rank two. For an elementary four-group
in the original component image, it transports the natural–dual fixed-space
calculation to the literal orbit and identifies the entire pointwise fixer.
The final theorem translates this into W ∩ C_G(A) and the original quotient
map N_G(W) → Aut_G(W), without replacing the orbit by its seed.

This supplies the inner-four-group centralizer dimension in 7.6.1.
The fixed-space span, outer-four-group exclusion, global r > 2 argument and
centralizer-core geometry remain obligations of qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith H.4.3(2) and 7.6.1, printed pp.380,702.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The complete automizer attains the table's two-rank, including its
outer coset; this strengthens the earlier upper bound on the actual orbit. -/
theorem sourceOrbit_binary_automizer_rank_eq
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) : primeRank 2 (ChapterE.Automizer D.sourceOrbit) = 2 := by
  obtain ⟨_,_,_,_,_,_,a,_⟩ := D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  rw [primeRank_equiv 2 a,
    primeRank_equiv 2 (MulAut.congr Matrix.PSL3Two.equiv)]
  exact Matrix.PSL3Even.automorphism_two_rank_eq_of_card_two (ZMod 2) (by simp)

/-- The source inner four-group fixes a three-space on the actual orbit,
and is its entire pointwise stabilizer in the ambient automizer. -/
theorem sourceOrbit_binary_inner_four_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup (Automizer D.sourceOrbit))
    (hAL : A ≤ inducedAutomizer D.sourceOrbit L)
    (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 4) :
    Nat.card (fixedSpace (automizerRepresentation D.sourceOrbit) A) = 8 ∧
      ∀ b : Automizer D.sourceOrbit,
        (∀ v ∈ fixedSpace (automizerRepresentation D.sourceOrbit) A,
          automizerRepresentation D.sourceOrbit b v = v) → b ∈ A := by
  obtain ⟨_,_,_,q,hq,E,f,hE,hfL,_,_,_,_⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  let i := D.sourceOrbit.normalizerMonoidHom.rangeRestrict.comp
    (inclusion D.sourceOrbit_component_normalizes)
  apply doubledBinary_inner_four_fixed (automizerRepresentation D.sourceOrbit) i q hq E hE f hfL A
    (hA := hA) (hcard := hcard)
  intro a ha
  obtain ⟨n,hn,he⟩ := hAL ha
  rw [← he]
  exact ⟨q ⟨n,hn⟩,(hfL ⟨n,hn⟩).symm⟩

/-- The inner four-group calculation on literal ambient centralizers.
It keeps the actual action image of A and the actual normalizer quotient map. -/
theorem sourceOrbit_binary_inner_four_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) (hAN : A ≤ normalizer (D.sourceOrbit : Set G))
    (hAL : inducedAutomizer D.sourceOrbit A ≤ inducedAutomizer D.sourceOrbit L)
    (hA : IsElementaryAbelian 2 (inducedAutomizer D.sourceOrbit A))
    (hcard : Nat.card (inducedAutomizer D.sourceOrbit A) = 4) :
    Nat.card (D.sourceOrbit ⊓ centralizer (A : Set G) : Subgroup G) = 8 ∧
      ∀ n : normalizer (D.sourceOrbit : Set G),
        (n : G) ∈ centralizer (D.sourceOrbit ⊓ centralizer (A : Set G) : Set G) ↔
          D.sourceOrbit.normalizerMonoidHom.rangeRestrict n ∈ inducedAutomizer D.sourceOrbit A := by
  obtain ⟨hc,hfix⟩ := D.sourceOrbit_binary_inner_four_fixed h hd F hF hmodel _ hAL hA hcard
  let W := D.sourceOrbit
  let B := inducedAutomizer W A
  let ρ := automizerRepresentation W
  let C := W ⊓ centralizer (A : Set G)
  let e : fixedSpace ρ B ≃ C := {
    toFun v := ⟨v.val.toMul,v.val.toMul.property,
      (mem_fixedSpace_inducedAutomizer W A hAN v.val).mp v.property⟩
    invFun x := ⟨Additive.ofMul ⟨x,x.property.1⟩,
      (mem_fixedSpace_inducedAutomizer W A hAN _).mpr x.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  refine ⟨(Nat.card_congr e).symm.trans hc, ?_⟩
  intro n
  constructor
  · intro hn
    apply hfix
    intro v hv
    apply Additive.toMul.injective
    apply Subtype.ext
    change (n : G) * (v.toMul : G) * (n : G)⁻¹ = (v.toMul : G)
    have hvC : (v.toMul : G) ∈ C :=
      ⟨v.toMul.property,(mem_fixedSpace_inducedAutomizer W A hAN v).mp hv⟩
    rw [← hn _ hvC, mul_assoc, mul_inv_cancel, mul_one]
  · intro hn x hx
    let v : Additive W := Additive.ofMul ⟨x,hx.1⟩
    have hv : v ∈ fixedSpace ρ B := (mem_fixedSpace_inducedAutomizer W A hAN v).mpr hx.2
    have he := hv ⟨_,hn⟩
    have he' : (n : G) * x * (n : G)⁻¹ = x :=
      congrArg (fun w : Additive W => (w.toMul : G)) he
    exact ((mul_inv_eq_iff_eq_mul).mp he').symm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
