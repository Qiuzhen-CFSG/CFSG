module
public import GorensteinWalter.NormalPSL2ToPGammaL2Apply
public import GorensteinWalter.AutAlternatingFour
public import GorensteinWalter.LinearThreeEquiv
public import GorensteinWalter.LinearRingEquiv

/-!
# The actual PGL2 automorphism model in field order three

For a field K of order three, conjugation identifies PGL2(K) with Aut(PSL2(K)).
The equivalence sends the canonical image of each PSL2 element to its inner
automorphism; thus it retains the specified core action.

The canonical PSL2 range has index two, hence is normal, and is
self-centralizing. Its conjugation action is therefore injective. The proved
PSL2(3) = A4 and Aut(A4) = S4 identifications show that the target has order
24, equal to the actual PGL2 order, making this action bijective.

This supplies the small-field projective extension step in
Alperin--Brauer--Gorenstein, Chapter II, Section 3, Proposition 3 (article
pages 24-26). It uses neither perfectness of PSL2(3) nor an arbitrary ambient
group recognition in place of the canonical action.
-/

namespace GorensteinWalter

universe u

public theorem exists_pgl2_equiv_aut_psl2_of_card_three
    (K : Type u) [Field K] [Finite K] (hcard : Nat.card K = 3) :
    ∃ e : PGL2 K ≃* MulAut (PSL2 K), ∀ x : PSL2 K,
      e (Matrix.ProjectiveSpecialLinearGroup.toPGL x) = MulAut.conj x := by
  classical
  have hK : IsOddPrimePower (Nat.card K) :=
    ⟨3, 1, Nat.prime_three, by decide, le_rfl, by simpa using hcard⟩
  let N : Subgroup (PGL2 K) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range
  let : N.Normal := N.normal_of_index_eq_two (pgl2_psl2Range_index_eq_two K hK)
  let eN := psl2EquivToPGLRange K
  let f := normalPSL2ConjAction N K eN.symm
  have hf : Function.Injective f := (MulAut.congr eN.symm).injective.comp
    (conjNormal_injective_of_centralizer_eq_bot N
      (pgl2_psl2Range_centralizer_eq_bot K hK))
  let : Fintype K := Fintype.ofFinite K
  let eK : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let eA := (psl2RingEquiv eK).symm.trans psl2_three_equiv_alternatingGroup
  let c : Equiv.Perm (Fin 4) →* MulAut (alternatingGroup (Fin 4)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin 4))
  let eAut := MulEquiv.ofBijective c
    GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj
  have hAut : Nat.card (MulAut (PSL2 K)) = 24 := by
    rw [Nat.card_congr (MulAut.congr eA).toEquiv,
      ← Nat.card_congr eAut.toEquiv, Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  have hfbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr
      ⟨hf, by rw [pgl2_card_formula K, hcard, hAut]; norm_num⟩
  refine ⟨MulEquiv.ofBijective f hfbij, ?_⟩
  intro x
  change MulAut.congr eN.symm
    (MulAut.conjNormal (H := N) (Matrix.ProjectiveSpecialLinearGroup.toPGL x)) = _
  rw [← psl2EquivToPGLRange_val K x, MulAut.conjNormal_val]
  ext y
  simp [MulAut.congr, MulAut.conj_apply, eN]

end GorensteinWalter
