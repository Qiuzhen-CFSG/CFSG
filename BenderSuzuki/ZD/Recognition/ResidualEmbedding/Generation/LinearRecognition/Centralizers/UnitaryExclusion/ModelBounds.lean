module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.Inputs
public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms.Special
public import Theory.SpecificGroups.SU3.FourAutomorphismBound

/-!
# Automorphism bounds for the actual unitary centralizer covers

The two alternatives retain their given Hermitian form and both field orders.
For the special cover, faithful descent through its scalar center gives the
rank bound. At exponent two the natural special-to-projective map is an
isomorphism, so the exceptional abelian-subgroup bound transfers as well.
All other transports use the actual equivalence stored in the cover witness.

These are the two model estimates used in the last paragraph of GLS4,
Chapter 2, Section 13, following Chapter 4, Lemmas 3.4–3.5. They discharge
`AutomorphismBounds` without additional model assumptions.
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion
open Subgroup Theory.GroupTheory _root_.BenderSuzuki.MatrixGroups

private theorem bounds_of_equiv {H K : Type*} [Group H] [Group K]
    [Finite H] [Finite K] {n : ℕ} (e : H ≃* K) (h : AutomorphismBounds K n) :
    AutomorphismBounds H n := by
  constructor
  · rw [primeRank_equiv 2 (MulAut.congr e)]
    exact h.rank
  · intro hn B hB hcomm hr
    let f := (MulAut.congr e).toMonoidHom
    let := hcomm
    have he := Subgroup.equivMapOfInjective B f (MulAut.congr e).injective
    have hr' : 3 ≤ primeRank 2 (B.map f) := by
      rw [← primeRank_equiv 2 he]
      exact hr
    have hc := h.exceptional_order hn (B.map f) (hB.map f)
      (Subgroup.map_isMulCommutative B f) hr'
    rwa [Subgroup.card_map_of_injective (MulAut.congr e).injective] at hc

/-- Both source automorphism estimates for either literal unitary cover.
No order, simplicity, perfectness, or involution-generation premise remains. -/
public theorem automorphismBounds_of_unitaryCentralizerCover
    {H : Type*} [Group H] [Finite H] {n : ℕ} (hn : 2 ≤ n)
    (hcover : IsUnitaryCentralizerCoverAt n H) : AutomorphismBounds H n := by
  obtain ⟨E, _, _, J, hJ, hcard, hfixed, hmodel⟩ := hcover
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hconj := External.huppert_II_10_4_conj_eq_frobenius J (2 ^ n) hcard hfixed
  have hp : AutomorphismBounds (ProjectiveSpecialUnitaryMatrixGroup J) n := by
    constructor
    · exact HermitianForm.EvenTwoRank.automorphism_two_rank_le J hn hcard hconj
    · intro hn2
      subst n
      exact HermitianForm.FourAutomorphismBound.abelian_twoGroup_card_le_sixteen
        J hJ hcard hfixed
  rcases hmodel with he | he
  · obtain ⟨e⟩ := he
    exact bounds_of_equiv e hp
  · obtain ⟨e⟩ := he
    apply bounds_of_equiv e
    constructor
    · exact HermitianForm.EvenTwoRank.special_automorphism_two_rank_le J hn hcard hfixed
    · intro hn2
      subst n
      let e := HermitianForm.EvenProjectiveComparison.specialProjectiveEquiv
        J (by decide : Even 2) hconj
      exact (bounds_of_equiv e hp).exceptional_order rfl

end BenderSuzuki.ZD.UnitaryExclusion
