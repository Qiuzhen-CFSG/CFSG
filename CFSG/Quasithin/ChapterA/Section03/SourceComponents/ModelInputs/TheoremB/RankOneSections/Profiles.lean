module

public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremB.Basic
public import Theory.SpecificGroups.FiniteModelSylowFrattini
public import Theory.SpecificGroups.OddClassicalSylowFrattini
public import Theory.SpecificGroups.OddThreeRank
public import Theory.SpecificGroups.G2.OddSylowFrattini
public import Theory.SpecificGroups.SymplecticSix.BinarySylowFrattini
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FrattiniExact
public import Theory.SpecificGroups.ClassicalUnitary.FourSylowStructure.Transport
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.Sylow

/-!
# The complete Theorem B catalogue for rank-one outer sections

Every nonabelian simple B-model has either solvable outer automorphisms or a
Sylow two-subgroup with at most eight Frattini generators. The shared C rows
and alternating groups use the completed outer calculations. Odd classical
groups, odd G₂, J₃, McL and Sp₆(2) use the actual Sylow bounds. For PSU₄ the
large-field Sylow automorphism group is solvable; its small endpoint has
three Frattini generators. The two order-sixteen flag factors of PSU₅(4)
give eight generators. No strongly quasithin hypothesis is added.

Source: Aschbacher--Smith, Theorem B (A.2.2), printed p.33, and the outer
section argument in 4.4.10--11, printed p.621.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.SpecificGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceComponents.TheoremBOuter.RankOneSections
open Section02 ClassificationModels

/-- The two proved mechanisms used in the complete B-model inspection. -/
def HasOuterProfile (S : Type*) [Group S] : Prop :=
  Group.IsSolvable (MulAut.Outer S) ∨
    ∃ P : Sylow 2 S, Nat.card (P ⧸ frattini P) ≤ 256

variable {S : Type*} [Group S] [Finite S]

private theorem linear_odd {n q : ℕ} (hn : n ≤ 4) (ho : Odd q)
    (hm : ClassicalGroup.IsPSL S n q) : HasOuterProfile S := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let P : Sylow 2 S := Classical.choice inferInstance
  refine .inr ⟨P,?_⟩
  rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup S))]
  exact (OddClassicalSylowFrattini.psl_card_le_128 hn
    (OddThreeRank.two_ne_zero_of_odd_card (k := 1) ho (by simpa using hF))
    (P.mapSurjective e.surjective)).trans (by decide)

private theorem unitary_odd {n q : ℕ} (hn : n ≤ 4) (ho : Odd q)
    (hm : ClassicalGroup.IsPSU S n q) : HasOuterProfile S := by
  obtain ⟨F,_,_,J,hF,_,⟨e⟩⟩ := hm
  let P : Sylow 2 S := Classical.choice inferInstance
  refine .inr ⟨P,?_⟩
  rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup S))]
  exact (OddClassicalSylowFrattini.psu_card_le_128 J hn
    (OddThreeRank.two_ne_zero_of_odd_card ho hF)
    (P.mapSurjective e.surjective)).trans (by decide)

private theorem symplectic_odd {q : ℕ} (ho : Odd q)
    (hm : ClassicalGroup.IsPSp S 2 q) : HasOuterProfile S := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let P : Sylow 2 S := Classical.choice inferInstance
  refine .inr ⟨P,?_⟩
  rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup S))]
  exact (OddClassicalSylowFrattini.psp_four_card_le_128
    (OddThreeRank.two_ne_zero_of_odd_card (k := 1) ho (by simpa using hF))
    (P.mapSurjective e.surjective)).trans (by decide)

private theorem g2_odd {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : IsG2At S p) : HasOuterProfile S := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let P : Sylow 2 S := Classical.choice inferInstance
  refine .inr ⟨P,?_⟩
  rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup S))]
  exact (Atlas.G2.OddSylowFrattini.frattini_card_le ho hF
    (P.mapSurjective e.surjective)).trans (by decide)

private theorem odd_profile (hm : IsTheoremBOddModel S) : HasOuterProfile S := by
  cases hm with
  | linear_two q ho hm => exact linear_odd (by decide) ho hm
  | linear_three p e _ ho _ hm => exact linear_odd (by decide) ho.pow hm
  | unitary_three p e _ ho _ hm => exact unitary_odd (by decide) ho.pow hm
  | symplectic p _ ho hm => exact symplectic_odd ho hm
  | g2 p hp ho hm => exact g2_odd hp ho hm
  | linear_four p _ hf hm =>
    have ho : Odd p := by
      obtain ⟨k,rfl⟩ := hf
      exact (even_two.pow_of_ne_zero (by positivity)).add_one
    exact linear_odd le_rfl ho hm
  | unitary_four p hp hmers hm =>
    have ho : Odd p := by
      obtain ⟨b,hb⟩ := hmers
      have hb0 : b ≠ 0 := by
        intro he
        simp only [he,pow_zero] at hb
        have := hp.two_le
        omega
      have heven : Even (p+1) := hb.symm ▸ even_two.pow_of_ne_zero hb0
      exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp heven)
    exact unitary_odd le_rfl ho hm

private theorem unitary_four_binary [IsSimpleGroup S] {n : ℕ} (hn : 1 ≤ n)
    (hm : ClassicalGroup.IsPSU S 4 (2 ^ n)) : HasOuterProfile S := by
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hm
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv S e.toEquiv
  let P : Sylow 2 S := Classical.choice inferInstance
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let j : P ≃* Q := P.equivMapOfInjective e.toMonoidHom e.injective
  by_cases hn1 : n = 1
  · refine .inr ⟨P,?_⟩
    rw [SylowFrattiniBounds.card_congr j,
      ClassicalUnitary.UnitaryFourSylow.FrattiniExact.projective_frattini_card
        F J (by omega) hcard hconj Q, hn1]
    norm_num
  · let : Group.IsSolvable (MulAut Q) :=
      ClassicalUnitary.FourSylowStructure.projective_sylow_mulAut_isSolvable
        F J (by omega : 1 < n) hcard hconj Q
    let : Group.IsSolvable (MulAut P) := Group.isSolvable_of_surjective
      (f := (MulAut.congr j.symm).toMonoidHom) (MulAut.congr j.symm).surjective
    let : Group.IsSolvable (fixingSubgroup (MulAut S) (P : Set S)) :=
      ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
    exact .inl (MulAut.outer_isSolvable_of_sylow_aut P)

private theorem unitary_five_four (hm : ClassicalGroup.IsPSU S 5 4) :
    HasOuterProfile S := by
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hm
  let : CharP F 2 := UnitaryFive.charP_two_of_card_sixteen hcard
  obtain ⟨a⟩ := UnitaryFive.projective_equiv_identity_four J hcard hconj
  let P : Sylow 2 S := Classical.choice inferInstance
  let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  obtain ⟨Q,_,hQ,hquot⟩ := UnitaryFive.Flag.sylow_invariant_frattini_flag_four
    (HermitianForm.IdentityGram.identityGram J) hcard hconj rfl (e.trans a) P
  have hc := card_eq_card_quotient_mul_card_subgroup Q
  rw [hQ,hquot] at hc
  exact .inr ⟨P,hc.le⟩

/-- Every row of the actual Theorem B list supplies one of the two mechanisms.
The nonabelian simple hypothesis is inherited from the component quotient. -/
theorem model_profile [IsSimpleGroup S] (hna : ¬ IsMulCommutative S)
    (hm : IsTheoremBModel S) : HasOuterProfile S := by
  have hC (h : IsTheoremCModel S) : HasOuterProfile S := .inl (of_theoremC hna h)
  cases hm with
  | alternating n _ e => exact .inl (alternating hna e)
  | odd h => exact odd_profile h
  | bender h => exact hC (.bender h)
  | linear_binary n hn h => exact hC (.linear_binary n hn h)
  | symplectic_binary h =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
    let P : Sylow 2 S := Classical.choice inferInstance
    exact .inr ⟨P,(SymplecticSix.BinarySylowFrattini.frattini_card_le_of_equiv
      hF e P).trans (by decide)⟩
  | rank_two n h =>
    cases h with
    | linear hn h => exact hC (.rank_two n (.linear hn h))
    | unitary_four hn h => exact unitary_four_binary hn h
    | unitary_five hn h => exact unitary_five_four (by simpa [hn] using h)
    | symplectic hn h => exact hC (.rank_two n (.symplectic hn h))
    | g2 hn h => exact hC (.rank_two n (.g2 hn h))
    | triality hn h => exact hC (.rank_two n (.triality hn h))
    | ree_f4 m hm hn h => exact hC (.rank_two n (.ree_f4 m hm hn h))
    | symplectic_derived hn h => exact hC (.rank_two n (.symplectic_derived hn h))
    | g2_derived hn h => exact hC (.rank_two n (.g2_derived hn h))
    | tits hn h => exact hC (.rank_two n (.tits hn h))
  | sporadic h =>
    rcases h with ⟨name,e⟩ | e | e
    · by_cases hj : name = .j3
      · subst name
        obtain ⟨e⟩ := e
        let P : Sylow 2 S := Classical.choice inferInstance
        exact .inr ⟨P,(FiniteModelSylowFrattini.j3_card_le_thirtytwo e P).trans (by decide)⟩
      · exact hC (.sporadic (.inl ⟨name,hj,e⟩))
    · exact hC (.sporadic (.inr e))
    · obtain ⟨e⟩ := e
      let P : Sylow 2 S := Classical.choice inferInstance
      exact .inr ⟨P,(FiniteModelSylowFrattini.mcl_card_le_128 e P).trans (by decide)⟩

end CFSG.Quasithin.ChapterA.Section03.SourceComponents.TheoremBOuter.RankOneSections
