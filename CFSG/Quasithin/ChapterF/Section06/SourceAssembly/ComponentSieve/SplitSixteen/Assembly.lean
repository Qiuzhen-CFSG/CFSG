module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.SplitSixteen.EvenAssembly
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.SplitSixteen.OddRankThree
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.SplitSixteen.OddRankTwo
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.SplitSixteen.Sporadic

/-!
# The full component catalogue under C2 times D8

Apply the order, power, and Sylow-center obstructions to every constructor
of the actual Theorem C catalogue. The resulting central quotient is odd
PSL2 of degree at most two, A6, A7, or PSL2(8). The last endpoint is retained
here for its separate actual outer-automorphism extension argument.

Source: Aschbacher--Smith F.6.18(8)--(9), printed p.310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.SplitSixteen
variable {G : Type*} [Group G] [Finite G]

private theorem alternating_degree_of_sylow_le_sixteen
    (P : Sylow 2 G) (hP : Nat.card P ≤ 16) (hns : ¬ Group.IsSolvable G)
    {n : ℕ} (hn : n ≤ 8) (e : G ≃* alternatingGroup (Fin n)) :
    n = 5 ∨ n = 6 ∨ n = 7 := by
  have h5 : 5 ≤ n := by
    by_contra! hh
    have hs : Group.IsSolvable (alternatingGroup (Fin n)) := by
      by_cases h4 : n = 4
      · subst n; exact alternatingGroup_fin_four_isSolvable
      · let := alternatingGroup.isMulCommutative_of_card_le_three
          (α := Fin n) (by simpa using (show n ≤ 3 by omega))
        exact Group.isSolvable_of_comm (isMulCommutative_iff.mp inferInstance)
    let := hs
    exact hns (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
  have hn8 : n ≠ 8 := by
    intro hh
    subst n
    have hd : 32 ∣ Nat.card G := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    have hb := Nat.le_of_dvd (Nat.card_pos (α := P))
      (P.pow_dvd_card_of_pow_dvd_card (n := 5) hd)
    omega
  omega

/-- Every source model constructor is discharged on the original central
quotient, with the binary-eight endpoint reserved for its outer action. -/
theorem theoremC_component_models_of_split_sixteen
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) (hF : generalizedFitting G = K) (hK : IsComponent G K)
    (hZ : Odd (Nat.card (center K)))
    (hm : ChapterA.Section02.IsTheoremCModel (K ⧸ center K)) :
    (∃ p f : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ f ∧ f ≤ 2 ∧
      ClassicalGroup.IsPSL (K ⧸ center K) 2 (p ^ f)) ∨
    Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin 6)) ∨
    Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin 7)) ∨
    ClassicalGroup.IsPSL (K ⧸ center K) 2 8 := by
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center K))
  let P : Sylow 2 (K ⧸ center K) := default
  have hP : Nat.card P ≤ 16 := by
    have hp := central_quotient_sylow_card_le T K P
    rwa [Nat.card_congr eT.toEquiv, split_sixteen_card] at hp
  have hprime (p : ℕ) (hp : p.Prime) (ho : Odd p)
      (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 p) :
      ∃ p f : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ f ∧ f ≤ 2 ∧
        ClassicalGroup.IsPSL (K ⧸ center K) 2 (p ^ f) :=
    ⟨p, 1, hp, ho, by decide, by decide, by simpa using hm⟩
  cases hm with
  | alternating n hn iso =>
    obtain ⟨e⟩ := iso
    rcases alternating_degree_of_sylow_le_sixteen P hP
      (Group.IsPerfect.not_isSolvable _) hn e with rfl | rfl | rfl
    · obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
      exact .inl (hprime 5 (by decide) (by decide)
        ⟨ZMod 5, inferInstance, inferInstance, Nat.card_zmod _, ⟨e.trans a.symm⟩⟩)
    · exact .inr (.inl ⟨e⟩)
    · exact .inr (.inr (.inl ⟨e⟩))
  | odd model =>
    cases model with
    | linear_two p f hp ho hf iso =>
      have hfpos : 1 ≤ f := by
        obtain ⟨F, _, _, hc, _⟩ := iso
        have hcard : 1 < Nat.card F := Finite.one_lt_card
        by_contra! hh
        have hz : f = 0 := by omega
        simp [hz] at hc
        omega
      exact .inl ⟨p, f, hp, ho, hfpos, hf, iso⟩
    | linear_three p hp ho iso =>
      let : Fact p.Prime := ⟨hp⟩
      exact (not_pslThree_central_quotient_of_split_sixteen T eT K ho iso).elim
    | unitary_three p hp ho iso =>
      let : Fact p.Prime := ⟨hp⟩
      exact (not_psuThree_central_quotient_of_split_sixteen T eT K ho iso).elim
  | bender model =>
    rcases bender_central_quotient_of_split_sixteen T eT K model with hm | hm
    · exact .inl (hprime 5 (by decide) (by decide) hm)
    · exact .inr (.inr (.inr hm))
  | rank_two f model =>
    rcases rankTwo_models_of_sylow_le_sixteen P hP model with hm | hm
    · exact .inl (hprime 7 (by decide) (by decide) hm)
    · exact .inr (.inl hm)
  | linear_binary n hn model =>
    exact (not_binary_four_or_five_of_sylow_le_sixteen P hP hn model).elim
  | sporadic model => exact (not_sporadic_component T eT K hF hK hZ model).elim

end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.SplitSixteen
