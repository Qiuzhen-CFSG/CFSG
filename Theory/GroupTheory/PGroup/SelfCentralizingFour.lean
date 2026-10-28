module
public import Theory.GroupTheory.InvolutionCentralizerFourRecognition
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import Theory.ElementaryAbelian.Basic

/-!
# A self-centralizing four-group in a finite two-group

The ambient center is nontrivial and lies in the four-group V. A noncentral
involution y in V, together with a central involution z, generates V, so
C(y)=C(V)=V. The proved involution-centralizer recognition gives a dihedral
group or the full semidihedral presentation. V must be proper: the elementary
four-group itself is excluded from the noncentral-involution argument.

Source: the Suzuki lemma used in Aschbacher--Smith C.6.1(6b), printed p.164.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {P : Type*} [Group P] [Finite P]

theorem selfCentralizingFour_involution_witness
    (hP : IsPGroup 2 P) (V : Subgroup P) [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 4) (hproper : V ≠ ⊤)
    (hself : centralizer (V : Set P) = V) :
    ∃ y : P, orderOf y = 2 ∧ y ∉ center P ∧ centralizer ({y} : Set P) = V := by
  have hVne : V ≠ ⊥ := by intro he; simp only [he,card_bot] at hV; omega
  let : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).mpr hVne
  let : Nontrivial P := V.subtype_injective.nontrivial
  let : Nontrivial (center P) := hP.center_nontrivial
  obtain ⟨z,hz1⟩ := exists_ne (1 : center P)
  have hzV : (z : P) ∈ V := hself ▸ center_le_centralizer (V : Set P) z.property
  have hz : orderOf (z : P) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : P) hzV)
    (fun he => hz1 (Subtype.ext he))
  have hnot : ¬ V ≤ zpowers (z : P) := by
    intro he
    have hc := card_le_of_le he
    rw [Nat.card_zpowers,hz,hV] at hc
    omega
  obtain ⟨y,hy,hyz⟩ := SetLike.not_le_iff_exists.mp hnot
  have hy1 : y ≠ 1 := fun he => hyz (he ▸ one_mem _)
  have hy2 : orderOf y = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) y hy) hy1
  have hzy : (z : P) ≠ y := fun he => hyz (he ▸ mem_zpowers (z : P))
  have hcomm : Commute (z : P) y := (mem_center_iff.mp z.property y).symm
  let : IsKleinFour (closure ({(z : P),y} : Set P)) :=
    isKleinFour_closure_pair_of_orderOf (z : P) y hz hy2 hzy hcomm
  have hgen : closure ({(z : P),y} : Set P) = V := by
    apply eq_of_le_of_card_ge
    · exact (closure_le _).mpr (by
        intro a ha
        rcases ha with rfl | rfl
        · exact hzV
        · exact hy)
    · rw [hV,IsKleinFour.card_four]
  have hC : centralizer ({y} : Set P) = V := by
    apply le_antisymm
    · intro a ha
      rw [←hself]
      apply mem_centralizer_iff.mpr
      have hv : V ≤ centralizer ({a} : Set P) := by
        rw [←hgen]
        apply (closure_le _).mpr
        intro v hv
        rcases hv with rfl | rfl
        · exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp z.property a).symm
        · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp ha).symm
      intro v hvV
      exact mem_centralizer_singleton_iff.mp (hv hvV)
    · exact V.le_centralizer.trans (centralizer_le (Set.singleton_subset_iff.mpr hy))
  refine ⟨y,hy2,?_,hC⟩
  intro hyZ
  apply hproper
  rw [←hC]
  exact top_unique (by intro a _; exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hyZ a))

theorem dihedral_or_semidihedral_of_selfCentralizing_four
    (hP : IsPGroup 2 P) (V : Subgroup P) [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 4) (hproper : V ≠ ⊤)
    (hself : centralizer (V : Set P) = V) :
    (∃ m : ℕ, Nonempty (P ≃* DihedralGroup m)) ∨
      (∃ n : ℕ, 4 ≤ n ∧ Nat.card P = 2 ^ n ∧
        ∃ a b : P, orderOf a = 2 ^ (n - 1) ∧ orderOf b = 2 ∧
          b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1) ∧ closure ({a,b} : Set P) = ⊤) := by
  obtain ⟨y,hy,hyZ,hC⟩ := selfCentralizingFour_involution_witness hP V hV hproper hself
  exact exists_dihedral_or_semidihedral_of_involution_centralizer_card_four
    hP y hy hyZ (hC ▸ hV)

end Theory.GroupTheory
