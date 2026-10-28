module
public import CFSG.Quasithin.ChapterF.Section01.RankOneSmallTwoPart
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveOddModels
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.GroupTheory.PerfectFiveSectionSmallCore
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters

/-!
# Source rank-one sections in the Mathieu eleven-point group

The order 7920 permits only PSL₂(4) among nonsolvable source rank-one
sections. In a perfect subgroup with this two-core quotient, the two-core
has order dividing four. The perfect action on that kernel is trivial.
A nontrivial kernel would contain a central involution, but every involution
centralizer in the actual M₁₁ carrier has order 48, prime to five.
Thus the subgroup itself is A₅. A full Sylow normalizing it acts faithfully,
since the same involution-centralizer obstruction removes its two-centralizer.
Its order would divide eight, whereas the M₁₁ Sylow has order sixteen.

The consumer is the actual smaller changed-Sylow containing component in
original 5.2.2. All intrinsic two-core quotients and the full normalizing
Sylow are retained; an arbitrary subgroup having an A₅ section is not excluded.
Source: Aschbacher–Smith F.1.1, A.3.12 and 5.2.2, printed pp.259,
47–48 and 648–649 (`refs/quasithin.pdf`). The exceptional comparison
reuses the attributed ATLAS port under LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source
variable {X : Type*} [Group X] [Finite X]
private theorem solvable_of_six (hc : Nat.card X = 6) : Group.IsSolvable X := by
  apply isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hd
  rw [hc] at hd
  have hh : p = 2 ∨ p = 3 := by
    have := hp.dvd_mul.mp (show p ∣ 2 * 3 from hd)
    exact this.imp ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp)
      ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp)
  exact hh

private theorem unitary_small_solvable {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (hc : Nat.card F = 2 ^ 2)
    (hj : ∀ x, J.conj x = x ^ 2) : Group.IsSolvable J.specialSubgroup := by
  let := HermitianForm.FixedFieldTwo.projective_isSolvable J hc hj
  let : Group.IsSolvable J.specialToProjective.ker :=
    Group.isSolvable_of_isSolvable_injective
      (inclusion_injective J.specialToProjective_ker_le_center)
  exact Group.isSolvable_of_ker_le_range J.specialToProjective.ker.subtype
    J.specialToProjective (by simp)

/-- The M₁₁ order permits only the field-four nonsolvable source rank-one section. -/
theorem IsRankOneModel.mathieu_eleven_section (hm : IsRankOneModel X)
    (hns : ¬ Group.IsSolvable X) (hd : Nat.card X ∣ 7920) :
    ClassicalGroup.IsPSL X 2 4 := by
  have h64 : ¬ 64 ∣ Nat.card X := by
    intro hh
    have := hh.trans hd
    norm_num at this
  cases hm with
  | linear f hf hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by
      simpa only [Nat.card_eq_fintype_card] using hF)
    have hc := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
    rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
      (CharTwo.neg_eq 1),mul_one,hF,←Nat.card_congr e.toEquiv] at hc
    have hpow : 2 ^ f ∣ 7920 := by
      apply dvd_trans (dvd_mul_right _ ((2 ^ f)^2 - 1))
      rwa [←hc]
    have hf4 : f ≤ 4 := by
      by_contra hh
      have hh := (pow_dvd_pow 2 (by omega : 5 ≤ f)).trans hpow
      norm_num at hh
    have hf2 : f = 2 := by
      interval_cases f
      · have hsol := solvable_of_six (by norm_num at hc; exact hc)
        exact (hns hsol).elim
      · rfl
      all_goals rw [hc] at hd; norm_num at hd
    exact ⟨F,inferInstance,inferInstance,by simpa [hf2] using hF,⟨e⟩⟩
  | suzuki m hm =>
    obtain ⟨e⟩ := hm
    by_cases hm0 : m = 0
    · subst m
      let := suzukiZero_isSolvable
      exact (hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
    · apply False.elim
      apply h64
      rw [Nat.card_congr e.toEquiv,suzukiMatrixGroup_card m (by omega)]
      apply dvd_mul_of_dvd_left
      apply dvd_mul_of_dvd_right
      change 2 ^ 6 ∣ (2 ^ (2 * m + 1)) ^ 2
      rw [←pow_mul]
      exact pow_dvd_pow 2 (by omega)
  | projective_unitary f hf hm =>
    obtain ⟨F,_,_,J,hF,hj,⟨e⟩⟩ := hm
    by_cases hf1 : f = 1
    · subst f
      let := HermitianForm.FixedFieldTwo.projective_isSolvable J (by simpa using hF) (by simpa using hj)
      exact (hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
    · apply False.elim
      have hd := HermitianForm.BinarySylowOrder.cube_dvd_card_projective J (by omega : f ≠ 0) hF hj
      rw [←Nat.card_congr e.toEquiv] at hd
      exact h64 ((show 64 ∣ (2 ^ f) ^ 3 from by
        change 2 ^ 6 ∣ (2 ^ f) ^ 3
        rw [←pow_mul]; exact pow_dvd_pow 2 (by omega)).trans hd)
  | special_unitary f hf hm =>
    obtain ⟨F,_,_,J,hF,hj,⟨e⟩⟩ := hm
    by_cases hf1 : f = 1
    · subst f
      let := unitary_small_solvable J (by simpa using hF) (by simpa using hj)
      exact (hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
    · apply False.elim
      have hd := (HermitianForm.BinarySylowOrder.cube_dvd_card_projective J
        (by omega : f ≠ 0) hF hj).trans
        (card_dvd_of_surjective J.specialToProjective J.specialToProjective_surjective)
      rw [←Nat.card_congr e.toEquiv] at hd
      exact h64 ((show 64 ∣ (2 ^ f) ^ 3 from by
        change 2 ^ 6 ∣ (2 ^ f) ^ 3
        rw [←pow_mul]; exact pow_dvd_pow 2 (by omega)).trans hd)
  | dihedral hm =>
    obtain ⟨e⟩ := hm
    let := GLS3.Chapter5.dihedralGroup_isSolvable 5
    exact (hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
end CFSG.Quasithin.ChapterF.Source

namespace CFSG.Quasithin.ChapterF.Source.MathieuEleven
open Sporadic.Mathieu

private theorem centralizer_five_free (t : M11) (ht : orderOf t = 2) :
    ¬ 5 ∣ Nat.card (centralizer ({t} : Set M11)) := by
  have ho : orderOf (MulAut.conj t) = 2 :=
    (orderOf_injective MulAut.conj
      (MulAut.conj_injective_of_center_eq_bot m11_center_eq_bot) t).trans ht
  let a := (MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj t)).symm.trans
    ((m11InvolutoryAutFixedEquiv (MulAut.conj t) ho).trans
      m11InvolutionCentralizer_mulEquiv_gl2.symm)
  rw [Nat.card_congr a.toEquiv,m11_involutionCentralizer_card]
  decide

private theorem no_centralizing_involution (B : Subgroup M11)
    (h5 : 5 ∣ Nat.card B) (t : M11) (htB : t ∈ centralizer (B : Set M11))
    (ht : orderOf t = 2) : False := by
  have hb : B ≤ centralizer ({t} : Set M11) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp htB b hb)
  exact centralizer_five_free t ht (h5.trans (card_dvd_of_le hb))

/-- A perfect subgroup of M₁₁ with a genuine source rank-one two-core quotient
has trivial two-core. The kernel is retained until its central involution is excluded. -/
theorem core_eq_bot (B : Subgroup M11) [Group.IsPerfect B]
    (hns : ¬ Group.IsSolvable B) (hm : IsRankOneModel (B ⧸ pCore 2 B)) :
    pCore 2 B = ⊥ := by
  have hquot : ¬ Group.IsSolvable (B ⧸ pCore 2 B) := by
    intro hh
    let := hh
    let : Group.IsNilpotent (pCore 2 B) := pCore_isNilpotent
    exact hns (Group.isSolvable_of_ker_le_range (pCore 2 B).subtype
      (QuotientGroup.mk' (pCore 2 B)) (by simp))
  have hdiv : Nat.card B ∣ 7920 := m11_order ▸ B.card_subgroup_dvd_card
  have hmodel := hm.mathieu_eleven_section hquot
    ((card_quotient_dvd_card (pCore 2 B)).trans hdiv)
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
  let a := e.trans (Atlas.Comparisons.Exceptional.psl2Card4EquivAlt5 hF)
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := a.isSimpleGroup
  have hc : Nat.card (B ⧸ pCore 2 B) = 60 := by
    rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    norm_num
  have h5 : 5 ∣ Nat.card B := (by rw [hc]; decide : 5 ∣ Nat.card (B ⧸ pCore 2 B)).trans
    (card_quotient_dvd_card (pCore 2 B))
  have hsmall : Nat.card (pCore 2 B) ∣ 8 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 B),hc] at hdiv
    have hd : Nat.card (pCore 2 B) ∣ 4 * 33 :=
      (Nat.mul_dvd_mul_iff_left (by decide : 0 < 60)).mp hdiv
    have hcop : Nat.Coprime (Nat.card (pCore 2 B)) 33 := by
      obtain ⟨r,hr⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
      rw [hr]
      exact (by decide : Nat.Coprime 2 33).pow_left r
    exact (hcop.dvd_of_dvd_mul_right hd).trans (by decide : 4 ∣ 8)
  have hz := pCore_two_le_center_of_perfect_simple_five_section
    (by rw [hc]; decide : 5 ∣ Nat.card (B ⧸ pCore 2 B)) hsmall
  by_contra hnon
  let : Nontrivial (pCore 2 B) := (nontrivial_iff_ne_bot _).mpr hnon
  have htwo : 2 ∣ Nat.card (pCore 2 B) :=
    (pCore_isPGroup (p := 2) (G := B)).card_eq_or_dvd.resolve_left (by
      intro hh
      exact hnon (card_eq_one.mp hh))
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := pCore 2 B) 2 htwo
  apply no_centralizing_involution B h5 (t : B)
  · intro b hb
    exact congrArg Subtype.val (mem_center_iff.mp (hz t.property) ⟨b,hb⟩)
  · simpa only [orderOf_coe] using ht

/-- A full Sylow of M₁₁ cannot normalize a nonsolvable perfect subgroup
whose literal two-core quotient is a source rank-one model. -/
theorem not_rankOne_quotient (S : Sylow 2 M11) (B : Subgroup M11)
    [Group.IsPerfect B] (hns : ¬ Group.IsSolvable B)
    (hn : (S : Subgroup M11) ≤ normalizer (B : Set M11)) :
    ¬ IsRankOneModel (B ⧸ pCore 2 B) := by
  intro hm
  have hz := core_eq_bot B hns hm
  let a : (B ⧸ pCore 2 B) ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  have hquot : ¬ Group.IsSolvable (B ⧸ pCore 2 B) := by
    intro hh
    let := hh
    exact hns (Group.isSolvable_of_surjective (f := a.toMonoidHom) a.surjective)
  have hmodel := hm.mathieu_eleven_section hquot
    ((card_quotient_dvd_card (pCore 2 B)).trans (m11_order ▸ B.card_subgroup_dvd_card))
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
  let b := a.symm.trans (e.trans (Atlas.Comparisons.Exceptional.psl2Card4EquivAlt5 hF))
  have hc : Nat.card B = 60 := by
    rw [Nat.card_congr b.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    norm_num
  apply ChapterA.Section03.SourceEmbeddings.AlternatingFive.not_sixteen_dvd_of_no_involution
    S B b hn (no_centralizing_involution B (by rw [hc]; decide))
  rw [m11_order]
  decide

end CFSG.Quasithin.ChapterF.Source.MathieuEleven
