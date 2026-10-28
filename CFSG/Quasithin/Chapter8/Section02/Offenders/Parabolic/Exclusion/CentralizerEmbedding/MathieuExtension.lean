module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.SmallModels.MathieuEleven
public import Theory.Mathieu.M11.Properties.SylowTwo
public import Theory.GroupTheory.SemidihedralStandardModel
public import Mathlib.GroupTheory.Complement

/-!
# The marked E₉-by-SD₁₆ extension in M₁₁

The checked induced automizer has order sixteen. Since this is the whole
Sylow-two order, its normalizer domain is the entire Sylow subgroup. Thus
an odd Ξ complement permutable with that Sylow is normal in their product.
Order 27 is excluded by |M₁₁|, leaving E₉. The quotient is the original
Sylow complement, identified with the fixed semidihedral model by the
checked generators and relation. An isomorphism transports this normal
subgroup to any marked copy of the product.

This reconstructs an extension: E₉ is the normal kernel and SD₁₆ is the
quotient. It does not assert an unconstructed marking of H/O₂(H).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Proposition 8.2.2(1), p.715. The carrier calculation reused below is
`mathieuEleven_automizer_card`; the Sylow presentation is from
`Theory.Mathieu.M11.Properties.SylowTwo`.
-/

@[expose] public section

open Subgroup Sporadic.Mathieu
open scoped Pointwise
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.XiEmbedding
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction.SmallModels

namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CentralizerEmbedding.Mathieu

private theorem sylow_card (S : Sylow 2 M11) : Nat.card S = 16 := by
  rw [S.card_eq_multiplicity, m11_order]
  decide +kernel

/-- Every actual Sylow two-subgroup is the fixed SD₁₆ model. -/
theorem sylow_equiv (S : Sylow 2 M11) :
    Nonempty (S ≃* Semidihedral.StandardModel 4 (by decide)) := by
  obtain ⟨T, a, b, ha, hb, hab, hgen⟩ := m11_exists_semidihedral_sylow
  obtain ⟨e⟩ := Semidihedral.standardModel_equiv_of_presentation (by decide : 4 ≤ 4)
    a b ha hb hab hgen (sylow_card T)
  exact ⟨(S.equiv T).trans e⟩

/-- The full induced automizer order forces normalization by the whole Sylow. -/
theorem pair_normalizes (S : Sylow 2 M11) (R : Subgroup M11)
    (hR : XiOddQuotient 3 R)
    (hperm : (R : Set M11) * (S : Set M11) = (S : Set M11) * (R : Set M11)) :
    (S : Subgroup M11) ≤ normalizer R := by
  let f := R.normalizerMonoidHom.comp (inclusion
    (show (S : Subgroup M11) ⊓ normalizer R ≤ normalizer R from inf_le_right))
  have hsurj := Nat.card_le_card_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hcard : Nat.card ((S : Subgroup M11) ⊓ normalizer R : Subgroup M11) ≥
      Nat.card S := by
    rw [sylow_card S, ← mathieuEleven_automizer_card S R hR hperm]
    exact hsurj
  have he := eq_of_le_of_card_ge
    (show (S : Subgroup M11) ⊓ normalizer R ≤ S from inf_le_left) hcard
  exact he.symm.le.trans inf_le_right

/-- The odd subgroup is an actual normal E₉ with quotient SD₁₆. -/
theorem pair_extension (S : Sylow 2 M11) (R : Subgroup M11)
    (hR : XiOddQuotient 3 R)
    (hperm : (R : Set M11) * (S : Set M11) = (S : Set M11) * (R : Set M11)) :
    let J : Subgroup M11 := R ⊔ S
    let N := R.subgroupOf J
    ∃ _ : N.Normal, IsElementaryAbelian 3 N ∧ Nat.card N = 9 ∧
      Nonempty ((J ⧸ N) ≃* Semidihedral.StandardModel 4 (by decide)) := by
  obtain ⟨hel, hc⟩ : IsElementaryAbelian 3 R ∧ Nat.card R = 9 := by
    rcases hR with ⟨he, hc⟩ | ⟨_, hc, _⟩
    · exact ⟨he, hc⟩
    · have hd := R.card_subgroup_dvd_card
      rw [hc, m11_order] at hd
      norm_num at hd
  let J : Subgroup M11 := R ⊔ S
  let N := R.subgroupOf J
  let U := (S : Subgroup M11).subgroupOf J
  have hn : N.Normal := (normal_subgroupOf_iff_le_normalizer
    (show R ≤ J from le_sup_left)).mpr
      (sup_le R.le_normalizer (pair_normalizes S R hR hperm))
  let _ := hn
  let _ := hel
  let eN : N ≃* R := subgroupOfEquivOfLe (show R ≤ J from le_sup_left)
  let eU : U ≃* S := subgroupOfEquivOfLe (show (S : Subgroup M11) ≤ J from le_sup_right)
  have hncard : Nat.card N = 9 := (Nat.card_congr eN.toEquiv).trans hc
  have hucard : Nat.card U = 16 := (Nat.card_congr eU.toEquiv).trans (sylow_card S)
  have hd : Disjoint R (S : Subgroup M11) :=
    (IsPGroup.of_card (p := 3) (n := 2) hc).disjoint_of_coprime S.isPGroup' (by decide)
  have hprod := card_set_mul_mul_card_inf R (S : Subgroup M11)
  rw [hd.eq_bot, card_bot, mul_one,
    ← coe_sup_of_set_mul_comm R (S : Subgroup M11) hperm, sylow_card S, hc] at hprod
  have hjcard : Nat.card J = 144 := hprod
  have hUN : U.IsComplement' N := isComplement'_of_coprime
    (by rw [hucard, hncard, hjcard]) (by rw [hucard, hncard]; decide)
  obtain ⟨e⟩ := sylow_equiv S
  exact ⟨hn, IsElementaryAbelian.subgroupOf le_sup_left, hncard,
    ⟨hUN.QuotientMulEquiv.trans (eU.trans e)⟩⟩

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CentralizerEmbedding.Mathieu

namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CentralizerEmbedding.Mathieu

/-- Transport the normal E₉ and its quotient, retaining its exact image. -/
theorem marked_extension {Q : Type*} [Group Q]
    (S : Sylow 2 M11) (R : Subgroup M11)
    (hR : XiOddQuotient 3 R)
    (hperm : (R : Set M11) * (S : Set M11) = (S : Set M11) * (R : Set M11))
    (e : Q ≃* (R ⊔ (S : Subgroup M11) : Subgroup M11)) :
    ∃ (N : Subgroup Q) (_ : N.Normal), IsElementaryAbelian 3 N ∧ Nat.card N = 9 ∧
      N.map e.toMonoidHom = R.subgroupOf (R ⊔ (S : Subgroup M11)) ∧
      Nonempty ((Q ⧸ N) ≃* Semidihedral.StandardModel 4 (by decide)) := by
  obtain ⟨hn, he, hc, ⟨d⟩⟩ := pair_extension S R hR hperm
  let N₀ := R.subgroupOf (R ⊔ (S : Subgroup M11))
  let _ := hn
  let _ := he
  let N := N₀.map e.symm.toMonoidHom
  have hn' : N.Normal := hn.map _ e.symm.surjective
  let _ := hn'
  refine ⟨N, hn', IsElementaryAbelian.map _, ?_, ?_, ?_⟩
  · exact (Nat.card_congr (e.symm.subgroupMap N₀).toEquiv).symm.trans hc
  · simp [N, N₀, map_map]
  · exact ⟨(QuotientGroup.congr N₀ N e.symm rfl).symm.trans d⟩

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CentralizerEmbedding.Mathieu
