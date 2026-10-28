module
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry.Coordinates
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Tactic.Group
public import Theory.GroupTheory.CharacteristicCentralizerFusion
/-!
# Sylow two-subgroups of S₇ are self-normalizing

The central involutions with supports of size two and four are unique in the
sixteen-word Sylow model. Its normalizer therefore centralizes both. Their
common centralizer is the same Sylow group: three point images determine a
permutation there, and a small coordinate table selects its word. Sylow
conjugacy transports the result. No enumeration of S₇ is required.

Source: Aschbacher–Smith C.5.12, printed p.163, final paragraph.
-/
public section
open Equiv Subgroup
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry
namespace SymmetricSevenSylow
private abbrev doubleSwap : S7 := swap01 * swap23
local instance (a b : S7) : Decidable (Commute a b) :=
  inferInstanceAs (Decidable (a*b=b*a))
private theorem word_central (v : Quadruple) :
    Commute (word v) doubleSwap ∧ Commute (word v) swap45 :=
  (by decide +kernel : ∀ v : Quadruple, Commute (word v) doubleSwap ∧ Commute (word v) swap45) v
private theorem central_word_unique (v : Quadruple)
    (h1 : Commute (word v) swap01) (h2 : Commute (word v) crossSwap) :
    ((word v).support.card = 2 → word v = swap45) ∧
    ((word v).support.card = 4 → word v = doubleSwap) :=
  (by decide +kernel : ∀ v : Quadruple,
    Commute (word v) swap01 → Commute (word v) crossSwap →
    ((word v).support.card = 2 → word v = swap45) ∧
    ((word v).support.card = 4 → word v = doubleSwap)) v h1 h2
set_option synthInstance.maxSize 256 in
private theorem word_selection (a b c : Fin 7)
    (ha : doubleSwap a ≠ a) (hb : doubleSwap b ≠ b)
    (hab : a ≠ b) (hab' : doubleSwap a ≠ b) (hc : swap45 c ≠ c) :
    ∃ v : Quadruple, word v 0 = a ∧ word v 2 = b ∧ word v 4 = c :=
  (by decide +kernel : ∀ a b c : Fin 7,
    doubleSwap a ≠ a → doubleSwap b ≠ b → a ≠ b → doubleSwap a ≠ b →
    swap45 c ≠ c → ∃ v : Quadruple, word v 0 = a ∧ word v 2 = b ∧ word v 4 = c)
    a b c ha hb hab hab' hc
private theorem commuting_values (g : S7) (hd : Commute g doubleSwap) (hs : Commute g swap45) :
    g 1 = doubleSwap (g 0) ∧ g 3 = doubleSwap (g 2) ∧
    g 5 = swap45 (g 4) ∧ g 6 = 6 := by
  have hd0 := congrArg (fun p : S7 => p 0) hd.eq
  have hd2 := congrArg (fun p : S7 => p 2) hd.eq
  have hs4 := congrArg (fun p : S7 => p 4) hs.eq
  have hd6 := congrArg (fun p : S7 => p 6) hd.eq
  have hs6 := congrArg (fun p : S7 => p 6) hs.eq
  change g 1 = doubleSwap (g 0) at hd0
  change g 3 = doubleSwap (g 2) at hd2
  change g 5 = swap45 (g 4) at hs4
  change g 6 = doubleSwap (g 6) at hd6
  change g 6 = swap45 (g 6) at hs6
  exact ⟨hd0,hd2,hs4,(by decide +kernel : ∀ a : Fin 7,
    a = doubleSwap a → a = swap45 a → a = 6) (g 6) hd6 hs6⟩
private theorem commuting_mem (g : S7) (hd : Commute g doubleSwap) (hs : Commute g swap45) :
    g ∈ sylowTwo := by
  obtain ⟨h1,h3,h5,h6⟩ := commuting_values g hd hs
  obtain ⟨v,h0,h2,h4⟩ := word_selection (g 0) (g 2) (g 4)
    (h1 ▸ g.injective.ne (by decide : (1:Fin 7)≠0))
    (h3 ▸ g.injective.ne (by decide : (3:Fin 7)≠2))
    (g.injective.ne (by decide : (0:Fin 7)≠2))
    (h1 ▸ g.injective.ne (by decide : (1:Fin 7)≠2))
    (h5 ▸ g.injective.ne (by decide : (5:Fin 7)≠4))
  obtain ⟨hv1,hv3,hv5,hv6⟩ := commuting_values (word v) (word_central v).1 (word_central v).2
  refine ⟨v,Equiv.ext fun i => ?_⟩
  fin_cases i
  · exact h0
  · change word v 1 = g 1
    rw [hv1,h1,h0]
  · exact h2
  · change word v 3 = g 3
    rw [hv3,h3,h2]
  · exact h4
  · change word v 5 = g 5
    rw [hv5,h5,h4]
  · change word v 6 = g 6
    rw [hv6,h6]

/-- The standard sixteen-word Sylow group is its own normalizer. -/
theorem standard_normalizer : normalizer (sylowTwo : Set S7) = sylowTwo := by
  refine le_antisymm ?_ sylowTwo.le_normalizer
  intro g hg
  have h01 : swap01 ∈ sylowTwo := ⟨(1,0,0,0),by decide +kernel⟩
  have hcross : crossSwap ∈ sylowTwo := ⟨(0,0,1,0),by decide +kernel⟩
  have transport (a : S7) (ha : a ∈ sylowTwo)
      (hc : a ∈ centralizer (sylowTwo : Set S7)) :
      ∃ v : Quadruple, word v = g*a*g⁻¹ ∧
        Commute (word v) swap01 ∧ Commute (word v) crossSwap := by
    obtain ⟨v,hv⟩ := le_normalizer_iff.mp (show normalizer (sylowTwo : Set S7) ≤
      normalizer (sylowTwo : Set S7) from le_rfl) g hg a ha
    have hgC := normalizer_le_normalizer_centralizer sylowTwo hg
    have hc' := le_normalizer_iff.mp (show normalizer (centralizer (sylowTwo : Set S7) : Set S7) ≤
      normalizer (centralizer (sylowTwo : Set S7) : Set S7) from le_rfl) g hgC a hc
    rw [← hv] at hc'
    exact ⟨v,hv,(hc' swap01 h01).symm,(hc' crossSwap hcross).symm⟩
  have hs : g*swap45*g⁻¹ = swap45 := by
    obtain ⟨v,hv,hv1,hv2⟩ := transport swap45 ⟨(0,0,0,1),by decide +kernel⟩ (by
      rintro _ ⟨w,rfl⟩
      exact (word_central w).2.eq)
    have hh : (word v).support.card = 2 := by
      rw [hv,Perm.card_support_conj]
      decide +kernel
    exact hv.symm.trans ((central_word_unique v hv1 hv2).1 hh)
  have hd : g*doubleSwap*g⁻¹ = doubleSwap := by
    obtain ⟨v,hv,hv1,hv2⟩ := transport doubleSwap ⟨(1,1,0,0),by decide +kernel⟩ (by
      rintro _ ⟨w,rfl⟩
      exact (word_central w).1.eq)
    have hh : (word v).support.card = 4 := by
      rw [hv,Perm.card_support_conj]
      decide +kernel
    exact hv.symm.trans ((central_word_unique v hv1 hv2).2 hh)
  exact commuting_mem g (mul_inv_eq_iff_eq_mul.mp hd) (mul_inv_eq_iff_eq_mul.mp hs)
private noncomputable def standardSylow : Sylow 2 S7 :=
  (IsPGroup.of_card (show Nat.card sylowTwo = 2 ^ 4 by rw [sylowTwo_card]; decide)).toSylow (by
    have hh := sylowTwo.card_mul_index
    have hc : Nat.card S7 = 5040 := by
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    rw [sylowTwo_card,hc] at hh
    have hi : sylowTwo.index = 315 := by omega
    rw [hi]
    decide)
/-- Every Sylow two-subgroup of S₇ is self-normalizing. -/
theorem sylow_normalizer_eq_self (P : Sylow 2 S7) :
    normalizer (P : Set S7) = (P : Subgroup S7) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S7 P standardSylow
  let e := MulAut.conj g
  have hmap : (P : Subgroup S7).map e.toMonoidHom = sylowTwo := by
    have hh := congrArg (fun Q : Sylow 2 S7 => (Q : Subgroup S7)) hg
    rwa [Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def] at hh
  apply map_injective (f := e.toMonoidHom) e.injective
  change (normalizer ((P : Subgroup S7) : Set S7)).map e.toMonoidHom =
    (P : Subgroup S7).map e.toMonoidHom
  rw [map_equiv_normalizer_eq,hmap,standard_normalizer]
end SymmetricSevenSylow
