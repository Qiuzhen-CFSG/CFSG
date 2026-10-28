module
public import Theory.SpecificGroups.SymmetricSevenSylowNormalizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating
/-!
# Sylow two-normalizers in A₇ and its symmetric overgroups

The even part of the sixteen-word S₇ Sylow model has eight elements. Its
center and unique common fixed point force a normalizing permutation into
the original sixteen-word group. The even normalizer is therefore the eight-
element subgroup itself. Sylow conjugacy transports the calculation; index
two then treats every subgroup of S₇ containing A₇.
Only tables on sixteen words and seven points are checked.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/
public section
open Equiv Subgroup
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry
namespace AlternatingSevenSylow
private abbrev doubleSwap : S7 := swap01 * swap23
private abbrev c : S7 := swap01 * swap45
private abbrev A7 := alternatingGroup (Fin 7)
private def evenTwo : Subgroup S7 := sylowTwo ⊓ A7
local instance (a b : S7) : Decidable (Commute a b) :=
  inferInstanceAs (Decidable (a*b=b*a))
private theorem word_central (v : Quadruple) :
    Commute (word v) doubleSwap ∧ Commute (word v) swap45 :=
  (by decide +kernel : ∀ v : Quadruple, Commute (word v) doubleSwap ∧ Commute (word v) swap45) v
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


private theorem central_unique (v : Quadruple) (hev : word v ∈ A7)
    (hx : Commute (word v) crossSwap) (hc : Commute (word v) c)
    (hne : word v ≠ 1) : word v = doubleSwap :=
  (by decide +kernel : ∀ v : Quadruple, Perm.sign (word v) = 1 →
    Commute (word v) crossSwap → Commute (word v) c → word v ≠ 1 → word v = doubleSwap)
    v hev hx hc hne
set_option synthInstance.maxSize 256 in
private theorem normalizer_even_le (g : S7) (hg : g ∈ normalizer (evenTwo : Set S7)) :
    g ∈ sylowTwo := by
  have hx : crossSwap ∈ evenTwo := ⟨⟨(0,0,1,0),by decide +kernel⟩,by change Perm.sign _ = 1; decide +kernel⟩
  have hc : c ∈ evenTwo := ⟨⟨(1,0,0,1),by decide +kernel⟩,by change Perm.sign _ = 1; decide +kernel⟩
  have hz : doubleSwap ∈ evenTwo := ⟨⟨(1,1,0,0),by decide +kernel⟩,by change Perm.sign _ = 1; decide +kernel⟩
  have hzC : doubleSwap ∈ centralizer (evenTwo : Set S7) := by
    rintro _ ⟨⟨v,rfl⟩,_⟩
    exact (word_central v).1.eq
  have hconj := le_normalizer_iff.mp le_rfl g hg doubleSwap hz
  obtain ⟨v,hv⟩ := hconj.1
  have hconjC := le_normalizer_iff.mp le_rfl g
    (normalizer_le_normalizer_centralizer evenTwo hg) doubleSwap hzC
  rw [← hv] at hconjC
  have hd : g*doubleSwap*g⁻¹ = doubleSwap := hv.symm.trans
    (central_unique v (hv ▸ hconj.2) (hconjC _ hx).symm (hconjC _ hc).symm (by
      intro he
      have hh : (MulAut.conj g) doubleSwap = (MulAut.conj g) 1 := by simpa using hv.symm.trans he
      have hn := (MulAut.conj g).injective hh
      exact (by decide +kernel : doubleSwap ≠ 1) hn))
  have fixed (a : S7) (ha : a ∈ evenTwo) : a (g 6) = g 6 := by
    obtain ⟨w,hw⟩ := (le_normalizer_iff.mp le_rfl g⁻¹ (inv_mem hg) a ha).1
    have hh := congrArg (fun p : S7 => p 6) hw
    have hf : word w 6 = 6 := (by decide +kernel : ∀ w : Quadruple, word w 6 = 6) w
    rw [hf] at hh
    have hh' := congrArg g hh
    simpa only [Perm.mul_apply,Perm.inv_def,Equiv.apply_symm_apply,Equiv.symm_symm,inv_inv] using hh'.symm
  have hg6 : g 6 = 6 := (by decide +kernel : ∀ i : Fin 7,
    crossSwap i = i → c i = i → i = 6) (g 6) (fixed _ hx) (fixed _ hc)
  have hdc : Commute g doubleSwap := mul_inv_eq_iff_eq_mul.mp hd
  have h45 : swap (g 4) (g 5) = swap45 := by
    have h4 := congrArg (fun p : S7 => p 4) hdc.eq
    have h5 := congrArg (fun p : S7 => p 5) hdc.eq
    change g 4 = doubleSwap (g 4) at h4
    change g 5 = doubleSwap (g 5) at h5
    exact (by decide +kernel : ∀ a b : Fin 7, a = doubleSwap a → b = doubleSwap b →
      a ≠ 6 → b ≠ 6 → a ≠ b → swap a b = swap45) (g 4) (g 5) h4 h5
      (hg6 ▸ g.injective.ne (by decide : (4:Fin 7)≠6))
      (hg6 ▸ g.injective.ne (by decide : (5:Fin 7)≠6))
      (g.injective.ne (by decide : (4:Fin 7)≠5))
  have hsc : Commute g swap45 := by
    change g * swap 4 5 = swap45 * g
    rw [Equiv.mul_swap_eq_swap_mul,h45]
  exact commuting_mem g hdc hsc
private theorem even_card : Nat.card evenTwo = 8 := by
  let f : sylowTwo →* ℤˣ := Perm.sign.comp sylowTwo.subtype
  have hf : Function.Surjective f := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1,map_one f⟩
    · exact ⟨⟨swap45,⟨(0,0,0,1),by decide +kernel⟩⟩,by
        change Perm.sign swap45 = -1
        decide +kernel⟩
  have hi : f.ker.index = 2 := by
    rw [index_ker,MonoidHom.range_eq_top.mpr hf,
      Nat.card_congr (Subgroup.topEquiv (G := ℤˣ)).toEquiv,Nat.card_eq_fintype_card]
    decide
  have hc := f.ker.card_mul_index
  rw [hi,sylowTwo_card] at hc
  let e : evenTwo ≃ f.ker := {
    toFun x := ⟨⟨x.val,x.property.1⟩,x.property.2⟩
    invFun x := ⟨x.val.val,x.val.property,x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Nat.card_congr e]
  omega
private def standard : Subgroup A7 := sylowTwo.subgroupOf A7
private theorem standard_map : standard.map A7.subtype = evenTwo := by
  rw [standard,subgroupOf_map_subtype]
  rfl
private theorem standard_card : Nat.card standard = 8 := by
  rw [← card_map_of_injective A7.subtype_injective,standard_map,even_card]
private theorem standard_normalizer : normalizer (standard : Set A7) = standard := by
  apply le_antisymm ?_ standard.le_normalizer
  intro g hg
  have hh := standard.le_normalizer_map A7.subtype (mem_map_of_mem A7.subtype hg)
  rw [standard_map] at hh
  exact normalizer_even_le g hh
private noncomputable def standardSylow : Sylow 2 A7 :=
  (IsPGroup.of_card (show Nat.card standard = 2 ^ 3 by rw [standard_card]; decide)).toSylow (by
    have hh := standard.card_mul_index
    have hc : Nat.card A7 = 2520 := by
      change Nat.card (alternatingGroup (Fin 7)) = 2520
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [standard_card,hc] at hh
    have hi : standard.index = 315 := by omega
    rw [hi]
    decide)
theorem sylow_normalizer_eq_self (P : Sylow 2 (alternatingGroup (Fin 7))) :
    normalizer (P : Set (alternatingGroup (Fin 7))) = (P : Subgroup _) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A7 P standardSylow
  let e := MulAut.conj g
  have hmap : (P : Subgroup A7).map e.toMonoidHom = standard := by
    have hh := congrArg (fun Q : Sylow 2 A7 => (Q : Subgroup A7)) hg
    rwa [Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def] at hh
  apply map_injective (f := e.toMonoidHom) e.injective
  change (normalizer ((P : Subgroup A7) : Set A7)).map e.toMonoidHom =
    (P : Subgroup A7).map e.toMonoidHom
  rw [map_equiv_normalizer_eq,hmap,standard_normalizer]
private theorem transport {H D : Type*} [Group H] [Group D] [Finite H] [Finite D]
    (e : H ≃* D) (P : Sylow 2 H)
    (h : ∀ Q : Sylow 2 D, normalizer (Q : Set D) = (Q : Subgroup D)) :
    normalizer (P : Set H) = (P : Subgroup H) := by
  apply map_injective (f := e.toMonoidHom) e.injective
  change (normalizer ((P : Subgroup H) : Set H)).map e.toMonoidHom =
    (P : Subgroup H).map e.toMonoidHom
  rw [map_equiv_normalizer_eq]
  exact h (P.mapSurjective e.surjective)
theorem overgroup_sylow_normalizer (J : Subgroup S7) (hJ : alternatingGroup (Fin 7) ≤ J) (P : Sylow 2 J) :
    normalizer (P : Set J) = (P : Subgroup J) := by
  have hd : J.index ∣ 2 := (alternatingGroup.index_eq_two (α := Fin 7)) ▸ index_dvd_of_le hJ
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h | h
  · have hj : J = ⊤ := index_eq_one.mp h
    exact transport ((MulEquiv.subgroupCongr hj).trans topEquiv) P
      SymmetricSevenSylow.sylow_normalizer_eq_self
  · have hj : J = A7 := Perm.eq_alternatingGroup_of_index_eq_two h
    exact transport (MulEquiv.subgroupCongr hj) P sylow_normalizer_eq_self
end AlternatingSevenSylow
