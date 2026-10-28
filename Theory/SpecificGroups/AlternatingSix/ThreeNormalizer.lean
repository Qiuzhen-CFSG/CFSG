module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Sylow
/-!
# A nonscalar square in the Sylow-three normalizer of A₆

Two disjoint cubic cycles give an actual Sylow nine. The even permutation
(03)(1425) normalizes this nine and its square inverts a nontrivial cubic.
Sylow conjugacy and surjective normalizer lifting retain the actual actors.
Only the nine coordinate pairs are enumerated; no subgroup census is used.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma45.7, p.245, excluding V=X.
-/

open Subgroup Equiv
namespace AlternatingSix.ThreeNormalizer
public abbrev A6 := alternatingGroup (Fin 6)
private def a : A6 := ⟨Equiv.swap 0 1*Equiv.swap 1 2,by change Perm.sign _=1; decide⟩
private def b : A6 := ⟨Equiv.swap 3 4*Equiv.swap 4 5,by change Perm.sign _=1; decide⟩
private def r : A6 := ⟨Equiv.swap 0 3*(Equiv.swap 1 4*Equiv.swap 4 2*Equiv.swap 2 5),by
  change Perm.sign _=1; decide⟩
private abbrev C3 := Multiplicative (ZMod 3)
private def f : C3×C3 →* A6 where
  toFun x := a^x.1.toAdd.val*b^x.2.toAdd.val
  map_one' := by decide
  map_mul' := by decide
private theorem f_injective : Function.Injective f := by decide
private theorem f_card : Nat.card f.range=9 := by
  rw [←Nat.card_congr (MonoidHom.ofInjective f_injective).toEquiv,Nat.card_prod]
  simp only [Nat.card_eq_fintype_card]
  decide
private theorem r_conjugates : ∀x:C3×C3, ∃y:C3×C3, f y=r*f x*r⁻¹ := by decide
private theorem r_inverse_conjugates : ∀x:C3×C3, ∃y:C3×C3, f y=r⁻¹*f x*r := by decide
private theorem r_normalizes : r∈normalizer (f.range:Set A6) := by
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨y,rfl⟩
    exact r_conjugates y
  · rintro ⟨y,hy⟩
    obtain ⟨w,hw⟩ := r_inverse_conjugates y
    refine ⟨w,?_⟩
    rw [hy] at hw
    exact hw.trans (by group)
private theorem a_mem : a∈f.range := ⟨(Multiplicative.ofAdd (1:ZMod 3),1),by decide⟩
private theorem square_moves : r^2*a*(r^2)⁻¹≠a := by decide

public theorem exists_sylow_three_square_noncentral :
    ∃(P:Sylow 3 A6)(g:A6), g∈normalizer (P:Set A6) ∧
      g^2∉centralizer (P:Set A6) := by
  have hc : Nat.card A6=360 := by rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
  let P : Sylow 3 A6 := Sylow.ofCard f.range (by rw [f_card,hc]; decide +kernel)
  refine ⟨P,r,r_normalizes,?_⟩
  intro hr
  apply square_moves
  have he := (hr a a_mem).symm
  exact mul_inv_eq_iff_eq_mul.mpr he

public theorem exists_square_noncentral_in_sylow (P:Sylow 3 A6) :
    ∃g:A6,g∈normalizer (P:Set A6) ∧ g^2∉centralizer (P:Set A6) := by
  obtain ⟨Q,g,hg,hgc⟩ := exists_sylow_three_square_noncentral
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq A6 Q P
  have he : (Q:Subgroup A6).map (MulAut.conj k).toMonoidHom=P := congrArg Sylow.toSubgroup hk
  refine ⟨k*g*k⁻¹,?_,?_⟩
  · change (MulAut.conj k) g∈normalizer ((P:Subgroup A6):Set A6)
    rw [←he,←map_equiv_normalizer_eq (Q:Subgroup A6) (MulAut.conj k)]
    exact mem_map_of_mem (MulAut.conj k).toMonoidHom hg
  · intro hh
    apply hgc
    intro x hx
    have hxx : k*x*k⁻¹∈(P:Subgroup A6) := he ▸ mem_map_of_mem (MulAut.conj k).toMonoidHom hx
    have hv := hh (k*x*k⁻¹) hxx
    apply (MulAut.conj k).injective
    rw [map_mul,map_mul,map_pow]
    exact hv

public theorem exists_square_noncentral_of_surjective {E : Type*} [Group E] [Finite E]
    (f:E→*A6) (hf:Function.Surjective f) (P:Sylow 3 E) :
    ∃g:E,g∈normalizer (P:Set E) ∧ g^2∉centralizer (P:Set E) := by
  let Q := P.mapSurjective hf
  obtain ⟨a,han,hac⟩ := exists_square_noncentral_in_sylow Q
  change a∈normalizer (((P:Subgroup E).map f):Set A6) at han
  rw [←P.normalizer_map_surjective f hf] at han
  obtain ⟨g,hg,hga⟩ := han
  refine ⟨g,hg,?_⟩
  intro hh
  apply hac
  rintro x ⟨y,hy,rfl⟩
  have he := congrArg f (hh y hy)
  simpa only [map_mul,map_pow,hga] using he
end AlternatingSix.ThreeNormalizer
