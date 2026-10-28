module

public import Theory.Representation.SLThreeCentralExtension.Involutions
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Mathlib.GroupTheory.Sylow

/-!
# A Sylow criterion for splitting a binary natural extension

A four-dimensional SL₃(2) module with a natural submodule and trivial
quotient splits if a vector outside that submodule is fixed by a subgroup
of index at most two in a genuine Sylow two-subgroup. That subgroup has
even order and contains an involution. If the whole module had no fixed
vectors, the involution's fixed and displacement spaces would agree and
lie in the natural submodule, a contradiction. The natural submodule has
no fixed vectors, so the resulting fixed line is its direct complement.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.72, printed p.1076; the involution calculation replaces the cited
nonsplit-extension exclusion B.4.8(3).
-/

public section

open Matrix Representation Representation.BinaryOffender Subgroup
namespace BinaryLinearThree.NaturalExtension
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  [FiniteDimensional (ZMod 2) M] (ρ : Representation (ZMod 2) Group M)

theorem splitting_of_fixed_involution
    (hdim : Module.finrank (ZMod 2) M = 4)
    (N : Subrepresentation ρ) (e : Representation.Equiv N.toRepresentation W)
    (hquot : ∀ g v, ρ g v - v ∈ N)
    (u : M) (hu : u ∉ N)
    (a : Group) (ha : orderOf a = 2) (hau : ρ a u = u) :
    IsCompl N.toSubmodule ρ.invariants ∧ Module.finrank (ZMod 2) ρ.invariants = 1 := by
  have hn : Module.finrank (ZMod 2) N.toSubmodule = 3 :=
    e.toLinearEquiv.finrank_eq.trans (Module.finrank_fin_fun (ZMod 2))
  have hfix : ρ.invariants ≠ ⊥ := by
    intro hf
    have hc := involution_codim_of_fixed_zero ρ hdim hf a ha
    have heq := (involution_range_eq_fixed ρ hdim a ha hc).1
    have huFix : u ∈ fixedSpace ρ (zpowers a) :=
      (mem_fixedSpace_zpowers_iff ρ a u).mpr hau
    rw [← heq] at huFix
    obtain ⟨v,hv⟩ := huFix
    exact hu (hv ▸ hquot a v)
  have hd : Disjoint N.toSubmodule ρ.invariants := by
    apply Submodule.disjoint_def.mpr
    intro v hv hf
    have hh : e ⟨v,hv⟩ ∈ Representation.OneCohomology.fixed W := by
      intro g
      have he := LinearMap.congr_fun (e.isIntertwining' g) ⟨v,hv⟩
      change e (N.toRepresentation g ⟨v,hv⟩) = W g (e ⟨v,hv⟩) at he
      exact he.symm.trans (congrArg e (Subtype.ext (hf g)))
    rw [Representation.OneCohomology.SLHigherNatural.fixed_eq_bot (by decide : 2 ≤ 3)] at hh
    exact congrArg Subtype.val (e.injective (hh.trans e.map_zero.symm))
  let : Nontrivial ρ.invariants := Submodule.nontrivial_iff_ne_bot.mpr hfix
  have hp : 0 < Module.finrank (ZMod 2) ρ.invariants := Module.finrank_pos
  have hs := N.toSubmodule.finrank_sup_add_finrank_inf_eq ρ.invariants
  rw [hd.eq_bot, finrank_bot, add_zero, hn] at hs
  have hle := (N.toSubmodule ⊔ ρ.invariants).finrank_le
  rw [hdim] at hle
  have hi : Module.finrank (ZMod 2) ρ.invariants = 1 := by omega
  refine ⟨⟨hd, codisjoint_iff.mpr ?_⟩, hi⟩
  apply Submodule.eq_top_of_finrank_eq
  rw [hdim]
  omega

theorem splitting_of_sylow_index
    (hdim : Module.finrank (ZMod 2) M = 4)
    (N : Subrepresentation ρ) (e : Representation.Equiv N.toRepresentation W)
    (hquot : ∀ g v, ρ g v - v ∈ N)
    (u : M) (hu : u ∉ N)
    (P : Sylow 2 Group) (B : Subgroup Group)
    (hBP : B ≤ P) (hindex : B.relIndex P ≤ 2)
    (hBu : ∀ b ∈ B, ρ b u = u) :
    IsCompl N.toSubmodule ρ.invariants ∧ Module.finrank (ZMod 2) ρ.invariants = 1 := by
  have hPcard : Nat.card P = 8 := by
    rw [P.card_eq_multiplicity, Matrix.PSL3Two.card_SL]
    decide +kernel
  have hcard : Nat.card B * B.relIndex P = 8 := by
    have hh := (B.subgroupOf P).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hBP).toEquiv] at hh
    exact hh.trans hPcard
  have hne : Nat.card B ≠ 1 := by intro hh; rw [hh, one_mul] at hcard; omega
  have hp : IsPGroup 2 B := P.isPGroup'.of_injective (Subgroup.inclusion hBP)
    (Subgroup.inclusion_injective hBP)
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 2
    (hp.card_eq_or_dvd.resolve_left hne)
  exact splitting_of_fixed_involution ρ hdim N e hquot u hu b
    ((Subgroup.orderOf_coe b).trans hb) (hBu b b.property)

end BinaryLinearThree.NaturalExtension
