module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.Defs
public import Mathlib.Data.Finite.Perm

/-!
# Transitive support factors are diagonal

For a transitive family of prime-order factors generating the core, a
normal subgroup containing one factor contains the entire core. Thus a
coordinate projection of an S₃ × S₃ marking cannot kill one order-three
factor: it would kill the order-nine core, embedding that core into the
other group of order six. Every coordinate restriction is therefore
injective, with range of order three.

This supplies the diagonal clause of Aschbacher--Smith D.2.14(7)(i),
printed p.187, conditional on the literal factors and their transitivity.
It works for every isomorphism to the specified symmetric-group product.
-/

public section

open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {P A : Subgroup G} {s : ℕ}

omit [Finite G] in
private theorem core_le_of_normal (d : SupportFactors ρ P s)
    (ht : d.IsTransitive A) (N : Subgroup G) [N.Normal]
    (i : Fin s) (hi : d.ambient i ≤ N) : P ≤ N := by
  have hall (j : Fin s) : d.ambient j ≤ N := by
    obtain ⟨a, ha⟩ := ht i j
    rw [← ha]
    refine (Subgroup.map_mono hi).trans ?_
    rintro x ⟨n, hn, rfl⟩
    exact Subgroup.Normal.conj_mem (inferInstance : N.Normal) n hn (a : G)
  intro x hx
  obtain ⟨v, hv⟩ := d.multiply_bijective.2 ⟨x, hx⟩
  have hmem (j : Fin s) : ((v j : P) : G) ∈ N :=
    hall j (Subgroup.mem_map_of_mem P.subtype (v j).property)
  have hh : P.subtype ((List.ofFn fun j => (v j : P)).prod) ∈ N := by
    rw [map_list_prod, List.map_ofFn]
    apply N.list_prod_mem
    intro y hy
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    exact hmem j
  have he : P.subtype ((List.ofFn fun j => (v j : P)).prod) = x :=
    congrArg Subtype.val hv
  rwa [he] at hh

private theorem injective_factor (d : SupportFactors ρ P s)
    (ht : d.IsTransitive A) {H : Type*} [Group H] (f : G →* H)
    (hn : ¬ P ≤ f.ker) (i : Fin s) :
    Function.Injective (f.comp (d.inclusion i)) := by
  let k := (f.comp (d.inclusion i)).ker
  have hd : Nat.card k ∣ 3 := by
    rw [← d.card_factor i]
    exact k.card_subgroup_dvd_card
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with hk | hk
  · exact (MonoidHom.ker_eq_bot_iff _).mp (Subgroup.card_eq_one.mp hk)
  · have hk' : k = ⊤ := k.eq_top_of_card_eq (hk.trans (d.card_factor i).symm)
    have hi : d.ambient i ≤ f.ker := by
      rintro x ⟨p, hp, rfl⟩
      have hh : (⟨p, hp⟩ : d.factor i) ∈ k := by rw [hk']; trivial
      exact hh
    exact (hn (core_le_of_normal d ht f.ker i hi)).elim

/-- Transitivity forces both projections to be faithful on every marked factor. -/
theorem SupportFactors.isDiagonal_of_isTransitive (d : SupportFactors ρ P s) (hP : Nat.card P = 9)
    (ht : d.IsTransitive A)
    (e : G ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    d.IsDiagonal e := by
  let f := (MonoidHom.fst (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3))).comp e.toMonoidHom
  let g := (MonoidHom.snd (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3))).comp e.toMonoidHom
  have hfg : ¬ P ≤ f.ker := by
    intro hh
    have hi : Function.Injective (g.comp P.subtype) := by
      intro x y hxy
      apply Subtype.ext
      apply e.injective
      apply Prod.ext
      · exact (show f x = 1 from hh x.property).trans
          (show f y = 1 from hh y.property).symm
      · exact hxy
    have hd := Subgroup.card_dvd_of_injective (g.comp P.subtype) hi
    rw [hP, Nat.card_perm] at hd
    norm_num [Nat.factorial] at hd
  have hgf : ¬ P ≤ g.ker := by
    intro hh
    have hi : Function.Injective (f.comp P.subtype) := by
      intro x y hxy
      apply Subtype.ext
      apply e.injective
      apply Prod.ext
      · exact hxy
      · exact (show g x = 1 from hh x.property).trans
          (show g y = 1 from hh y.property).symm
    have hd := Subgroup.card_dvd_of_injective (f.comp P.subtype) hi
    rw [hP, Nat.card_perm] at hd
    norm_num [Nat.factorial] at hd
  intro i
  have hf := injective_factor d ht f hfg i
  have hg := injective_factor d ht g hgf i
  refine ⟨hf, hg, ?_, ?_⟩
  · exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans (d.card_factor i)
  · exact (Nat.card_congr (MonoidHom.ofInjective hg).toEquiv).symm.trans (d.card_factor i)
end CFSG.Quasithin.ChapterD.FittingConfigurations
