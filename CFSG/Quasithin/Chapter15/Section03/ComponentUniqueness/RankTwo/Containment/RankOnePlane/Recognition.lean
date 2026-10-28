module

public import GorensteinWalter.NormalKleinFourIndexThree
public import Theory.GroupTheory.PPerfectHom


/-!
# Recognition from a self-centralizing four-group

A finite two-perfect group with a normal self-centralizing Klein four-group
is A₄. Conjugation on the three nonidentity elements has trivial sign,
so the four-group has index dividing three. Index one would make the entire
two-perfect group a nontrivial two-group. The index-three recognition theorem
then constructs the actual multiplicative equivalence.

This is the elementary actor-recognition step used in Aschbacher--Smith,
proof of 15.3.40, printed p.1138 of the combined manuscript (1 March 2004).
-/

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane

private def nonidentityPerm {K : Type*} [Group K] :
    MulAut K →* Equiv.Perm {x : K // x ≠ 1} where
  toFun f := Equiv.Perm.subtypePerm f.toEquiv (fun x => f.map_ne_one_iff)
  map_one' := by ext x; rfl
  map_mul' f g := by ext x; rfl

private theorem nonidentityPerm_injective {K : Type*} [Group K] :
    Function.Injective (nonidentityPerm (K := K)) := by
  intro f g h
  ext x
  by_cases hx : x = 1
  · simp [hx]
  · exact congrArg Subtype.val (Equiv.congr_fun h ⟨x, hx⟩)

/-- A normal self-centralizing four-group in a finite two-perfect group
identifies the entire group with A₄. -/
public theorem alternating_four_of_pPerfect_selfCentralizing_kleinFour {H : Type*} [Group H] [Finite H] (K : Subgroup H) [K.Normal]
    [IsKleinFour K] (hc : centralizer (K : Set H) = K)
    (hp : IsPPerfect 2 H) : Nonempty (H ≃* alternatingGroup (Fin 4)) := by
  classical
  let X := {x : K // x ≠ 1}
  let : Fintype X := Fintype.ofFinite X
  have hX : Nat.card X = 3 := by
    change (({1} : Set K)ᶜ).ncard = 3
    rw [Set.ncard_compl, IsKleinFour.card_four, Set.ncard_singleton]
  let f : H →* Equiv.Perm X := nonidentityPerm.comp MulAut.conjNormal
  have hsign : Equiv.Perm.sign.comp f = 1 := by
    apply hp.hom_eq_one_of_isPGroup
    exact IsPGroup.of_card (n := 1) (by simp [Nat.card_eq_fintype_card])
  let g : H →* alternatingGroup X := f.codRestrict _ (fun x => by
    change Equiv.Perm.sign (f x) = 1
    exact DFunLike.congr_fun hsign x)
  have hk : g.ker = K := by
    trans centralizer (K : Set H)
    · ext x
      change g x = 1 ↔ x ∈ centralizer (K : Set H)
      constructor
      · intro hx y hy
        have hfx : f x = 1 := congrArg Subtype.val hx
        have ha : (MulAut.conjNormal (H := K) x) = 1 :=
          nonidentityPerm_injective (by exact hfx)
        have hz := congrArg Subtype.val (DFunLike.congr_fun ha (⟨y,hy⟩ : K))
        change x * y * x⁻¹ = y at hz
        exact (mul_inv_eq_iff_eq_mul.mp hz).symm
      · intro hx
        apply Subtype.ext
        apply Equiv.ext
        intro y
        apply Subtype.ext
        apply Subtype.ext
        change x * (y.val : H) * x⁻¹ = y.val
        exact mul_inv_eq_iff_eq_mul.mpr ((hx y.val y.val.property).symm)
    · exact hc
  have hindex : K.index ∣ 3 := by
    rw [← hk, Subgroup.index_ker]
    have hh := g.range.card_subgroup_dvd_card
    have ha : Nat.card (alternatingGroup X) = 3 := by
      let : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      rw [nat_card_alternatingGroup, hX]
      decide
    rwa [ha] at hh
  have hi : K.index = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hindex with hi | hi
    · have ht : K = ⊤ := (Subgroup.index_eq_one.mp hi)
      have hH : Nat.card H = 4 := by
        rw [← Subgroup.card_top, ← ht]
        exact IsKleinFour.card_four
      have hone := hp.hom_eq_one_of_isPGroup
        (IsPGroup.of_card (n := 2) hH) (MonoidHom.id H)
      have he : ∀ x : H, x = 1 := fun x => DFunLike.congr_fun hone x
      have hs : Subsingleton H := ⟨fun x y => (he x).trans (he y).symm⟩
      let := hs
      simp at hH
    · exact hi
  exact GorensteinWalter.mulEquiv_alternatingGroup_four_of_normal_kleinFour_index_three
    K inferInstance inferInstance hc hi
end CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane
