module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IndexNormal
public import Theory.GroupTheory.PGroup.MaximalIndex

/-!
# Odd order from a cyclic Sylow two-subgroup

A finite group with a cyclic Sylow two-subgroup and no normal subgroup of
index two has odd order. In ABG Chapter II, Section 2, Proposition 2,
article page 15, this is applied to the quotient by a nontrivial normal
subgroup after showing that its Sylow two-subgroup is cyclic.

If the group had even order, two would be its smallest prime divisor.
Burnside's transfer is then a homomorphism onto the chosen Sylow subgroup:
its restriction is the index power map, which is bijective. A maximal
subgroup of this nontrivial two-group has index two, and its inverse image
is a normal subgroup of index two in the original group, a contradiction.
The proof uses Mathlib's transfer and the finite p-group maximal-index theorem.
-/

/-- A cyclic Sylow two-subgroup forces odd order in the absence of normal index two. -/
public theorem odd_card_of_cyclic_sylow_two_of_no_normal_index_two
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) (hP : IsCyclic P)
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2) : Odd (Nat.card G) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  have htwo : 2 ∣ Nat.card G := even_iff_two_dvd.mp heven
  have hmin : (Nat.card G).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr htwo
  have hNC := hP.normalizer_le_centralizer hmin
  let f := MonoidHom.transferSylow P hNC
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨y, hy⟩ := (P.isPGroup'.powEquiv' P.not_dvd_index).surjective x
    refine ⟨y, ?_⟩
    change f.domRestrict (P : Subgroup G) y = x
    rw [show ⇑(f.domRestrict (P : Subgroup G)) = fun x : P => x ^ (P : Subgroup G).index
      from MonoidHom.transferSylow_domRestrict_eq_pow P hNC]
    exact hy
  have hPne : (P : Subgroup G) ≠ ⊥ := by
    intro h
    have hi := P.not_dvd_index
    rw [h, Subgroup.index_bot] at hi
    exact hi htwo
  let : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot _).mpr hPne
  obtain ⟨U, hU⟩ := IsCoatomic.exists_coatom (α := Subgroup P)
  have hindex : (U.comap f).index = 2 :=
    (U.index_comap_of_surjective hsurj).trans (P.isPGroup'.index_of_isCoatom U hU)
  exact hno (U.comap f) ((U.comap f).normal_of_index_eq_two hindex) hindex
