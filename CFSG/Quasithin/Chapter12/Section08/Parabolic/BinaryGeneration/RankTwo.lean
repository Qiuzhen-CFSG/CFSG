module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryGeneration.Core

/-!
# Full LT action in the rank-two source alternative

The original elementary seed has order four. Its LT conjugation action
has kernel O₂(LT), and the source quotient is S₃, of the same order as
Aut(V). Thus the literal LT action, and hence P=LT action, is full.
There is no surjectivity requirement on the two-perfect subgroup L.

Source: Aschbacher–Smith, Hypothesis 12.8.1(2), Lemmas 12.8.3 and
12.8.9(1), printed pp.849–850 and 852–853.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

theorem binarySeedAction_rankTwo_surjective (F : InvariantFlag T V 2)
    [IsElementaryAbelian 2 V] (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hcore : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (e : ((L ⊔ (T : Subgroup G) : Subgroup G) ⧸ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) ≃*
      Equiv.Perm (Fin 3)) : Function.Surjective (F.binarySeedAction L hL) := by
  let R := L ⊔ (T : Subgroup G)
  let f := F.binarySeedAction L hL
  have hcard : Nat.card V = 4 := by
    have hc := F.card 2 le_rfl
    rw [F.last] at hc
    norm_num at hc
    exact hc
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour V := ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩
  have hk : f.ker = pCore 2 R := by
    apply map_injective R.subtype_injective
    rw [F.binarySeedAction_ker L hL, subgroupOf_map_subtype, inf_comm, hcore]
    rfl
  have hr : Nat.card f.range = 6 := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hk,
      Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  apply MonoidHom.range_eq_top.mp
  apply eq_of_le_of_card_ge le_top
  rw [Subgroup.card_top, IsKleinFour.card_mulAut]
  exact hr.ge

theorem binaryPlaneAction_rankTwo_surjective (F : InvariantFlag T V 2)
    [IsElementaryAbelian 2 V] (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hcore : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (e : ((L ⊔ (T : Subgroup G) : Subgroup G) ⧸ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) ≃*
      Equiv.Perm (Fin 3)) : Function.Surjective (F.binaryPlaneAction le_rfl L hL) :=
  F.binaryPlaneAction_surjective le_rfl L hL (F.binarySeedAction_rankTwo_surjective L hL hcore e)

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
