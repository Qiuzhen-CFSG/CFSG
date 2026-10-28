module

public import Theory.Representation.HexacodeAction.Cover
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Three-rank of the concrete hexacode cover

The central scalar of order three and the explicit lift `hexX` generate
an elementary abelian subgroup of order nine. Independence is detected by
the actual coordinate map to A₆. In particular this argument retains the
nonsplit triple cover, rather than replacing it by A₆ or a product.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
A.3.18, printed pp.51–52, and 15.3.49(k), p.1144. The explicit monomial
lift is from the licensed ATLAS port `HexacodeNonsplit`; its cube is checked
in the same concrete coordinates.
-/

@[expose] public section

open Atlas.Codes Subgroup

namespace Representation.Hexacode

def evenX : HexEvenAutomorphisms := ⟨hexX, hexX_even⟩

theorem evenX_cube : evenX ^ 3 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Monomial.ext
  · apply Equiv.ext
    intro i
    revert i
    decide
  · funext i
    apply LinearEquiv.ext
    intro u
    revert i u
    decide

theorem evenX_order : orderOf evenX = 3 := by
  apply orderOf_eq_prime evenX_cube
  intro he
  have hc := congrArg (fun x : HexEvenAutomorphisms => hexCoordinateSixHom x.val) he
  simp only [evenX, OneMemClass.coe_one, map_one] at hc
  rw [hexX_coordinate] at hc
  have hh := DFunLike.congr_fun hc (0 : Fin 6)
  exact (by decide : (1 : Fin 6) ≠ 0) hh

theorem evenX_not_mem_center : evenX ∉ center HexEvenAutomorphisms := by
  rw [← even_kernel_eq_center]
  intro he
  have hc := congrArg (fun x : alternatingGroup (Fin 6) => x.val (0 : Fin 6)) he
  change (hexCoordinateSixHom hexX) 0 = 0 at hc
  rw [hexX_coordinate] at hc
  exact (by decide : (1 : Fin 6) ≠ 0) hc

theorem two_le_primeRank_even : 2 ≤ primeRank 3 HexEvenAutomorphisms := by
  let E := zpowers hexEvenZ
  let : IsElementaryAbelian 3 E :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hexEvenZ_order ▸ pow_orderOf_eq_one hexEvenZ)
  have hE : E ≤ center HexEvenAutomorphisms := by
    rw [← even_kernel_eq_center, hexEvenCoordinate_kernel]
  have hcard : Nat.card E = 3 ^ 1 := by
    rw [Nat.card_zpowers, hexEvenZ_order, pow_one]
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join E evenX evenX_order
    (fun h => evenX_not_mem_center (hE h)) (by
      intro z hz
      exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp (hE hz) evenX).symm) hcard

end Representation.Hexacode
