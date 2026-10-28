module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.DesignProjection
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.HexadCover.Quotient
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.HexadCover.Generation

/-!
# The native hexad parabolic retains its triple cover

For every actual hexad b, the full inverse image D of its design stabilizer
has elementary abelian two-core of order sixteen. Its design image is the
literal pointwise hexad kernel. The quotient D/O₂(D) maps onto S₆ with
cubic kernel; the full inverse image of A₆ is quasisimple and is identified
with the even hexacode group over the prescribed six-point projection.
That projection has no homomorphic section.

The pair--hexad and partition stabilizers generate the full design hexad
stabilizer. Cubic survival in a perfect subgroup ensures that any subgroup
of D with this design image is D. Identifying the source-generated subgroup
with these marked positions remains with the parent source assembly.

Source: Aschbacher--Smith 14.4.12, printed pp.1011--1012, and H.12.1(4),
printed pp.393--394. The native matrices and their attribution are inherited
from ActorCatalogue.Native; the marked cover comparison uses GLS 5.2.3.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics

/-- The native two-core and its actual pointwise design image. -/
theorem hexadPreimage_twoCore {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    IsElementaryAbelian 2 (pCore 2 (hexadPreimage b)) ∧
    Nat.card (pCore 2 (hexadPreimage b)) = 16 ∧
    ((hexadPreimage b).pCoreIn 2).map designProjection =
      (m22HexadPointwiseKernel b).map M22ValueBound.Concrete.inclusion :=
  ⟨HexadCover.twoCore_elementary hb, HexadCover.twoCore_card hb,
    HexadCover.twoCore_design_image hb⟩

/-- The quotient is a cubic extension of S₆ with the marked quasisimple A₆ preimage. -/
theorem hexadPreimage_quotient {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    Function.Surjective (HexadCover.quotientSixProjection hb) ∧
    Nat.card (HexadCover.quotientSixProjection hb).ker = 3 ∧
    IsQuasisimple (HexadCover.evenQuotient hb) ∧
    ∃ e : HexadCover.evenQuotient hb ≃* Atlas.Codes.HexEvenAutomorphisms,
      Atlas.Codes.hexEvenCoordinate.comp e.toMonoidHom = HexadCover.evenProjection hb :=
  ⟨HexadCover.quotientSixProjection_surjective hb,
    HexadCover.quotientSixProjection_kernel_card hb,
    HexadCover.evenQuotient_isQuasisimple hb, HexadCover.exists_hexacode_equiv hb⟩

theorem outerPairHexad_sup_outerSecond :
    outerPairHexad ⊔ M22ValueBound.Concrete.outerSecond =
      MulAction.stabilizer m22DesignAut m22Hexad123 :=
  HexadCover.outerPairHexad_sup_outerSecond

/-- This criterion applies to the parent's source-generated native subgroup. -/
theorem eq_hexadPreimage_of_design_image {b : Finset (Fin 22)} (hb : b ∈ m22Blocks)
    (J : Subgroup Model) (hJ : J ≤ hexadPreimage b)
    (hmap : J.map designProjection = MulAction.stabilizer m22DesignAut b) :
    J = hexadPreimage b := HexadCover.eq_hexadPreimage_of_map hb J hJ hmap

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics
