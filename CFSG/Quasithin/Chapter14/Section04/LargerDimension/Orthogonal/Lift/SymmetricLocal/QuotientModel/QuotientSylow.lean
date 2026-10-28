module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.QuotientModel.Source
public import Theory.Representation.OrthogonalFourPlusMatrix.QuotientLocal.SwapSylow

/-!
# The selected quotient involution has the required local Sylow

The marked component action embeds the literal quotient H/O₂(H) faithfully
in Aut(A₅ × A₅), contains all inner automorphisms, and sends the selected i*
to the factor swap. The structural swap-centralizer theorem therefore makes
the intersection with the image of the original T a Sylow subgroup. This
supplies precisely the quotient premise of `lift_local_sylow_of_quotient`;
neither the original Sylow nor the selected involution is conjugated.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010, using case (3) of
14.4.2, printed pp.1006–1007, and G.11.2(7).
-/

public section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.QuotientModel
open Subgroup
open ClassicalOrthogonal.FourPlusMatrix.QuotientLocal
variable {G : Type*} [Group G] [Finite G]

/-- The exact quotient-centralizer Sylow required in the local normalizer
calculation, deduced from the selected component data. -/
theorem quotient_centralizer_sylow_of_selected
    (T : Sylow 2 G) (z i : G)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hiT : i ∈ T) (hiz : i ∈ centralizer ({z} : Set G))
    (d : SelectedComponentData
      ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G)))
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))) ⟨i,hiz⟩)
      (((diagonalResidual (centralizer ({z} : Set G)) i).subgroupOf
        (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))) :
    let H := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 H)
    let B := centralizer ({q ⟨i,hiz⟩} : Set (H ⧸ pCore 2 H))
    ∃ R : Sylow 2 B, (R : Subgroup B) =
      (((T : Subgroup G).subgroupOf H).map q).subgroupOf B := by
  exact exists_swap_centralizer_sylow d.action d.action_injective d.inner_le_range
    (quotientSylow T z hTz) _ (selected_mem_quotientSylow T z i hTz hiT) d.action_exchange

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.QuotientModel
