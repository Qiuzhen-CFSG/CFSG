module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.SelectedSource.Backward
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.SelectedSource.Forward
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Endpoint

/-!
# Source assembly of the MS93 local-product argument

The separating-edge source package supplies the residual bounds. Whole
configuration transport gives the forward normal product on the original
critical path. Endpoint noncontainment follows from the original critical
pair and the local edge supplement. No selected backward witness,
separation, span or generation premise remains in this conclusion.

This is exactly the product stage consumed by Geometry's terminal-seed
assembly. The older universal conditional interfaces remain available.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(6) and the following
local-product argument, printed pp.885--886.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {geometry : MS93.Geometry R}

/-- The exact local-product and endpoint-escape contract consumed by Geometry. -/
theorem local_products (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (facts : ContraryLocalFacts geometry)
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hlarge : 6 < geometry.b R) (selected : CentralizerChoice p) :
    ∃ s, Before p.a' p.a s 2 ∧
      ((Vcirc R p.a ⊔ Vcirc R s).subgroupOf (stabilizer R s)).Normal ∧
      ¬ Vcirc R p.c ≤ Q R p.a := by
  obtain ⟨s, hs, hn⟩ := SelectedSource.forward_product_normal source hb modules transfer initial facts
    p bad hlarge selected
  exact ⟨s, hs, hn, endpoint_moving_not_le source p hlarge⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts
