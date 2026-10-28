module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers.Models
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers.ProductMark.SquareClass

/-!
# The two-central mark in the symmetric fixed-subgroup row of HS

The marked double transposition is the square of an even permutation in the
standard `A₈`.  Transporting that square through the supplied fixed-subgroup
equivalence gives a square in the actual HS carrier.  The checked HS
square-class calculation then places this involution in the center of an
actual Sylow two-subgroup.

Source: Aschbacher–Smith I.2.2(5a) and its HS discussion, printed pp.409–412,
and 16.1.5(10), printed p.1172.  The square-class witness is the certified
degree-100 HS calculation in `CoverLayers.ProductMark.SquareClass`.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers
open Subgroup Theory.GroupTheory DoubleCoverCentralizer
open OtherPreliminaries.JankoTwoHigmanSims
open Sporadic.LeechRelated.HS

private theorem symmetric_root_square : ∃ a : A8, a ^ 2 = rootInvolution 3 := by
  let p : Equiv.Perm (Fin 8) :=
    Equiv.swap 0 2 * Equiv.swap 2 1 * Equiv.swap 1 3 * Equiv.swap 4 5
  have hp : p ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  refine ⟨⟨p, hp⟩, ?_⟩
  apply Subtype.ext
  change p ^ 2 = (rootInvolution 3).val
  dsimp [p, rootInvolution]
  decide +kernel

/-- The marked involution in the actual symmetric fixed subgroup is two-central
in HS. -/
theorem symmetricRoot_twoCentral (r : MulAut Carrier)
    (v : r.fixedSubgroup ≃* S8) : TwoCentral (symmetricRoot r v) := by
  obtain ⟨a, ha⟩ := symmetric_root_square
  let f : A8 →* Carrier :=
    r.fixedSubgroup.subtype.comp (v.symm.toMonoidHom.comp symmetricEmbedding)
  apply ProductMark.involution_twoCentral_of_square _ (symmetricRoot_order r v) (f a)
  rw [← map_pow, ha]
  rfl

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers
