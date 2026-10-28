module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers.Models
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers.ProductMark.SquareClass

/-!
# The two-central mark in the product fixed-subgroup row of HS

The marked double transposition (0 1)(2 3) is the square of the even
permutation (0 2 1 3)(4 5) in A₆. Its image under the actual inner embedding,
the supplied fixed-subgroup equivalence, and the inclusion into HS remains
an involutory square. The HS square-class calculation makes it two-central.
No simplicity, perfectness, or order assumption on the actor is needed.

Source: Aschbacher–Smith I.2.2(5a) and its HS discussion, printed pp.409–412,
and 16.1.5(10), printed p.1172. This proves the product-row mark needed by
the separate covering-layer assembly, without assuming a covering section.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers
open Subgroup Theory.GroupTheory DoubleCoverCentralizer
open OtherPreliminaries.JankoTwoHigmanSims
open Sporadic.LeechRelated.HS

private theorem product_root_square : ∃ a : A6, a ^ 2 = rootInvolution 1 := by
  let p : Equiv.Perm (Fin 6) :=
    Equiv.swap 0 2 * Equiv.swap 2 1 * Equiv.swap 1 3 * Equiv.swap 4 5
  have hp : p ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  refine ⟨⟨p, hp⟩, ?_⟩
  apply Subtype.ext
  change p ^ 2 = (rootInvolution 1).val
  dsimp [p, rootInvolution]
  decide +kernel

/-- The marked involution in the actual inner A₆ component of any supplied
product fixed subgroup is two-central in HS. -/
theorem productRoot_twoCentral (r : MulAut Carrier)
    (v : r.fixedSubgroup ≃* C2 × MulAut A6) : TwoCentral (productRoot r v) := by
  obtain ⟨a, ha⟩ := product_root_square
  let f : A6 →* Carrier :=
    r.fixedSubgroup.subtype.comp (v.symm.toMonoidHom.comp productEmbedding)
  apply ProductMark.involution_twoCentral_of_square _ (productRoot_order r v) (f a)
  rw [← map_pow, ha]
  rfl

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers
