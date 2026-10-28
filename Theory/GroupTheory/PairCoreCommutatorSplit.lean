module

public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicSetup

/-!
# Converting a paired core split to commutator layers

The source pair gives a decomposition of the ambient 2-core into the two
natural block layers.  This generic lemma rewrites those layers as the
ambient-core commutators, with the order chosen for the two opposite
centralizer factors.
-/

public section
open Subgroup
open CFSG.Quasithin.ChapterC
namespace Theory.GroupTheory

variable {H : Type*} [Group H] [Finite H] {U A B : Subgroup H}

theorem pair_core_commutator_split
    (hU : U = pCore 2 H)
    (hA : IsBlock A) (hB : IsBlock B)
    (hsplit : pCore 2 H = (blockU A).map A.subtype ⊔
      (blockU B).map B.subtype) :
    U = ⁅U,B⁆ ⊔ ⁅U,A⁆ := by
  rw [hU, hB.ambient_core_commutator, hA.ambient_core_commutator]
  simpa only [sup_comm] using hsplit

end Theory.GroupTheory
