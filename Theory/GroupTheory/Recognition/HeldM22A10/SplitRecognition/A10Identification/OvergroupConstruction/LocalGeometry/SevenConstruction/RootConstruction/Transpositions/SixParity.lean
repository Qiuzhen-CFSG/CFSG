module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.Transpositions.ActorRelations
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
/-!
# Parity in the supplied six-point extension

The perfect A6 is the derived subgroup of its extension by mu-prime.
Thus every supplied S6 equivalence identifies A6 with the even permutations.
This is used to transport the finite four-group actor back to the given A6.
Source: Held, Illinois J. Math. 13 (1969), Lemmas 4.2 and 5.10,
DOI 10.1215/ijm/1256053756.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction
variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer) (L : Source.SixLocalData D e)
private theorem six_commutator : ⁅L.A ⊔ zpowers (mu' D e), L.A ⊔ zpowers (mu' D e)⁆ = L.A := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect L.A :=
    Group.IsPerfect.ofSurjective (f := L.alternatingEquiv.symm.toMonoidHom)
      L.alternatingEquiv.symm.surjective
  let X := L.A ⊔ zpowers (mu' D e)
  have hA : L.A ≤ X := le_sup_left
  have hn : zpowers (mu' D e) ≤ normalizer (L.A : Set G) := zpowers_le.mpr L.mu'_normalizes
  let : (L.A.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hA).mpr (sup_le L.A.le_normalizer hn)
  have htop : L.A.subgroupOf X ⊔ (zpowers (mu' D e)).subgroupOf X = ⊤ :=
    (codisjoint_subgroupOf_sup L.A (zpowers (mu' D e))).eq_top
  have hcomm : IsMulCommutative ((zpowers (mu' D e)).subgroupOf X) := inferInstance
  have hder : commutator X ≤ L.A.subgroupOf X :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top htop hcomm
  apply le_antisymm
  · simpa only [map_subtype_commutator, map_subgroupOf_eq_of_le hA] using
      map_mono (f := X.subtype) hder
  · exact L.A.commutator_eq_self.symm.le.trans (commutator_mono hA hA)

public theorem six_even_subgroup :
    (alternatingGroup (Fin 6)).comap L.symmetricEquiv.toMonoidHom =
      L.A.subgroupOf (L.A ⊔ zpowers (mu' D e)) := by
  have hmap : (commutator (L.A ⊔ zpowers (mu' D e) : Subgroup G)).map
      L.symmetricEquiv.toMonoidHom = alternatingGroup (Fin 6) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr L.symmetricEquiv.surjective,
      ← _root_.commutator_def, alternatingGroup.commutator_perm_eq (by simp)]
  rw [← hmap, comap_map_eq_self_of_injective L.symmetricEquiv.injective]
  apply map_subtype_inj.mp
  rw [map_subtype_commutator, map_subgroupOf_eq_of_le le_sup_left]
  exact six_commutator D e L
end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction
