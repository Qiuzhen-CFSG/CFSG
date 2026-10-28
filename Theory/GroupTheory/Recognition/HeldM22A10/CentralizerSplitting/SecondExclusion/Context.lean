module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Structure
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.FusionConstraints

/-!
# Transport of the second candidate into the actual involution centralizer

An assumed equivalence from the actual involution centralizer to the second
permutation model identifies their distinguished central involutions. It embeds
the concrete exceptional subgroup, of order 64, into the ambient group.
Normalizer control for that image transports to every conjugate by the local
centralizer. Thus the remaining ambient normalizer problem may use one fixed
concrete subgroup, independently of the choice of local Sylow subgroup.

This is preparatory transport for Huppert--Blackburn III, XII.1.18(b), p.314.
It does not prove the exclusion or assume splitting or recognition.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.SecondExclusion
universe u
variable {G : Type u} [Group G] (D : LocalData G)
    (e : D.centralizer ≃* NonsplitModels.Second)

/-- The concrete model's embedding into the actual ambient centralizer. -/
@[expose] public def embedding : NonsplitModels.Second →* G :=
  D.centralizer.subtype.comp e.symm.toMonoidHom

public theorem embedding_injective : Function.Injective (embedding D e) :=
  D.centralizer.subtype_injective.comp e.symm.injective

public theorem embedding_mem (x : NonsplitModels.Second) :
    embedding D e x ∈ D.centralizer := (e.symm x).property

public theorem embedding_range : (embedding D e).range = D.centralizer := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact embedding_mem D e x
  · intro x hx
    refine ⟨e ⟨x, hx⟩, ?_⟩
    change (e.symm (e ⟨x, hx⟩) : G) = x
    simp

/-- The source involution corresponds to the concrete model's central involution. -/
public theorem centralInvolution_image : e D.centralInvolution = Model.centralPoint := by
  have hc : e D.centralInvolution ∈ center NonsplitModels.Second := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [map_mul] using
      congrArg e (mem_center_iff.mp D.centralInvolution_mem_center x)
  rcases Model.center_cases _ hc with h | h
  · have h1 : D.centralInvolution = 1 := e.injective (h.trans e.map_one.symm)
    exact (D.z_ne_one (congrArg D.centralizer.subtype h1)).elim
  · exact h

public theorem embedding_centralPoint : embedding D e Model.centralPoint = D.z := by
  rw [← centralInvolution_image D e]
  change (e.symm (e D.centralInvolution) : G) = D.z
  simp [LocalData.centralInvolution]

/-- The exceptional subgroup remains tied to its actual ambient inclusion. -/
@[expose] public def ambientExceptionalSubgroup : Subgroup G :=
  Model.exceptionalSubgroup.map (embedding D e)

public theorem ambientExceptionalSubgroup_le : ambientExceptionalSubgroup D e ≤ D.centralizer :=
  (map_le_range (embedding D e) Model.exceptionalSubgroup).trans_eq (embedding_range D e)

public theorem ambientExceptionalSubgroup_card : Nat.card (ambientExceptionalSubgroup D e) = 64 := by
  rw [ambientExceptionalSubgroup, card_map_of_injective (embedding_injective D e),
    Model.exceptionalSubgroup_card]

/-- Control for the fixed exceptional subgroup suffices for every local conjugate. -/
public theorem conjugate_normalizer_control
    (h : normalizer (ambientExceptionalSubgroup D e : Set G) ≤ D.centralizer)
    (a : NonsplitModels.Second) :
    normalizer
      ((Model.exceptionalSubgroup.map (MulAut.conj a).toMonoidHom).map
        (embedding D e) : Set G) ≤ D.centralizer := by
  have hmap : (Model.exceptionalSubgroup.map (MulAut.conj a).toMonoidHom).map
      (embedding D e) = (ambientExceptionalSubgroup D e).map
        (MulAut.conj (embedding D e a)).toMonoidHom := by
    rw [ambientExceptionalSubgroup, map_map, map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]
  rw [hmap, ← map_equiv_normalizer_eq]
  rintro _ ⟨x, hx, rfl⟩
  exact D.centralizer.mul_mem
    (D.centralizer.mul_mem (embedding_mem D e a) (h hx))
    (D.centralizer.inv_mem (embedding_mem D e a))

end Theory.GroupTheory.HeldM22A10.SecondExclusion
