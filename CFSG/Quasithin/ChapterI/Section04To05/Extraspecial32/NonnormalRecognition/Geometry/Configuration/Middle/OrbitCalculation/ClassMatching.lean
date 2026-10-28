module
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.OrbitCalculation.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.OrbitCalculation.ClassMatching.Transport
public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.MiddleClassIncidence

/-!
# Endpoint-normalizer class matching for the middle sixteen

The marked affine coordinates identify the actual endpoint E with the
translation kernel, A with the middle radical, and Q with the intrinsic
point two-core. The concrete affine matching is a bijection of the two sets
of outside involutions whose pairs are conjugate. Transporting it back gives
conjugacy in N_G(E), so it restricts to an equivalence over each literal
conjugacy class of that normalizer. Together with |A ∩ E| = 4, this proves
the exact `MiddleClassMatching` contract used by the nine-point fusion count.

All coordinates and model facts are constructed from the given local data
and endpoint splitting. No ambient fusion assertion or A₃ configuration is
required; the separate fusion union belongs to the enclosing assembly.
Source: M. Aschbacher, “A 2-local characterization of M12”, Lemma 2.6(3)
and the final paragraph of Lemma 3.1, printed pp.35–37,
https://authors.library.caltech.edu/records/m3wrn-5w840/files/ASCijm03.pdf.
-/

public section
open Subgroup Matrix.PSL3Two Matrix.PSL3Two.SplitParabolic
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration.OrbitCalculation
variable {G : Type*} [Group G] {z g : G}
namespace ClassMatching
open MiddleClassIncidence

private noncomputable def outsideEquiv {A : Subgroup G}
    (coords : MarkedCoordinates z g A) (B : Subgroup G) (C : Subgroup Block)
    (hB : (B.subgroupOf (endpointNormalizer z g)).map coords.equiv.toMonoidHom = C) :
    normalizerInvolutionsOutside z g B ≃ outsideInvolutions C :=
  coords.equiv.toEquiv.subtypeEquiv (by
    intro x
    have hmem : coords.equiv x ∈ C ↔ (x : G) ∈ B := by
      rw [← hB]
      exact mem_map_iff_mem (f := coords.equiv.toMonoidHom) coords.equiv.injective
    have hker : coords.equiv x ∈ projection.ker ↔ (x : G) ∈ coreIntersection z g := by
      rw [← coords.kernel]
      exact mem_map_iff_mem (f := coords.equiv.toMonoidHom) coords.equiv.injective
    have ho : orderOf (x : G) = orderOf x :=
      orderOf_injective (endpointNormalizer z g).subtype
        (endpointNormalizer z g).subtype_injective x
    change ((x : G) ∈ B ∧ (x : G) ∉ coreIntersection z g ∧ orderOf (x : G) = 2) ↔
      (coords.equiv x ∈ C ∧ coords.equiv x ∉ projection.ker ∧
        orderOf (coords.equiv x) = 2)
    rw [hmem, hker, coords.equiv.orderOf_eq, ho])

/-- The concrete matching transports to conjugacy in the literal endpoint normalizer. -/
theorem class_fibers {A : Subgroup G} (coords : MarkedCoordinates z g A)
    (c : ConjClasses (endpointNormalizer z g)) :
    Nat.card {x : normalizerInvolutionsOutside z g A //
      ConjClasses.mk (x : endpointNormalizer z g) = c} =
    Nat.card {x : normalizerInvolutionsOutside z g (coreInG z) //
      ConjClasses.mk (x : endpointNormalizer z g) = c} := by
  let a := outsideEquiv coords A middleGroup coords.middle
  let q := outsideEquiv coords (coreInG z) (pointPreimage.pCoreIn 2) coords.core
  let e := a.trans (matching.trans q.symm)
  have he (x : normalizerInvolutionsOutside z g A) :
      IsConj (x : endpointNormalizer z g) (e x : endpointNormalizer z g) := by
    have hc := coords.equiv.symm.toMonoidHom.map_isConj (matching_isConj (a x))
    change IsConj (coords.equiv.symm (coords.equiv x)) (e x) at hc
    simpa only [MulEquiv.symm_apply_apply] using hc
  exact Nat.card_congr (e.subtypeEquiv (fun x => by
    rw [ConjClasses.mk_eq_mk_iff_isConj.mpr (he x)]))

end ClassMatching

/-- Intrinsic class matching for the core and the middle sixteen in the split endpoint
normalizer. All model, kernel, marked-centralizer and core premises are discharged. -/
theorem middleClassMatching_of_point_split [Finite G] (h : Hypotheses z)
    (d : IntersectionData z g) (m : MiddleLocalData z)
    (point_split : ∃ K : Subgroup (normalizer (coreIntersection z g : Set G)),
      IsComplement' ((coreIntersection z g).subgroupOf
        (normalizer (coreIntersection z g : Set G))) K) :
    MiddleClassMatching z g m.A := by
  obtain ⟨coords⟩ := ClassMatching.exists_markedCoordinates h d m point_split
  exact ⟨ClassMatching.plane_card d m coords, ClassMatching.class_fibers coords⟩

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration.OrbitCalculation
end
