module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.ExceptionalEnlargement
import Mathlib.Tactic.Group

/-!
# Complete whole-normalizer placement for native-pair extensions

The common images lie in an actual max2 conjugate. The exceptional image
has a strict two-local enlargement, so it cannot occur at maximal two-local
level. The seed itself is likewise excluded. Thus every pure elementary
overgroup of any conjugate native pair has its whole maximal two-local
normalizer equal to a literal max2 conjugate, without an order restriction.
The arbitrary-radical application retains all original restriction/core maps.
Source: Kleidman--Wilson (1988), Section 2.1, p.489.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
open Cardinality KernelCount QuotientCount.Image
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
open ElementaryEightGeometry NativePair NativePair.Stabilizer LinearFive InvolutionCentralizers.Second
open M22Images.KernelAction InvolutionCentralizers.Second.FiveAction DisplacementActions
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup
  Cardinality.localKernel basis Cardinality.localX Cardinality.localY
set_option backward.isDefEq.respectTransparency true



private theorem map_conj_mul (A : Subgroup Model) (g k : Model) :
    (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*k)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]
private theorem map_conj_one (A : Subgroup Model) :
    A.map (MulAut.conj (1 : Model)).toMonoidHom = A :=
  mem_normalizer_iff_map_conj_eq.mp (normalizer (A : Set Model)).one_mem

/-- Complete native-pair branch under the original maximal TWO-local
hypothesis, including the former exceptional order-sixteen case. -/
theorem native_extension_maximal (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    ∃ k : Model, normalizer (X : Set Model) =
      sourceSubgroup.map (MulAut.conj k).toMonoidHom := by
  have hlarge : 4 < Nat.card X := by
    by_contra hn
    have he : nativePair = X := eq_of_le_of_card_ge hpair (by
      rw [nativePair_card]
      exact Nat.le_of_not_gt hn)
    exact normalizer_not_maximal (he.symm ▸ hmax)
  rcases maximal_pure_extension_after_two_images X hpair hlarge hpure hmax with h | h
  · exact h
  obtain ⟨g,hP,_,_,_,hp,hm,hfour,hpos,_,_⟩ := h
  let Y := X.map (MulAut.conj (g.val : Model)).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  exact (exceptional_not_maximal Y hP hp hpos hfour hm).elim

/-- The same conclusion for an arbitrary original embedding of the native
pair. Its original ambient conjugator is retained in the endpoint map. -/
theorem marked_extension_maximal (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (g : Model)
    (hpair : nativePair.map (MulAut.conj g).toMonoidHom ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    ∃ k : Model, normalizer (X : Set Model) =
      sourceSubgroup.map (MulAut.conj (g*k)).toMonoidHom := by
  let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hP : nativePair ≤ Y := by
    have h := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hpair
    rwa [map_conj_mul,inv_mul_cancel,map_conj_one] at h
  have hp : ∀ v ∈ Y, v ≠ 1 → IsConj a v := by
    rintro v ⟨w,hw,rfl⟩ hv
    exact (hpure w hw (fun he => hv (by rw [he,map_one]))).trans
      (isConj_iff.mpr ⟨g⁻¹,rfl⟩)
  have hn : normalizer (Y : Set Model) = (normalizer (X : Set Model)).map
      (MulAut.conj g⁻¹).toMonoidHom := (map_equiv_normalizer_eq X (MulAut.conj g⁻¹)).symm
  have hm : IsMaximalTwoLocal (normalizer (Y : Set Model)) := by
    rw [hn]
    exact isMaximalTwoLocal_map (MulAut.conj g⁻¹) hmax
  obtain ⟨k,hk⟩ := native_extension_maximal Y hP hp hm
  refine ⟨k,?_⟩
  rw [hn] at hk
  have he := congrArg (fun A : Subgroup Model => A.map (MulAut.conj g).toMonoidHom) hk
  rwa [map_conj_mul,map_conj_mul,mul_inv_cancel,map_conj_one] at he

/-- The arbitrary-radical application of every pure native-pair
extension, with the original normalizer and literal denominator maps. -/
theorem marked_extension_radical (P X : Subgroup Model)
    (hP : P.IsPRadical 2) [IsElementaryAbelian 2 X] (g : Model)
    (hpair : nativePair.map (MulAut.conj g).toMonoidHom ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model)))
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    ∃ k : Model, let L := sourceSubgroup.map (MulAut.conj (g*k)).toMonoidHom
      IsTwoLocal L ∧ normalizer (P : Set Model) ≤ L ∧ P ≤ L ∧
      (normalizer (P.subgroupOf L : Set L)).map L.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf L).IsPRadical 2 ∧
      (normalizer (P.subgroupOf L : Set L)).pCoreIn 2 = P.subgroupOf L ∧
      ((normalizer (P.subgroupOf L : Set L)).pCoreIn 2).map L.subtype = P := by
  obtain ⟨k,hk⟩ := marked_extension_maximal X g hpair hpure hmax
  let L := sourceSubgroup.map (MulAut.conj (g*k)).toMonoidHom
  have hNL : normalizer (P : Set Model) ≤ L := hNX.trans hk.le
  have hPL := P.le_normalizer.trans hNL
  have hNN := hNL.trans L.le_normalizer
  have hc := hP.normalizer_core_subgroupOf L hPL hNN
  refine ⟨k,sourceSubgroup_isTwoLocal.map_equiv (MulAut.conj (g*k)),hNL,hPL,?_,
    hP.subgroupOf_of_normalizer_normalizes L hPL hNN,hc,?_⟩
  · rw [← subgroupOf_normalizer_eq hPL,map_subgroupOf_eq_of_le hNL]
  · rw [hc,map_subgroupOf_eq_of_le hPL]

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
