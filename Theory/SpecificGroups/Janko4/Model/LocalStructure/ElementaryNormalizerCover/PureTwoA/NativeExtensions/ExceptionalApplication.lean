module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.ExceptionalCentralizer
import Mathlib.Tactic.Group

/-!
# Maximal native-pair extensions outside the exceptional order sixteen

The actual image reduction and exact exceptional kernel calculation force
every unresolved pure extension to have order sixteen. Every other proper
pure extension of a conjugate native pair therefore has its WHOLE normalizer
in a literal max2 conjugate. The final theorem applies this result to the
original arbitrary radical, retaining the local normalizer restriction and
both two-core identities. No saturation or invariant-plane reduction is used.

The exceptional order-sixteen centralizer identification and the independent
no-native-pair branch remain required for the full cover.
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

/-- Every remaining actual subgroup has order sixteen, exact fixed kernel
for its full centralizer, and centralizer order 256. Both whole
ambient local groups retain the original positioning conjugator. -/
theorem maximal_pure_extension_exceptional_control (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X) (hlarge : 4 < Nat.card X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    (∃ k : Model, normalizer (X : Set Model) =
      sourceSubgroup.map (MulAut.conj k).toMonoidHom) ∨
    ∃ g : localPairCentralizer,
      let Y := X.map (MulAut.conj (g.val : Model)).toMonoidHom
      nativePair ≤ Y ∧ Nat.card Y = 16 ∧ Y ≤ M ∧
      centralizer (Y : Set Model) ≤ M ∧
      (∀ y ∈ Y, y ≠ 1 → IsConj a y) ∧
      IsMaximalTwoLocal (normalizer (Y : Set Model)) ∧
      (Y.subgroupOf M).map starHom = pureBlock 0 ∧
      Y ⊓ embeddedKernel = nativePair ∧
      centralizer (Y : Set Model) ⊓ embeddedKernel = exceptionalSpace ∧
      Nat.card (centralizer (Y : Set Model)) = 256 ∧
      centralizer (Y : Set Model) = (centralizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)).toMonoidHom ∧
      normalizer (Y : Set Model) = (normalizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)).toMonoidHom := by
  rcases maximal_pure_extension_after_two_images X hpair hlarge hpure hmax with h | h
  · exact Or.inl h
  obtain ⟨g,hP,_,hM,hC,hp,hm,hfour,hpos,hct,hnt⟩ := h
  let Y := X.map (MulAut.conj (g.val : Model)).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  exact Or.inr ⟨g,hP,exceptional_four_card Y hP hp hpos hfour,hM,hC,hp,hm,
    pure_position_image_eq Y hP hp 0 hpos hfour,
    exceptional_four_kernel Y hP hp hpos hfour,
    exceptional_centralizer_kernel_eq Y hP hp hpos hfour,
    exceptional_centralizer_card Y hP hp hpos hfour,hct,hnt⟩

/-- Except at order sixteen, the whole normalizer of every proper pure
native-pair extension is an actual max2 conjugate. -/
theorem native_extension_maximal_of_card_ne_sixteen (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X) (hlarge : 4 < Nat.card X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) (hcard : Nat.card X ≠ 16) :
    ∃ k : Model, normalizer (X : Set Model) =
      sourceSubgroup.map (MulAut.conj k).toMonoidHom := by
  rcases maximal_pure_extension_after_two_images X hpair hlarge hpure hmax with h | h
  · exact h
  obtain ⟨g,hP,_,_,_,hp,_,hfour,hpos,_,_⟩ := h
  let Y := X.map (MulAut.conj (g.val : Model)).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hc := exceptional_four_card Y hP hp hpos hfour
  change Nat.card (X.map (MulAut.conj (g.val : Model)).toMonoidHom) = 16 at hc
  rw [card_map_of_injective (MulAut.conj (g.val : Model)).injective] at hc
  exact (hcard hc).elim

/-- The same conclusion for an arbitrary original embedding of the native
pair. Its original ambient conjugator is retained in the endpoint map. -/
theorem marked_extension_maximal_of_card_ne_sixteen (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (g : Model)
    (hpair : nativePair.map (MulAut.conj g).toMonoidHom ≤ X)
    (hlarge : 4 < Nat.card X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) (hcard : Nat.card X ≠ 16) :
    ∃ k : Model, normalizer (X : Set Model) =
      sourceSubgroup.map (MulAut.conj (g*k)).toMonoidHom := by
  let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hP : nativePair ≤ Y := by
    have h := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hpair
    rwa [map_conj_mul,inv_mul_cancel,map_conj_one] at h
  have hYcard : Nat.card Y = Nat.card X := card_map_of_injective (MulAut.conj g⁻¹).injective
  have hp : ∀ v ∈ Y, v ≠ 1 → IsConj a v := by
    rintro v ⟨w,hw,rfl⟩ hv
    exact (hpure w hw (fun he => hv (by rw [he,map_one]))).trans
      (isConj_iff.mpr ⟨g⁻¹,rfl⟩)
  have hn : normalizer (Y : Set Model) = (normalizer (X : Set Model)).map
      (MulAut.conj g⁻¹).toMonoidHom := (map_equiv_normalizer_eq X (MulAut.conj g⁻¹)).symm
  have hm : IsMaximalTwoLocal (normalizer (Y : Set Model)) := by
    rw [hn]
    exact isMaximalTwoLocal_map (MulAut.conj g⁻¹) hmax
  obtain ⟨k,hk⟩ := native_extension_maximal_of_card_ne_sixteen Y hP
    (hYcard.symm ▸ hlarge) hp hm (hYcard.symm ▸ hcard)
  refine ⟨k,?_⟩
  rw [hn] at hk
  have he := congrArg (fun A : Subgroup Model => A.map (MulAut.conj g).toMonoidHom) hk
  rwa [map_conj_mul,map_conj_mul,mul_inv_cancel,map_conj_one] at he

/-- The arbitrary-radical application of all non-sixteen native-pair
extensions, with the original normalizer and literal denominator maps. -/
theorem marked_extension_radical_of_card_ne_sixteen (P X : Subgroup Model)
    (hP : P.IsPRadical 2) [IsElementaryAbelian 2 X] (g : Model)
    (hpair : nativePair.map (MulAut.conj g).toMonoidHom ≤ X)
    (hlarge : 4 < Nat.card X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) (hcard : Nat.card X ≠ 16)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    ∃ k : Model, let L := sourceSubgroup.map (MulAut.conj (g*k)).toMonoidHom
      IsTwoLocal L ∧ normalizer (P : Set Model) ≤ L ∧ P ≤ L ∧
      (normalizer (P.subgroupOf L : Set L)).map L.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf L).IsPRadical 2 ∧
      (normalizer (P.subgroupOf L : Set L)).pCoreIn 2 = P.subgroupOf L ∧
      ((normalizer (P.subgroupOf L : Set L)).pCoreIn 2).map L.subtype = P := by
  obtain ⟨k,hk⟩ := marked_extension_maximal_of_card_ne_sixteen X g hpair hlarge hpure hmax hcard
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
