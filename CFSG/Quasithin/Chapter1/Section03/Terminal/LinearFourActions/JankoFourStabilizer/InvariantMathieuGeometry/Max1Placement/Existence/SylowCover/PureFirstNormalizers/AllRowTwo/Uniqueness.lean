module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.Reduction

/-!
# Uniqueness of the native eight over a plane

A plane in a conjugate of the certified eight can be moved, inside that
conjugate's max4 normalizer, to its marked plane. The already proved full
plane-normalizer bound then forces the transporting element into max4.
Consequently two certified-eight conjugates containing one plane coincide.
This also controls the whole normalizer of a subgroup already contained in
such an eight, without assuming that any selected plane is invariant.

Source: Kleidman--Wilson (1988), Corollary 1.2.2(a), pp.488--489. This is
the uniqueness step only; existence for an arbitrary all-row-two group is
not a premise silently supplied by the four-group census.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo
open SymmetricLinear
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
attribute [local irreducible] modelGroup matrixA matrixB

private theorem map_conj_mul (A : Subgroup Model) (g k : Model) :
    (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*k)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem undo_conj (A : Subgroup Model) (g : Model) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [map_conj_mul,inv_mul_cancel]
  have he : (MulAut.conj (1 : Model)).toMonoidHom = MonoidHom.id Model := by ext x; simp
  rw [he,map_id]

/-- A conjugate of the certified eight containing the distinguished plane is
necessarily the original eight. -/
theorem eight_eq_of_plane_le (g : Model)
    (hP : max4Plane ≤ max4Eight.map (MulAut.conj g).toMonoidHom) :
    max4Eight.map (MulAut.conj g).toMonoidHom = max4Eight := by
  let Y := max4Plane.map (MulAut.conj g⁻¹).toMonoidHom
  have hY : Y ≤ max4Eight := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hP
    rwa [undo_conj] at hh
  have hc : Nat.card Y = 4 :=
    (card_map_of_injective (MulAut.conj g⁻¹).injective).trans max4Plane_card
  obtain ⟨k,hk⟩ := max4_eight_plane_transitive Y hY hc
  have he : max4Plane = max4Plane.map (MulAut.conj (g*(k : Model))).toMonoidHom := by
    have hh := congrArg (fun A : Subgroup Model => A.map (MulAut.conj g).toMonoidHom) hk
    change (max4Plane.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = _ at hh
    have hu := undo_conj max4Plane g⁻¹
    simp only [inv_inv] at hu
    rw [hu,map_conj_mul] at hh
    exact hh
  have hgk : g*(k : Model) ∈ max4Subgroup :=
    plane_normalizer_lt_max4.le (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hg : g ∈ max4Subgroup := by
    have hh := max4Subgroup.mul_mem hgk (max4Subgroup.inv_mem k.property)
    simpa using hh
  apply mem_normalizer_iff_map_conj_eq.mp
  rwa [max4_eight_normalizer_eq]

/-- Every plane contained in a certified-eight conjugate determines that
conjugate uniquely; no invariance of the plane is required. -/
theorem eight_unique_over_plane (Y : Subgroup Model) (hcard : Nat.card Y = 4)
    (g k : Model)
    (hg : Y ≤ max4Eight.map (MulAut.conj g).toMonoidHom)
    (hk : Y ≤ max4Eight.map (MulAut.conj k).toMonoidHom) :
    max4Eight.map (MulAut.conj g).toMonoidHom =
      max4Eight.map (MulAut.conj k).toMonoidHom := by
  let Z := Y.map (MulAut.conj g⁻¹).toMonoidHom
  have hZ : Z ≤ max4Eight := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hg
    rwa [undo_conj] at hh
  have hc : Nat.card Z = 4 :=
    (card_map_of_injective (MulAut.conj g⁻¹).injective).trans hcard
  obtain ⟨u,hu⟩ := max4_eight_plane_transitive Z hZ hc
  have hp : max4Plane ≤
      max4Eight.map (MulAut.conj ((u : Model)⁻¹*(g⁻¹*k))).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hk
    change Z ≤ _ at hh
    rw [hu,map_conj_mul] at hh
    have hi := map_mono (f := (MulAut.conj (u : Model)⁻¹).toMonoidHom) hh
    rwa [undo_conj,map_conj_mul] at hi
  have he := eight_eq_of_plane_le _ hp
  have hm := congrArg (fun A : Subgroup Model =>
    A.map (MulAut.conj (g*(u : Model))).toMonoidHom) he
  rw [map_conj_mul] at hm
  have hcj : (g*(u : Model))*((u : Model)⁻¹*(g⁻¹*k)) = k := by group
  rw [hcj] at hm
  have huN : max4Eight.map (MulAut.conj (u : Model)).toMonoidHom = max4Eight :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [max4_eight_normalizer_eq]; exact u.property)
  rw [← map_conj_mul,huN] at hm
  exact hm.symm

/-- Once the whole source group is in a certified-eight conjugate, its whole
normalizer preserves that eight, even if it moves every plane of the group. -/
theorem normalizer_le_of_eight_container
    (X Y : Subgroup Model) (hYX : Y ≤ X) (hcard : Nat.card Y = 4)
    (g : Model) (hX : X ≤ max4Eight.map (MulAut.conj g).toMonoidHom) :
    normalizer (X : Set Model) ≤ max4Subgroup.map (MulAut.conj g).toMonoidHom := by
  rw [← conjugate_eight_normalizer]
  intro n hn
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (max4Eight.map (MulAut.conj g).toMonoidHom).map
    (MulAut.conj n).toMonoidHom = _
  rw [map_conj_mul]
  have hnp : X ≤ max4Eight.map (MulAut.conj (n*g)).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj n).toMonoidHom) hX
    have hn' : X.map (MulAut.conj n).toMonoidHom = X :=
      mem_normalizer_iff_map_conj_eq.mp hn
    rw [hn',map_conj_mul] at hh
    exact hh
  exact eight_unique_over_plane Y hcard (n*g) g (hYX.trans hnp) (hYX.trans hX)

/-- Literal radical restriction after the source container is established.
The new uniqueness argument supplies the full normalizer containment. -/
theorem radical_restriction_of_eight_container
    (P X Y : Subgroup Model) (hP : P.IsPRadical 2)
    (hPX : normalizer (P : Set Model) ≤ normalizer (X : Set Model))
    (hYX : Y ≤ X) (hcard : Nat.card Y = 4)
    (g : Model) (hX : X ≤ max4Eight.map (MulAut.conj g).toMonoidHom) :
    let M := max4Subgroup.map (MulAut.conj g).toMonoidHom
    IsTwoLocal M ∧ normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype =
        normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P := by
  apply radical_max4_of_eight_witness P X
    (max4Eight.map (MulAut.conj g).toMonoidHom) g hP hPX _ rfl
  rw [conjugate_eight_normalizer]
  exact normalizer_le_of_eight_container X Y hYX hcard g hX

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo
