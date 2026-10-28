module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.SixPointModel.Quotients
public import Theory.GroupTheory.PCoreSurjective

/-!
# Intrinsic hexad kernels in the native M22 pair groups

The pointwise kernel of the source octad fixes the deleted pair {0,9}.
Its preimages in native M22 and in the setwise pair stabilizer are therefore
isomorphic to that elementary group of order sixteen. The literal six-point
actions have images A6 and S6, whose two-cores are trivial. Their kernels
are consequently precisely the intrinsic two-cores of the hexad stabilizers.
This proves both kernel-image equalities required by the later cocode transfers.

The quotient equivalences retain the six actual coordinates and their quotient
maps. The equality between the inner and outer cores uses the original M22
embedding. All normality is relative to the respective hexad stabilizer.
The natural conjugation-module identification and compatible Sylow catalogue
are separate obligations; neither follows from the quotient orders alone.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
H.14.3(3) and the sketch following it, printed p.397 (PDF p.408).
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise
namespace Sporadic.Mathieu.M22ChapterH.Hexad
open MathieuCode MathieuCode.Hexad.CocodeAction.SixPointModel
noncomputable section

private theorem pointwise_elementary : IsElementaryAbelian 2 (octadPointwiseKernel O) := by
  rw [← octad_core_map_eq_pointwise]
  let := (LinearFourCore.octad_core_structure O).2
  exact IsElementaryAbelian.map_subtype

private theorem pointwise_card : Nat.card (octadPointwiseKernel O) = 16 := by
  rw [octadPointwiseKernel, Subgroup.card_map_of_injective (octadStabilizer O).subtype_injective,
    ← CocodeOctad.coordinateAction_ker_eq]
  exact CocodeOctad.card_coordinateKernel O

private theorem pointwise_le_inner : octadPointwiseKernel O ≤ m22Embedding.range := by
  intro g hg
  rw [m22Embedding_range]
  have hf := (mem_octadPointwiseKernel O g).mp hg
  exact ⟨hf 0 (by decide +kernel), hf 9 (by decide +kernel)⟩

private theorem pointwise_le_outer : octadPointwiseKernel O ≤ m22PairStabilizer := by
  intro g hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro i hi
  rw [(mem_octadPointwiseKernel O g).mp hg i (m22Pair_le_sourceOctad hi)]
  exact hi

private theorem coordinateKernel_isPGroup {G : Type*} [Group G]
    (f : G →* m22PairStabilizer) (hf : Function.Injective f)
    (hr : octadPointwiseKernel O ≤ (m22PairStabilizer.subtype.comp f).range) :
    IsPGroup 2 (coordinateAction f).ker := by
  let e := m22PairStabilizer.subtype.comp f
  have he : Function.Injective e := Subtype.val_injective.comp hf
  have hm : ((octadPointwiseKernel O).comap e).map e = octadPointwiseKernel O :=
    Subgroup.map_comap_eq_self hr
  rw [coordinateAction_ker hf hm]
  let := pointwise_elementary
  exact ((IsElementaryAbelian.isPGroup 2 (octadPointwiseKernel O)).comap_of_injective
    e he).comap_subtype

private theorem alternating_not_two : ¬ IsPGroup 2 (alternatingGroup H) := by
  let : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [Nat.card_eq_fintype_card, card_H]; decide)
  intro hp
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hc : Nat.card (alternatingGroup H) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, card_H]
    decide
  have hd : 3 ∣ 2 ^ n := hn ▸ hc.symm ▸ (by decide : 3 ∣ 360)
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

private theorem alternating_twoCore : pCore 2 (alternatingGroup H) = ⊥ := by
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top
      (by rw [Nat.card_eq_fintype_card, card_H]; decide : 5 ≤ Nat.card H)
      (N := pCore 2 (alternatingGroup H)) with h | h
  · exact h
  · have hp := pCore_isPGroup (p := 2) (G := alternatingGroup H)
    rw [h] at hp
    exact (alternating_not_two (hp.of_equiv Subgroup.topEquiv)).elim

private theorem symmetric_twoCore : pCore 2 (Equiv.Perm H) = ⊥ := by
  by_contra h
  have hn : Nontrivial (pCore 2 (Equiv.Perm H)) := (Subgroup.nontrivial_iff_ne_bot _).mpr h
  have hle := Equiv.Perm.alternatingGroup_le_of_normal
    (by rw [Nat.card_eq_fintype_card, card_H]; decide : 5 ≤ Nat.card H) hn
  exact alternating_not_two (pCore_isPGroup.to_le hle)

private def innerAction : m22InnerHexadStabilizer O →* alternatingGroup H :=
  innerCoordinateAction.codRestrict _ (fun g =>
    innerCoordinateAction_range ▸ (show innerCoordinateAction g ∈ innerCoordinateAction.range
      from ⟨g, rfl⟩))

private theorem innerAction_surjective : Function.Surjective innerAction := by
  intro s
  have hs : s.val ∈ innerCoordinateAction.range := innerCoordinateAction_range.symm ▸ s.property
  obtain ⟨g, hg⟩ := hs
  exact ⟨g, Subtype.ext hg⟩

/-- The literal inner coordinate kernel is the intrinsic hexad two-core. -/
theorem inner_kernel_eq_core :
    innerCoordinateAction.ker = pCore 2 (m22InnerHexadStabilizer O) := by
  have hp : IsPGroup 2 innerCoordinateAction.ker :=
    coordinateKernel_isPGroup m22ToPairStabilizer
      (fun _ _ h => m22Embedding_injective (congrArg Subtype.val h)) pointwise_le_inner
  have hk : innerAction.ker = innerCoordinateAction.ker := by
    ext g
    exact Subtype.ext_iff
  have he := innerAction.comap_pCore_of_ker_isPGroup innerAction_surjective (hk ▸ hp)
  rw [alternating_twoCore] at he
  exact hk.symm.trans he

/-- The literal outer coordinate kernel is the intrinsic hexad two-core. -/
theorem outer_kernel_eq_core :
    outerCoordinateAction.ker = pCore 2 (m22OuterHexadStabilizer O) := by
  have hp : IsPGroup 2 outerCoordinateAction.ker :=
    coordinateKernel_isPGroup (MonoidHom.id _) Function.injective_id (by
      simpa only [MonoidHom.comp_id, Subgroup.range_subtype] using pointwise_le_outer)
  have he := outerCoordinateAction.comap_pCore_of_ker_isPGroup
    (MonoidHom.range_eq_top.mp outerCoordinateAction_range) hp
  rw [symmetric_twoCore] at he
  exact he

private theorem mapped_coordinateKernel {G : Type*} [Group G]
    (f : G →* m22PairStabilizer) (hf : Function.Injective f)
    (hr : octadPointwiseKernel O ≤ (m22PairStabilizer.subtype.comp f).range) :
    ((coordinateAction f).ker.map (Stabilizer f).subtype).map
      (m22PairStabilizer.subtype.comp f) = octadPointwiseKernel O := by
  let e := m22PairStabilizer.subtype.comp f
  have hm : ((octadPointwiseKernel O).comap e).map e = octadPointwiseKernel O :=
    Subgroup.map_comap_eq_self hr
  rw [coordinateAction_ker hf hm, Subgroup.map_subgroupOf_eq_of_le]
  · exact hm
  · intro g hg
    apply MulAction.mem_stabilizer_finset'.mpr
    intro i hi
    rw [(mem_octadPointwiseKernel O (e g)).mp hg i hi]
    exact hi

/-- The earlier H.14 kernel comparison required by the native inner cocode transfer. -/
theorem inner_kernel_image :
    (m22InnerHexadKernel O).map m22Embedding = octadPointwiseKernel O := by
  unfold m22InnerHexadKernel
  rw [← inner_kernel_eq_core]
  exact mapped_coordinateKernel m22ToPairStabilizer
    (fun _ _ h => m22Embedding_injective (congrArg Subtype.val h)) pointwise_le_inner

/-- The same comparison in the actual setwise pair stabilizer. -/
theorem outer_kernel_image :
    (m22OuterHexadKernel O).map m22PairStabilizer.subtype = octadPointwiseKernel O := by
  unfold m22OuterHexadKernel
  rw [← outer_kernel_eq_core]
  exact mapped_coordinateKernel (MonoidHom.id _) Function.injective_id (by
    simpa only [MonoidHom.comp_id, Subgroup.range_subtype] using pointwise_le_outer)

/-- The kernel equivalence induced by the actual M22 embedding. -/
def innerKernelOctadEquiv : m22InnerHexadKernel O ≃* octadPointwiseKernel O :=
  ((m22InnerHexadKernel O).equivMapOfInjective m22Embedding m22Embedding_injective).trans
    (MulEquiv.subgroupCongr inner_kernel_image)

/-- The kernel equivalence induced by inclusion of the pair group in M24. -/
def outerKernelOctadEquiv : m22OuterHexadKernel O ≃* octadPointwiseKernel O :=
  ((m22OuterHexadKernel O).equivMapOfInjective m22PairStabilizer.subtype
    m22PairStabilizer.subtype_injective).trans (MulEquiv.subgroupCongr outer_kernel_image)

@[simp] theorem innerKernelOctadEquiv_coe (x : m22InnerHexadKernel O) :
    (innerKernelOctadEquiv x).val = m22Embedding x.val := rfl

@[simp] theorem outerKernelOctadEquiv_coe (x : m22OuterHexadKernel O) :
    (outerKernelOctadEquiv x).val = x.val.val := rfl

private theorem elementary_of_equiv {G : Type*} [Group G]
    (e : G ≃* octadPointwiseKernel O) : IsElementaryAbelian 2 G := by
  let he := pointwise_elementary
  refine { is_comm := ⟨fun x y => e.injective ?_⟩, exponent_dvd_p := ?_ }
  · simpa only [map_mul] using he.toIsMulCommutative.is_comm.comm (e x) (e y)
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply e.injective
    simpa only [map_pow, map_one] using
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp he.exponent_dvd_p (e x))

theorem inner_kernel_elementary : IsElementaryAbelian 2 (m22InnerHexadKernel O) :=
  elementary_of_equiv innerKernelOctadEquiv

theorem outer_kernel_elementary : IsElementaryAbelian 2 (m22OuterHexadKernel O) :=
  elementary_of_equiv outerKernelOctadEquiv

theorem inner_kernel_card : Nat.card (m22InnerHexadKernel O) = 16 :=
  (Nat.card_congr innerKernelOctadEquiv.toEquiv).trans pointwise_card

theorem outer_kernel_card : Nat.card (m22OuterHexadKernel O) = 16 :=
  (Nat.card_congr outerKernelOctadEquiv.toEquiv).trans pointwise_card

/-- Passing from M22 to its pair overgroup does not enlarge the hexad two-core. -/
theorem inner_kernel_map_pair :
    (m22InnerHexadKernel O).map m22ToPairStabilizer = m22OuterHexadKernel O := by
  apply Subgroup.map_injective m22PairStabilizer.subtype_injective
  rw [Subgroup.map_map, outer_kernel_image]
  exact inner_kernel_image

/-- The intrinsic inner quotient acts as A6 on the actual six remaining coordinates. -/
def innerQuotientEquiv :
    (m22InnerHexadStabilizer O ⧸ pCore 2 (m22InnerHexadStabilizer O)) ≃* alternatingGroup H :=
  innerIntrinsicQuotientAlternatingEquiv inner_kernel_image

/-- The intrinsic outer quotient acts as S6 on those same coordinates. -/
def outerQuotientEquiv :
    (m22OuterHexadStabilizer O ⧸ pCore 2 (m22OuterHexadStabilizer O)) ≃* Equiv.Perm H :=
  outerIntrinsicQuotientSymmetricEquiv outer_kernel_image

@[simp] theorem innerQuotientEquiv_mk (g : m22InnerHexadStabilizer O) :
    (innerQuotientEquiv (QuotientGroup.mk g) : Equiv.Perm H) = innerCoordinateAction g :=
  innerIntrinsicQuotientAlternatingEquiv_mk inner_kernel_image g

@[simp] theorem outerQuotientEquiv_mk (g : m22OuterHexadStabilizer O) :
    outerQuotientEquiv (QuotientGroup.mk g) = outerCoordinateAction g :=
  outerIntrinsicQuotientSymmetricEquiv_mk outer_kernel_image g

end
end Sporadic.Mathieu.M22ChapterH.Hexad
