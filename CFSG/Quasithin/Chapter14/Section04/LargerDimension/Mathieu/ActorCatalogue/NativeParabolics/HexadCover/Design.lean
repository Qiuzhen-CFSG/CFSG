module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.DesignProjection
public import Theory.Mathieu.M22.Properties.OuterHexadRadical
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PartitionStructure.Restriction

/-!
# The labelled outer hexad action

The full design stabilizer has order 11520 and acts as S₆ on the hexad.
Its pointwise kernel is the included elementary abelian inner kernel of
order sixteen. The inverse image of A₆ is exactly the inner stabilizer.
These are the design-level maps used to retain the cubic layer of the
native cover in Aschbacher--Smith 14.4.12, printed pp.1011--1012.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.HexadCover
open M22ValueBound.Concrete

noncomputable def innerInclusion (b : Finset (Fin 22)) :
    MulAction.stabilizer M22 b →* MulAction.stabilizer m22DesignAut b where
  toFun g := ⟨inclusion g.val, g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem innerInclusion_injective (b : Finset (Fin 22)) :
    Function.Injective (innerInclusion b) := by
  intro x y h
  exact Subtype.ext (inclusion_injective (congrArg Subtype.val h))

theorem action_inner {b : Finset (Fin 22)} (hb : b ∈ m22Blocks)
    (g : MulAction.stabilizer M22 b) :
    M22OuterHexad.action hb (innerInclusion b g) = m22HexadAction hb g := rfl

theorem outer_stabilizer_card {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    Nat.card (MulAction.stabilizer m22DesignAut b) = 11520 := by
  obtain ⟨g, hg⟩ := exists_smul_m22Hexad123_eq hb
  have he : inclusion g • m22Hexad123 = b := hg
  rw [← Nat.card_congr (MulAction.stabilizerEquivStabilizer he.symm).toEquiv]
  have ho : PartitionStructure.oddElement ∈
      MulAction.stabilizer m22DesignAut m22Hexad123 := by
    change m22OddPairSwap • m22Hexad123 = m22Hexad123
    decide +kernel
  rw [PartitionStructure.outer_card_double _ ho]
  change Nat.card (MulAction.stabilizer M22 m22Hexad123) * 2 = 11520
  rw [m22Hexad_stabilizer_card m22Hexad123_mem]

theorem action_kernel_card {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    Nat.card (M22OuterHexad.action hb).ker = 16 := by
  rw [← card_map_of_injective (MulAction.stabilizer m22DesignAut b).subtype_injective,
    M22OuterHexad.action_ker_map hb, card_map_of_injective inclusion_injective,
    m22HexadPointwiseKernel_card hb]

theorem action_kernel_elementary {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    IsElementaryAbelian 2 (M22OuterHexad.action hb).ker := by
  let := m22HexadPointwiseKernel_elementaryAbelian hb
  let : IsElementaryAbelian 2 ((m22HexadPointwiseKernel b).map inclusion) :=
    IsElementaryAbelian.map inclusion
  have he := ((M22OuterHexad.action hb).ker.equivMapOfInjective _
    (MulAction.stabilizer m22DesignAut b).subtype_injective).trans
      (MulEquiv.subgroupCongr (M22OuterHexad.action_ker_map hb))
  refine { is_comm := ⟨fun x y => he.injective ?_⟩, exponent_dvd_p := ?_ }
  · simp only [map_mul]
    exact mul_comm' _ _
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply he.injective
    simpa only [map_pow, map_one] using
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 _) (he x))

theorem action_surjective {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    Function.Surjective (M22OuterHexad.action hb) := by
  apply MonoidHom.range_eq_top.mp
  apply eq_top_of_card_eq
  have hc := (M22OuterHexad.action hb).ker.card_mul_index
  rw [action_kernel_card hb, index_ker, outer_stabilizer_card hb] at hc
  have hp : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  rw [hp]
  omega

theorem action_inner_range {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    (innerInclusion b).range.map (M22OuterHexad.action hb) = alternatingGroup (Fin 6) := by
  rw [← MonoidHom.range_comp]
  exact m22HexadAction_range hb

theorem action_kernel_le_inner {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    (M22OuterHexad.action hb).ker ≤ (innerInclusion b).range := by
  intro g hg
  have hm : g.val ∈ (m22HexadPointwiseKernel b).map inclusion := by
    rw [← M22OuterHexad.action_ker_map hb]
    exact ⟨g, hg, rfl⟩
  obtain ⟨x, hx, he⟩ := hm
  exact ⟨⟨x, m22HexadPointwiseKernel_le b hx⟩, Subtype.ext he⟩

theorem action_alternating_preimage {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    (alternatingGroup (Fin 6)).comap (M22OuterHexad.action hb) =
      (innerInclusion b).range := by
  rw [← action_inner_range hb, comap_map_eq, sup_eq_left.mpr (action_kernel_le_inner hb)]

theorem action_even_iff_inner {b : Finset (Fin 22)} (hb : b ∈ m22Blocks)
    (g : MulAction.stabilizer m22DesignAut b) :
    M22OuterHexad.action hb g ∈ alternatingGroup (Fin 6) ↔ g.val ∈ M22ValueBound.Concrete.inner := by
  change g ∈ (alternatingGroup (Fin 6)).comap (M22OuterHexad.action hb) ↔ _
  rw [action_alternating_preimage hb]
  constructor
  · rintro ⟨x, rfl⟩
    exact x.val.property
  · intro h
    exact ⟨⟨⟨g.val.val, h⟩, g.property⟩, rfl⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.HexadCover
