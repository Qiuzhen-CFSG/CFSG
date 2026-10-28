module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.HexadCover.Design
public import Theory.GroupTheory.PCoreActionSplitting
public import Theory.GroupTheory.CentralCoprimeAbelianLift

/-!
# The two-core of the native outer hexad preimage

The full six-point kernel is a central extension of E₁₆ by the cubic
scalar group: it lies in the component, even though the whole hexad
stabilizer does not. This kernel is nilpotent. Its characteristic Sylow
two-subgroup is therefore normal in the full native preimage and maps
isomorphically onto the literal pointwise hexad kernel. The outer design
two-core calculation makes it exactly O₂. Factoring it out leaves a
surjection to S₆ with kernel of order three.

Source: Aschbacher--Smith 14.4.12, pp.1011--1012, and H.12.1(4), pp.393--394.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu
open scoped IsMulCommutative Pointwise
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.HexadCover
open M22ValueBound.Concrete

noncomputable def projection (b : Finset (Fin 22)) :
    hexadPreimage b →* MulAction.stabilizer m22DesignAut b :=
  localProjection (MulAction.stabilizer m22DesignAut b)

theorem projection_kernel (b : Finset (Fin 22)) :
    (projection b).ker = cubic.subgroupOf (hexadPreimage b) := localProjection_ker _

noncomputable def sixProjection {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    hexadPreimage b →* Equiv.Perm (Fin 6) := (M22OuterHexad.action hb).comp (projection b)

theorem sixProjection_surjective {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    Function.Surjective (sixProjection hb) :=
  (action_surjective hb).comp (localProjection_surjective _)

theorem projection_kernel_card (b : Finset (Fin 22)) :
    Nat.card (projection b).ker = 3 := by
  have hc : cubic ≤ hexadPreimage b := cubic_le_preimage _
  rw [projection_kernel, Nat.card_congr (subgroupOfEquivOfLe hc).toEquiv, cubic_card]

theorem outer_twoCore {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    pCore 2 (MulAction.stabilizer m22DesignAut b) = (M22OuterHexad.action hb).ker := by
  apply Subgroup.map_injective (MulAction.stabilizer m22DesignAut b).subtype_injective
  rw [M22OuterHexad.action_ker_map hb]
  exact M22OuterHexad.radical_eq hb _ (by
    rintro _ ⟨g, hg, rfl⟩
    exact hg) le_rfl

theorem twoCore_le_sixKernel {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    pCore 2 (hexadPreimage b) ≤ (sixProjection hb).ker := by
  have hn : ((pCore 2 (hexadPreimage b)).map (projection b)).Normal :=
    Normal.map inferInstance _ (localProjection_surjective _)
  have hm : (pCore 2 (hexadPreimage b)).map (projection b) ≤
      pCore 2 (MulAction.stabilizer m22DesignAut b) :=
    le_sSup ⟨hn, pCore_isPGroup.map _⟩
  rw [outer_twoCore hb] at hm
  exact map_le_iff_le_comap.mp hm

/-- The full six-point kernel is inside the genuine triple-cover component. -/
theorem sixKernel_le_component {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    (sixProjection hb).ker ≤ component.subgroupOf (hexadPreimage b) := by
  intro x hx
  have hi : projection b x ∈ (innerInclusion b).range :=
    action_kernel_le_inner hb hx
  obtain ⟨g, hg⟩ := hi
  have hm : designProjection x.val ∈ M22ValueBound.Concrete.inner := by
    change (projection b x).val ∈ M22ValueBound.Concrete.inner
    rw [← congrArg Subtype.val hg]
    exact g.val.property
  have hx' : x.val ∈ M22ValueBound.Concrete.inner.comap designProjection := hm
  rwa [component_preimage_designProjection] at hx'

noncomputable def kernelProjection {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    (sixProjection hb).ker →* (M22OuterHexad.action hb).ker :=
  (projection b).subgroupComap (M22OuterHexad.action hb).ker

theorem kernelProjection_surjective {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    Function.Surjective (kernelProjection hb) :=
  (projection b).subgroupComap_surjective_of_surjective _ (localProjection_surjective _)

theorem kernelProjection_central {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    (kernelProjection hb).ker ≤ center (sixProjection hb).ker := by
  intro x hx
  have hx' : x.val ∈ (projection b).ker :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rw [projection_kernel] at hx'
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (Subtype.ext
    (cubic_le_centralizer_component hx' y.val.val (sixKernel_le_component hb y.property)))

theorem sixKernel_nilpotent {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    Group.IsNilpotent (sixProjection hb).ker := by
  let := action_kernel_elementary hb
  exact Subgroup.isNilpotent_of_ker_le_center (kernelProjection hb) (kernelProjection_central hb)

/-- The actual design projection sends the native two-core onto the pointwise kernel. -/
theorem twoCore_map_projection {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    (pCore 2 (hexadPreimage b)).map (projection b) = (M22OuterHexad.action hb).ker := by
  let R := (sixProjection hb).ker
  let := sixKernel_nilpotent hb
  let P : Sylow 2 R := Sylow.nonempty.some
  have hP : (P : Subgroup R) ≤ pCore 2 R := le_sSup ⟨inferInstance, P.isPGroup'⟩
  have hkP : IsPGroup 2 (M22OuterHexad.action hb).ker :=
    IsPGroup.of_card (n := 4) (action_kernel_card hb)
  have hm : (P.mapSurjective (kernelProjection_surjective hb) : Subgroup (M22OuterHexad.action hb).ker) = ⊤ := by
    apply top_unique
    exact (hkP.to_subgroup ⊤).le_sylow_of_normal _
  change (P : Subgroup R).map (kernelProjection hb) = ⊤ at hm
  have hc : pCore 2 (hexadPreimage b) = R.pCoreIn 2 :=
    pCore_eq_map_of_normal_of_le 2 R (twoCore_le_sixKernel hb)
  apply le_antisymm (map_le_iff_le_comap.mpr (twoCore_le_sixKernel hb))
  intro y hy
  have ht : (⟨y, hy⟩ : (M22OuterHexad.action hb).ker) ∈
      (P : Subgroup R).map (kernelProjection hb) := hm ▸ mem_top _
  obtain ⟨x, hx, he⟩ := ht
  refine ⟨x.val, ?_, congrArg Subtype.val he⟩
  rw [hc]
  exact ⟨x, hP hx, rfl⟩

theorem twoCore_projection_injective (b : Finset (Fin 22)) :
    Function.Injective ((projection b).comp (pCore 2 (hexadPreimage b)).subtype) :=
  injective_comp_subtype_of_coprime_ker (projection b)
    (by rw [projection_kernel_card]; decide) _ pCore_isPGroup

/-- An actual marked isomorphism from O₂ to the pointwise design kernel. -/
noncomputable def twoCoreKernelEquiv {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    pCore 2 (hexadPreimage b) ≃* (M22OuterHexad.action hb).ker := by
  let f := (projection b).comp (pCore 2 (hexadPreimage b)).subtype
  have hf : f.range = (M22OuterHexad.action hb).ker := by
    change ((projection b).comp (pCore 2 (hexadPreimage b)).subtype).range = _
    rw [MonoidHom.range_comp, range_subtype]
    exact twoCore_map_projection hb
  exact (MonoidHom.ofInjective (twoCore_projection_injective b)).trans
    (MulEquiv.subgroupCongr hf)

theorem twoCore_card {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    Nat.card (pCore 2 (hexadPreimage b)) = 16 :=
  (Nat.card_congr (twoCoreKernelEquiv hb).toEquiv).trans (action_kernel_card hb)

theorem twoCore_elementary {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    IsElementaryAbelian 2 (pCore 2 (hexadPreimage b)) := by
  let he := action_kernel_elementary hb
  let e := twoCoreKernelEquiv hb
  refine { is_comm := ⟨fun x y => e.injective ?_⟩, exponent_dvd_p := ?_ }
  · simpa only [map_mul] using he.toIsMulCommutative.is_comm.comm (e x) (e y)
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply e.injective
    simpa only [map_pow, map_one] using
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp he.exponent_dvd_p (e x))

theorem twoCore_design_image {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    ((hexadPreimage b).pCoreIn 2).map designProjection =
      (m22HexadPointwiseKernel b).map inclusion := by
  have he := congrArg (map (MulAction.stabilizer m22DesignAut b).subtype)
    (twoCore_map_projection hb)
  rw [M22OuterHexad.action_ker_map hb] at he
  rw [map_map] at he
  have hc : (MulAction.stabilizer m22DesignAut b).subtype.comp (projection b) =
      designProjection.comp (hexadPreimage b).subtype := by ext x; rfl
  rw [hc] at he
  rw [pCoreIn, map_map]
  exact he

theorem sixKernel_eq_twoCore_sup_cubic {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    (sixProjection hb).ker = pCore 2 (hexadPreimage b) ⊔ (projection b).ker := by
  rw [sixProjection, ← MonoidHom.comap_ker, ← twoCore_map_projection hb, comap_map_eq]

noncomputable def quotientSixProjection {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    (hexadPreimage b ⧸ pCore 2 (hexadPreimage b)) →* Equiv.Perm (Fin 6) :=
  QuotientGroup.lift _ (sixProjection hb) (twoCore_le_sixKernel hb)

theorem quotientSixProjection_mk {b : Finset (Fin 22)} (hb : b ∈ m22Blocks)
    (x : hexadPreimage b) :
    quotientSixProjection hb (QuotientGroup.mk' _ x) = sixProjection hb x := rfl

theorem quotientSixProjection_surjective {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    Function.Surjective (quotientSixProjection hb) :=
  QuotientGroup.lift_surjective_of_surjective _ _ (sixProjection_surjective hb) _

theorem quotientSixProjection_kernel {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    (quotientSixProjection hb).ker =
      (projection b).ker.map (QuotientGroup.mk' (pCore 2 (hexadPreimage b))) := by
  rw [quotientSixProjection, QuotientGroup.ker_lift, sixKernel_eq_twoCore_sup_cubic hb,
    Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]

theorem quotientSixProjection_kernel_card {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    Nat.card (quotientSixProjection hb).ker = 3 := by
  let q := QuotientGroup.mk' (pCore 2 (hexadPreimage b))
  have hd : Disjoint (pCore 2 (hexadPreimage b)) (projection b).ker :=
    IsPGroup.disjoint_of_ne 2 3 (by decide) _ _ pCore_isPGroup
      (IsPGroup.of_card (n := 1) (by simpa using projection_kernel_card b))
  have hi : Function.Injective (q.comp (projection b).ker.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hxQ : x.val ∈ pCore 2 (hexadPreimage b) :=
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hx)
    exact Subtype.ext (hd.le_bot ⟨hxQ, x.property⟩)
  rw [quotientSixProjection_kernel hb]
  have hi' : Function.Injective (q.subgroupMap (projection b).ker) := by
    intro x y h
    exact hi (congrArg Subtype.val h)
  exact (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap (projection b).ker)
    ⟨hi', q.subgroupMap_surjective _⟩).toEquiv).symm.trans (projection_kernel_card b)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.HexadCover
