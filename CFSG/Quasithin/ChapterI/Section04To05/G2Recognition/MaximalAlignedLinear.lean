module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalLinearQuotient
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCompletion

/-!
# The two original endpoint quotient maps on their whole common middle

The left cubic normalizer acts on its core modulo its center. The same
construction for the opposite factor is transported by the original Sylow
aligner to the literal right endpoint. Both maps are onto GL₂(3), with
kernels exactly the original marked cores. The common order2916 Borel maps
on each side to the normalizer of the corresponding cubic Sylow image.

Restricting by both actual middle inclusions gives a joint linear action.
Its kernel is the common core of order81, and its image has order36. These
maps retain the original completion, generation and torus markings; they
identify the quotient portion of the endpoint comparison. Equivalences of
the full endpoints with the Atlas parabolics, compatible on the whole
middle, remain necessary for I.4.5.

Source: Aschbacher–Smith I.4.5, printed p.417, via the original marked
cubic normalizers. The literal application is Chapter14LinearQuotient.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace AlignedCubicPair
variable {t : CubicTorus c} (d : AlignedCubicPair t)

/-- The original left core, with no change of marking. -/
abbrev leftCore (_d : AlignedCubicPair t) : Subgroup G := cubicOddCore c t.x
/-- The original opposite core under the same aligner as the whole right endpoint. -/
abbrev rightCore : Subgroup G :=
  (cubicOddCore (swapFactors c) t.swap.x).map (MulAut.conj d.aligner).toMonoidHom

/-- The actual conjugation equivalence to the aligned right endpoint. -/
def rightEndpointEquiv : cubicNormalizer (swapFactors c) t.swap.x ≃* d.rightEndpoint :=
  (MulAut.conj d.aligner).subgroupMap _

noncomputable def leftLinearAction : d.leftEndpoint →*
    Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) := t.cubicLinearAction d.core_order

/-- The original opposite core retains its order under the factor marking. -/
theorem right_core_order (d : AlignedCubicPair t) : Nat.card (cubicOddCore (swapFactors c) t.swap.x)=243 :=
  t.oddCore_card_eq.symm.trans d.core_order

noncomputable def rightLinearAction : d.rightEndpoint →*
    Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  (t.swap.cubicLinearAction d.right_core_order).comp
    d.rightEndpointEquiv.symm.toMonoidHom

theorem leftLinearAction_surjective : Function.Surjective d.leftLinearAction :=
  t.cubicLinearAction_surjective d.core_order

theorem rightLinearAction_surjective : Function.Surjective d.rightLinearAction :=
  (t.swap.cubicLinearAction_surjective d.right_core_order).comp
    d.rightEndpointEquiv.symm.surjective

theorem leftLinearAction_kernel : d.leftLinearAction.ker=d.leftCore.subgroupOf d.leftEndpoint :=
  t.cubicLinearAction_kernel d.core_order

theorem rightLinearAction_kernel : d.rightLinearAction.ker=d.rightCore.subgroupOf d.rightEndpoint := by
  ext a
  change t.swap.cubicLinearAction d.right_core_order
    (d.rightEndpointEquiv.symm a)=1 ↔ (a:G)∈d.rightCore
  rw [←MonoidHom.mem_ker,t.swap.cubicLinearAction_kernel]
  change (MulAut.conj d.aligner).symm (a:G)∈cubicOddCore (swapFactors c) t.swap.x ↔
    (a:G)∈(cubicOddCore (swapFactors c) t.swap.x).map (MulAut.conj d.aligner).toMonoidHom
  exact mem_map_equiv.symm

omit [Finite G] in
private theorem right_transport (K : Subgroup G) :
    ((K.map (MulAut.conj d.aligner).toMonoidHom).subgroupOf d.rightEndpoint).map
      d.rightEndpointEquiv.symm.toMonoidHom=
        K.subgroupOf (cubicNormalizer (swapFactors c) t.swap.x) := by
  rw [map_equiv_eq_comap_symm']
  ext a
  change MulAut.conj d.aligner (a:G)∈K.map (MulAut.conj d.aligner).toMonoidHom ↔ (a:G)∈K
  exact mem_map_iff_mem (MulAut.conj d.aligner).injective

/-- The same original whole middle has the prescribed left linear Borel image. -/
theorem leftLinearAction_borel :
    (t.leftCubicBorel.subgroupOf d.leftEndpoint).map d.leftLinearAction=
      normalizer (((t.leftCoreExtension.subgroupOf d.leftEndpoint).map
        d.leftLinearAction):Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))) :=
  t.cubicLinearAction_borel_image d.core_order

/-- The aligned whole middle has the prescribed right linear Borel image. -/
theorem rightLinearAction_borel :
    (t.leftCubicBorel.subgroupOf d.rightEndpoint).map d.rightLinearAction=
      normalizer (((t.leftCoreExtension.subgroupOf d.rightEndpoint).map
        d.rightLinearAction):Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))) := by
  have hb := t.maximal_aligned_borels d.core_order d.aligner d.aligned
  simp only [rightLinearAction,←map_map]
  rw [←hb,d.right_transport,←d.aligned,d.right_transport]
  exact t.swap.cubicLinearAction_borel_image d.right_core_order

theorem rightLinearAction_sylow_image_card :
    Nat.card ((t.leftCoreExtension.subgroupOf d.rightEndpoint).map d.rightLinearAction)=3 := by
  simp only [rightLinearAction,←map_map]
  rw [←d.aligned,d.right_transport]
  exact t.swap.cubicLinearAction_sylow_image_card d.right_core_order

theorem rightLinearAction_borel_image_card :
    Nat.card ((t.leftCubicBorel.subgroupOf d.rightEndpoint).map d.rightLinearAction)=12 := by
  simp only [rightLinearAction,←map_map]
  rw [←t.maximal_aligned_borels d.core_order d.aligner d.aligned,d.right_transport]
  exact t.swap.cubicLinearAction_borel_image_card d.right_core_order

/-- Both quotient actions restricted by the literal inclusions of the whole middle. -/
noncomputable def middleLinearAction : t.leftCubicBorel →*
    (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) ×
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :=
  (d.leftLinearAction.comp (inclusion t.leftCubicBorel_le)).prod
    (d.rightLinearAction.comp (inclusion (d.overlap ▸ inf_le_right)))

/-- The two middle actions have exactly the original common core as kernel. -/
theorem middleLinearAction_kernel :
    d.middleLinearAction.ker=(d.leftCore⊓d.rightCore).subgroupOf t.leftCubicBorel := by
  ext a
  change (d.leftLinearAction (inclusion t.leftCubicBorel_le a),
    d.rightLinearAction (inclusion (d.overlap ▸ inf_le_right) a))=(1,1) ↔ _
  rw [Prod.mk.injEq,←MonoidHom.mem_ker,←MonoidHom.mem_ker,
    d.leftLinearAction_kernel,d.rightLinearAction_kernel]
  rfl

/-- The original middle quotient is the actual order36 joint linear image. -/
theorem middleLinearAction_range_card : Nat.card d.middleLinearAction.range=36 := by
  have hc := (t.maximal_aligned_core_pair d.core_order d.aligner d.aligned).2.1
  change Nat.card (d.leftCore⊓d.rightCore:Subgroup G)=81 at hc
  have hK : d.leftCore⊓d.rightCore≤t.leftCubicBorel :=
    inf_le_left.trans (le_sup_left.trans le_sup_left)
  have hh := d.middleLinearAction.ker.card_mul_index
  rw [index_ker] at hh
  rw [d.middleLinearAction_kernel,
    Nat.card_congr (subgroupOfEquivOfLe hK).toEquiv,hc,
    (t.maximal_leftCubicBorel_split d.core_order).2.2.2] at hh
  omega

end AlignedCubicPair
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
