module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceFour
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.Decomposition
public import Theory.Representation.PSL3Two.ParabolicFixedFree


/-!
# Center coefficients above distance four

The genuine earlier core-factor conclusions identify the entire commutator-core
center with the local elementary layer. Projection to its natural summand has
exactly the component-central kernel. Restriction through the literal component
embedding preserves both the quotient action and centralization by the intrinsic
two-core of the component.

These coefficient facts retain the fixed summand. They require no centrality of
that summand in the original overgroup.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5) and section 7;
Aschbacher--Smith C.1.34(4), printed pp.136--137.
-/

public noncomputable section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
  {h : Input κ L R} (t : InputSetup h)
  (common : CommonFacts t.reduction.radical t.source t.geometry)
  (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
local notation "r" => t.reduction.radical
local notation "a" => alpha r
include common earlier

theorem large_centerLayer_contains_center :
    (center (blockU L)).map (blockU L).subtype ≤ t.centerLayer := by
  rintro x ⟨u,hu,rfl⟩
  change t.componentEmbedding (u : L) ∈ Z r a
  exact DistanceEight.CoreFactors.Center.core_center_le_Z_of_earlier common earlier
    (mem_map_of_mem (core r a).subtype
      (centerCongr t.intrinsicCoreEquiv ⟨u,hu⟩).property)

noncomputable def largeCenterProjection : center (blockU L) →* Multiplicative (Fin 3 → ZMod 2) :=
  (t.layerProjection common).comp {
    toFun z := ⟨z.val,t.large_centerLayer_contains_center common earlier
      (mem_map_of_mem _ z.property)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }

theorem largeCenterProjection_surjective : Function.Surjective (t.largeCenterProjection common earlier) := by
  intro v
  let u := common.natural.equiv.symm v
  have hUC : U r a ≤ (center (core r a)).map (core r a).subtype :=
    le_sup_left.trans (earlier.factor_inclusions common).2.1
  obtain ⟨w,hw,he⟩ := hUC u.property
  let z := (centerCongr t.intrinsicCoreEquiv).symm ⟨w,hw⟩
  refine ⟨z,?_⟩
  have hz : t.componentEmbedding (z.val : L) = (u : FreeAmalgam r) := by
    have hh := congrArg (fun y : center (core r a) => ((y.val : core r a) : FreeAmalgam r))
      ((centerCongr t.intrinsicCoreEquiv).apply_symm_apply ⟨w,hw⟩)
    exact hh.trans he
  let := Z_elementary_of_positive r t.geometry a rfl (by
    change 0 < t.geometry.b r
    exact lt_trans (by decide) common.large_distance)
  have hp : t.centralProjection common
      ⟨t.componentEmbedding (z.val : L),
        t.large_centerLayer_contains_center common earlier (mem_map_of_mem _ z.property)⟩ = u := by
    change CommutativeComplementProjection.projection _ _ _ _ _ _ = u
    convert CommutativeComplementProjection.projection_product
      (Z r a) (U r a) (Z r a ⊓ centralizer (Ltilde r a : Set (FreeAmalgam r)))
      common.decomposition common.disjoint u 1 using 1
    congr 1
    apply Subtype.ext
    simpa only [CommutativeComplementProjection.product_val, coe_one, mul_one] using hz
  change common.natural.equiv (t.centralProjection common
    ⟨t.componentEmbedding (z.val : L),t.large_centerLayer_contains_center common earlier
      (mem_map_of_mem _ z.property)⟩) = v
  rw [hp,common.natural.equiv.apply_symm_apply]

theorem largeCenterProjection_eq_one_iff (z : center (blockU L)) :
    t.largeCenterProjection common earlier z = 1 ↔ (z.val : L) ∈ center L := by
  constructor
  · exact t.layerProjection_kernel_central common _
  · intro hz
    apply Multiplicative.toAdd.injective
    apply BinaryLinearThree.ParabolicFixedFree.natural_fixed_eq_zero
    intro g _
    obtain ⟨q,rfl⟩ := (h.quotientEquiv.trans common.natural.marking).surjective g
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    let zL : t.centerLayer := ⟨z.val,t.large_centerLayer_contains_center common earlier
      (mem_map_of_mem _ z.property)⟩
    have he := t.layerProjection_action common l zL
    have hz' : (⟨l * (zL : L) * l⁻¹,t.centerLayer_normal.conj_mem zL zL.property l⟩ : t.centerLayer) = zL := by
      apply Subtype.ext
      change l * (z.val : L) * l⁻¹ = (z.val : L)
      rw [mem_center_iff.mp hz l,mul_inv_cancel_right]
    rw [hz'] at he
    exact he.symm

theorem large_core_centralizes_center (l : L) (hl : l ∈ pCore 2 L)
    (z : center (blockU L)) : l * (z.val : L) * l⁻¹ = z.val := by
  apply t.componentEmbedding_injective
  rw [map_mul,map_mul,map_inv]
  have hz : t.componentEmbedding (z.val : L) ∈ Z r a :=
    t.large_centerLayer_contains_center common earlier (mem_map_of_mem _ z.property)
  let m : t.reduction.overgroup := inclusion (show L ≤ t.reduction.overgroup from le_sup_left) l
  have hlq : t.componentEmbedding l ∈ Q r a := by
    change m ∈ (Q r a).comap (embedM r)
    rw [t.Q_pullback, ← t.source.projection_kernel]
    change t.source.projection m = 1
    exact (t.projection_component l).trans
      ((congrArg h.quotientEquiv ((QuotientGroup.eq_one_iff l).mpr hl)).trans h.quotientEquiv.map_one)
  have hc := commutator_eq_bot_iff_le_centralizer.mp (t.geometry.centralizes a rfl) hz _ hlq
  rw [hc,mul_inv_cancel_right]

theorem largeCenterProjection_action (l : L) (x y : center (blockU L))
    (hy : (y.val : L) = l * (x.val : L) * l⁻¹) :
    (t.largeCenterProjection common earlier y).toAdd =
      Representation.specialLinearNatural 3
        (common.natural.marking (h.quotientEquiv (QuotientGroup.mk' _ l)))
          (t.largeCenterProjection common earlier x).toAdd := by
  have he := t.layerProjection_action common l
    ⟨x.val,t.large_centerLayer_contains_center common earlier (mem_map_of_mem _ x.property)⟩
  have hh : (⟨y.val,t.large_centerLayer_contains_center common earlier
      (mem_map_of_mem _ y.property)⟩ : t.centerLayer) =
      ⟨l * (x.val : L) * l⁻¹,t.centerLayer_normal.conj_mem _
        (t.large_centerLayer_contains_center common earlier (mem_map_of_mem _ x.property)) l⟩ :=
    Subtype.ext hy
  exact (congrArg (fun z : t.centerLayer => (t.layerProjection common z).toAdd) hh).trans he

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
