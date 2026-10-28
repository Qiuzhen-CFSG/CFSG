module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.SourceResidual
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.ActorFixedVector
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.Recognition
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.LayerClosureCharacteristic
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.LayerClosureSmallActor
/-!
# Excluding an A₅ actor in the original positive-center overcomponent

If the faithful actor on the normal closure W of the original A₅ layer is
A₅, equality of orders gives W=U(L). Normal generation also identifies W
with blockU(I), so normality of the overcomponent makes this layer invariant
under the actual centralizer. The solvable two-perfect point residual must
then fix the original Sylow-fixed vector, contradicting its marked movement.

The final consumer uses the literal original orthogonal action and point
residual. Its solvability follows from the already proved three-group
residual quotient of the original minimal parabolic. No solvability,
fixed-vector, or actor-recognition premise is added to the exclusion.

Source: Aschbacher–Smith 10.2.1, printed p.743.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open ChapterC Chapter3.Section02 FixedCenterOvercomponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
/-- An A₅ faithful actor forces every solvable two-perfect actor in the
actual ambient centralizer to fix the original full-Sylow fixed vector. -/
theorem source_a5_overcomponent_actor_five_fixes_original_vector
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {I X : Subgroup G} (hLI : L≤I) (hIX : I≤X)
    (hI : (I.subgroupOf X).IsCComponent)
    (hNI : X≤normalizer (I:Set G))
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G)) X)
    (hU : (blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype≤pCore 2 I)
    (ha : Nonempty ((I ⧸ centralizer
      (normalClosure ((blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype:Set I):Set I))
      ≃* alternatingGroup (Fin 5)))
    (Y : Subgroup G) [Group.IsSolvable Y] (hp : IsPPerfect 2 Y)
    (hYX : Y≤X)
    (hTY : (T:Subgroup G)⊓normalizer (L:Set G)≤normalizer (Y:Set G))
    {v : G} (hv : v∈(blockU L).map L.subtype)
    (hvT : v∈centralizer ((T:Subgroup G)⊓L:Set G)) :
    Y≤centralizer ({v}:Set G) := by
  let K := L.subgroupOf I
  let U := (blockU K).map K.subtype
  let W := normalClosure (U:Set I)
  let V := (blockU L).map L.subtype
  have hL := (source_a5_original_block_of_baumann_not_controlled D e hn hout).2.2
  have hK : IsAlternatingBlock K 5 := hL.of_mulEquiv (subgroupOfEquivOfLe hLI).symm
  obtain ⟨S,_,hSK⟩ := source_containing_component_sylow hLI hIX hI hS
  have hWU : W=U := hK.normalClosure_layer_eq_of_alternatingFive_actor K S hSK hU ha
  have hWB : W=blockU I := hK.normalClosure_layer_eq_blockU K S hSK hU
    (hK.normalClosure_eq_top_in_cComponent hIX hI)
  have hUm : U.map I.subtype=V := by
    let a := subgroupOfEquivOfLe hLI
    change ((blockU K).map K.subtype).map I.subtype=(blockU L).map L.subtype
    rw [←RankOne.Solvable.blockU_map_equiv a,map_map,map_map]
    rfl
  have hWm : W.map I.subtype=V := hWU ▸ hUm
  have hXV : X≤normalizer (V:Set G) := by
    rw [←hWm,hWB]
    exact hNI.trans (normalizer_le_normalizer_characteristic_image I (blockU I))
  have hLX : L≤X := hLI.trans hIX
  have hVX : V≤X := (map_subtype_le _).trans hLX
  let LX := L.subgroupOf X
  let IX := I.subgroupOf X
  let VX := V.subgroupOf X
  let RX := ((T:Subgroup G)⊓L).subgroupOf X
  let YX := Y.subgroupOf X
  let : IX.Normal := (normal_subgroupOf_iff_le_normalizer hIX).mpr hNI
  let : VX.Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  have hLXblock : IsAlternatingBlock LX 5 := hL.of_mulEquiv (subgroupOfEquivOfLe hLX).symm
  have hVXlayer : VX=(blockU LX).map LX.subtype := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hVX]
    let a := subgroupOfEquivOfLe hLX
    change (blockU L).map L.subtype=((blockU LX).map LX.subtype).map X.subtype
    rw [←RankOne.Solvable.blockU_map_equiv a,map_map,map_map]
    rfl
  have hWi (i:I) : (i:G)∈V ↔ i∈W := by
    rw [←hWm]
    constructor
    · rintro ⟨j,hj,he⟩
      exact (Subtype.ext he : j=i) ▸ hj
    · exact mem_map_of_mem I.subtype
  let a : IX ≃* I := subgroupOfEquivOfLe hIX
  have hc : (centralizer (VX.subgroupOf IX:Set IX)).map a.toMonoidHom =
      centralizer (W:Set I) := by
    ext i
    constructor
    · rintro ⟨j,hj,rfl⟩ z hz
      have hz' : a.symm z∈VX.subgroupOf IX := (hWi z).mpr hz
      change z*a j=a j*z
      simpa only [map_mul,a.apply_symm_apply] using congrArg a (hj (a.symm z) hz')
    · intro hi
      refine ⟨a.symm i,?_,a.apply_symm_apply i⟩
      intro z hz
      apply a.injective
      simpa only [map_mul,a.apply_symm_apply] using hi (a z) ((hWi (a z)).mp hz)
  obtain ⟨ea⟩ := ha
  have haX : Nonempty ((IX ⧸ centralizer (VX.subgroupOf IX:Set IX)) ≃* alternatingGroup (Fin 5)) :=
    ⟨(QuotientGroup.congr _ _ a hc).trans ea⟩
  have hR : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓L) L := by
    have hLH : L≤localJoin T L := (le_componentOrbit L T).trans le_sup_left
    have hcomp : (L.subgroupOf (localJoin T L)).IsCComponent := by
      change (L.subgroupOf (componentOrbit L (T:Subgroup G)⊔(T:Subgroup G))).IsCComponent
      rw [componentOrbit_sup]
      exact D.maximal.1.1
    exact Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
      ⟨T.subtype (show (T:Subgroup G)≤localJoin T L from le_sup_right),
        map_subgroupOf_eq_of_le le_sup_right⟩ hLH hcomp.subnormal
  have hRX : Chapter1.IsSylowIn 2 RX LX := by
    apply (Chapter1.IsSylowIn.map_iff X.subtype X.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le (inf_le_right.trans hLX),map_subgroupOf_eq_of_le hLX]
    exact hR
  let : Group.IsSolvable YX := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hYX).toMonoidHom) (subgroupOfEquivOfLe hYX).injective
  have hpX : IsPPerfect 2 YX := hp.of_surjective
    (subgroupOfEquivOfLe hYX).symm.toMonoidHom (subgroupOfEquivOfLe hYX).symm.surjective
  have hRYX : RX≤normalizer (YX:Set X) := by
    rw [←subgroupOf_normalizer_eq hYX]
    exact comap_mono ((inf_le_inf_left _ L.le_normalizer).trans hTY)
  have hfix := alternatingFive_actor_fixes_sylow_vector LX IX RX YX VX
    hLXblock (comap_mono hLI) hVXlayer haX hRX hpX hRYX
    (v:=⟨v,hVX hv⟩) hv (fun r hr => Subtype.ext (hvT r hr))
  intro y hy
  exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
    (mem_centralizer_singleton_iff.mp (hfix (show (⟨y,hYX hy⟩:X)∈YX from hy))))

private theorem parabolic_wreath_isSolvable
    {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    (f : H →* BinaryFourPlus.Wreath) (hf : Function.Surjective f) :
    Group.IsSolvable H := by
  let Q := H ⧸ pCore 2 H
  let : Group.IsNilpotent (pResidual 2 Q) :=
    (parabolic_wreath_residual_isThreeGroup S hP f hf).isNilpotent
  let : Group.IsNilpotent (Q ⧸ pResidual 2 Q) :=
    (isPGroup_quotient_pResidual 2).isNilpotent
  let : Group.IsSolvable Q :=
    (Group.isSolvable_iff_subgroup_quotient (pResidual 2 Q)).mpr ⟨inferInstance,inferInstance⟩
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 H)).mpr ⟨inferInstance,inferInstance⟩

/-- The prescribed original point residual excludes A₅ as the faithful
actor on the contained normal closure. All residual properties are derived
from the original H-star subgroup and its marked orthogonal action. -/
theorem source_a5_fixed_center_overcomponent_actor_not_five
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {H : Subgroup G} (hH : H∈Chapter3.HStar (T:Subgroup G) D.maximalLocal)
    (hHN : H≤normalizer (ChapterB.baumann (T:Subgroup G):Set G))
    (f : H →* BinaryFourPlus.Wreath) (hf : Function.Surjective f)
    (v₁ v₂ : G) (a b : BinaryFourPlus.Plane) (ha : a≠0) (hb : b≠0)
    (hfix₁ : ∀h:H,(BinaryFourPlus.wreathToIsometry (f h)).val (a,0)=(a,0) ↔
      (h:G)∈centralizer ({v₁}:Set G))
    (hfix₂ : ∀h:H,(BinaryFourPlus.wreathToIsometry (f h)).val (0,b)=(0,b) ↔
      (h:G)∈centralizer ({v₂}:Set G))
    (hv₁L : v₁∈(blockU L).map L.subtype)
    (hv₁T : v₁∈centralizer ((T:Subgroup G)⊓L:Set G))
    (hCT : (T:Subgroup G)⊓centralizer ({v₂}:Set G)=
      (T:Subgroup G)⊓normalizer (L:Set G))
    {I : Subgroup G} (hLI : L≤I) (hIX : I≤centralizer ({v₂}:Set G))
    (hI : (I.subgroupOf (centralizer ({v₂}:Set G))).IsCComponent)
    (hNI : centralizer ({v₂}:Set G)≤normalizer (I:Set G))
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G))
      (centralizer ({v₂}:Set G)))
    (hU : (blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype≤pCore 2 I) :
    ¬ Nonempty ((I ⧸ centralizer
      (normalClosure ((blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype:Set I):Set I))
      ≃* alternatingGroup (Fin 5)) := by
  intro hactor
  obtain ⟨hp,hYX,hTY,_,_,hmove⟩ := source_fixed_center_pointResidual_data
    D e hn hout hH hHN f hf v₁ v₂ a b ha hb hfix₁ hfix₂
  rw [hCT] at hTY
  let : Group.IsSolvable H := parabolic_wreath_isSolvable (T.subtype hH.1.1.2)
    (source_a5_HStar_minimal_parabolic D e hn H hH) f hf
  let : Group.IsSolvable (pointResidual H v₂) := Group.isSolvable_of_isSolvable_injective
    (f := inclusion ((pointResidual_le H v₂).trans inf_le_left))
    (inclusion_injective ((pointResidual_le H v₂).trans inf_le_left))
  exact hmove (source_a5_overcomponent_actor_five_fixes_original_vector
    D e hn hout hLI hIX hI hNI hS hU hactor (pointResidual H v₂) hp hYX hTY hv₁L hv₁T)
end CFSG.Quasithin.Chapter10
