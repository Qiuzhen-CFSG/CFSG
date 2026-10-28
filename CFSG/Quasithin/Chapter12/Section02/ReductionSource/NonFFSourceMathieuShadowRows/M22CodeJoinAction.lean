module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeCentralizer
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeOuterCentralizer
public import Theory.GroupTheory.PGroup.NormalSupplementKernel
public import Theory.GroupTheory.PCoreSurjective
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodePointLocalCore
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# The full original LT action on the marked M22 design

The given whole-orbit embedding supplies the actual action of LT on the
design, with the same component map and the same central vector. Once the
selected block identifies the component kernel, the Sylow supplement shows
that the full kernel is exactly O₂(LT). The centralizer of the original
vector maps onto its inner hexad stabilizer and its product with T lies in
the full hexad stabilizer.

Source: Aschbacher--Smith 8.2.10--11, printed pp.721--722, refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

def sourceOrbit_m22_designAction
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation) : (L ⊔ (T : Subgroup G) : Subgroup G) →* m22DesignAut :=
  NormalizedShadowRows.pairDesignEquiv.toMonoidHom.comp (d.embedding.comp D.orbitHom)

omit [Finite G] in
theorem sourceOrbit_m22_designAction_component
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation) (l : L) :
    D.sourceOrbit_m22_designAction d (inclusion le_sup_left l) =
      M22ValueBound.Concrete.inclusion (d.componentEquiv (D.orbitComponentHom l)) := by
  change NormalizedShadowRows.pairDesignEquiv (d.embedding (D.orbitComponentHom l)) = _
  exact (congrArg NormalizedShadowRows.pairDesignEquiv
    (d.on_component (D.orbitComponentHom l))).trans
      (NormalizedShadowRows.pairDesignEquiv_inner (d.componentEquiv (D.orbitComponentHom l)))

/-- The selected-block component kernel determines the full original join kernel. -/
theorem sourceOrbit_m22_designAction_kernel
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (hker : D.orbitComponentHom.ker = pCore 2 L) :
    (D.sourceOrbit_m22_designAction d).ker = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
  let J := L ⊔ (T : Subgroup G)
  let K := L.subgroupOf J
  let P := (T : Subgroup G).subgroupOf J
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hfK : IsPGroup 2 (D.orbitHom.comp K.subtype).ker := by
    let j : (D.orbitHom.comp K.subtype).ker →* pCore 2 L := {
      toFun x := ⟨⟨x.val.val,x.val.property⟩,hker ▸ (show
        D.orbitComponentHom ⟨x.val.val,x.val.property⟩ = 1 from Subtype.ext x.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    apply pCore_isPGroup.of_injective j
    intro x y he
    exact Subtype.ext (Subtype.ext (Subtype.ext
      (congrArg (fun t : pCore 2 L => (t.val : G)) he)))
  have hf : IsPGroup 2 D.orbitHom.ker :=
    D.orbitHom.kernel_isPGroup_of_normal_supplement K P
      T.isPGroup'.comap_subtype (by
        rw [←subgroupOf_sup (show L ≤ J from le_sup_left)
          (show (T : Subgroup G) ≤ J from le_sup_right),subgroupOf_self]) hfK
  have hk := D.orbitHom.comap_pCore_of_ker_isPGroup D.orbitHom_surjective hf
  rw [D.orbit_twoCore_eq_bot h, MonoidHom.comap_bot] at hk
  rw [sourceOrbit_m22_designAction,
    MonoidHom.ker_comp_of_injective _ _ NormalizedShadowRows.pairDesignEquiv.injective,
    MonoidHom.ker_comp_of_injective _ _ d.injective]
  exact hk

omit [Finite G] in
/-- The full action retains the original whole-code coordinates. -/
theorem sourceOrbit_m22_pairAction_coordinates
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : Additive D.sourceOrbit) :
    let E := D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv
    let hJN : L ⊔ (T : Subgroup G) ≤ normalizer (D.sourceOrbit : Set G) :=
      sup_le D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes
    E (automizerRepresentation D.sourceOrbit
      (D.sourceOrbit.normalizerMonoidHom.rangeRestrict (inclusion hJN g)) v) =
      m22OuterCodeRepresentation (d.embedding (D.orbitHom g)) (E v) := by
  dsimp only
  let w := D.sourceOrbitCoordinates.symm v
  have hc : D.sourceOrbitCoordinates (D.orbitRepresentation (D.orbitHom g) w) =
      automizerRepresentation D.sourceOrbit
        (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
          (inclusion (sup_le D.sourceOrbit_component_normalizes
            D.sourceOrbit_weakClosure_setup.normalizes) g))
        (D.sourceOrbitCoordinates w) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (D.sourceOrbitCoordinates_apply (D.orbitRepresentation (D.orbitHom g) w)).trans
      (congrArg (fun x : G => (g : G) * x * (g : G)⁻¹)
        (D.sourceOrbitCoordinates_apply w).symm)
  have hw : D.sourceOrbitCoordinates w = v := D.sourceOrbitCoordinates.apply_symm_apply v
  rw [hw] at hc
  have he := LinearMap.congr_fun (d.equivalence.isIntertwining' (D.orbitHom g)) w
  exact (congrArg d.equivalence.toLinearEquiv
    ((congrArg D.sourceOrbitCoordinates.symm hc).symm.trans
      (D.sourceOrbitCoordinates.symm_apply_apply _))).trans he

omit [Finite G] in
/-- Preserving the original hexad is exactly centralizing its original vector. -/
theorem sourceOrbit_m22_designAction_mem_hexad_iff
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (z : D.sourceOrbit) {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hzB : (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
      (Additive.ofMul z) = m22HexadVector hB)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    D.sourceOrbit_m22_designAction d g ∈ MulAction.stabilizer m22DesignAut B ↔
      g.val ∈ centralizer ({(z : G)} : Set G) := by
  let E := D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv
  let hJN : L ⊔ (T : Subgroup G) ≤ normalizer (D.sourceOrbit : Set G) :=
    sup_le D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes
  let a := automizerRepresentation D.sourceOrbit
    (D.sourceOrbit.normalizerMonoidHom.rangeRestrict (inclusion hJN g))
  have he : E (a (Additive.ofMul z)) =
      m22OuterCodeRepresentation (d.embedding (D.orbitHom g)) (E (Additive.ofMul z)) :=
    D.sourceOrbit_m22_pairAction_coordinates d g (Additive.ofMul z)
  rw [show D.sourceOrbit_m22_designAction d g =
    NormalizedShadowRows.pairDesignEquiv (d.embedding (D.orbitHom g)) from rfl,
    ←NormalizedShadowRows.outer_code_hexad_vector_fixed_iff hB, ←hzB]
  constructor
  · intro hh
    have hv := congrArg (fun v : Additive D.sourceOrbit => (v.toMul : G))
      (E.injective (he.trans hh))
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hv)
  · intro hh
    have hv : a (Additive.ofMul z) = Additive.ofMul z := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change g.val*z.val*g.val⁻¹=z.val
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hh)
    exact he.symm.trans (congrArg E hv)

omit [Finite G] in
/-- The original component centralizer covers the full inner hexad stabilizer. -/
theorem sourceOrbit_m22_designAction_centralizer_image
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (z : D.sourceOrbit) {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hzB : (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
      (Additive.ofMul z) = m22HexadVector hB) :
    ((L ⊓ centralizer ({(z : G)} : Set G)).subgroupOf
      (L ⊔ (T : Subgroup G))).map (D.sourceOrbit_m22_designAction d) =
      (MulAction.stabilizer M22 B).map M22ValueBound.Concrete.inclusion := by
  let q := d.componentEquiv.toMonoidHom.comp D.orbitComponentHom
  have hq : Function.Surjective q := d.componentEquiv.surjective.comp D.orbitComponentHom_surjective
  ext y
  constructor
  · rintro ⟨g,hg,rfl⟩
    let l : L := ⟨g,hg.1⟩
    have he : D.sourceOrbit_m22_designAction d g =
        M22ValueBound.Concrete.inclusion (q l) := D.sourceOrbit_m22_designAction_component d l
    refine ⟨q l,?_,he.symm⟩
    change M22ValueBound.Concrete.inclusion (q l) ∈ MulAction.stabilizer m22DesignAut B
    rw [←he]
    exact (D.sourceOrbit_m22_designAction_mem_hexad_iff d z hB hzB g).mpr hg.2
  · rintro ⟨s,hs,rfl⟩
    obtain ⟨l,hl⟩ := hq s
    let g : (L ⊔ (T : Subgroup G) : Subgroup G) := inclusion le_sup_left l
    have he : D.sourceOrbit_m22_designAction d g = M22ValueBound.Concrete.inclusion s :=
      (D.sourceOrbit_m22_designAction_component d l).trans
        (congrArg M22ValueBound.Concrete.inclusion hl)
    refine ⟨g,⟨l.property,?_⟩,he⟩
    apply (D.sourceOrbit_m22_designAction_mem_hexad_iff d z hB hzB g).mp
    rw [he]
    exact hs

omit [Finite G] in
/-- The literal centralizer and original Sylow preserve the same marked hexad. -/
theorem sourceOrbit_m22_designAction_point_join
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G))
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hzB : (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
      (Additive.ofMul z) = m22HexadVector hB) :
    (((L ⊓ centralizer ({(z : G)} : Set G)) ⊔ (T : Subgroup G)).subgroupOf
      (L ⊔ (T : Subgroup G))).map (D.sourceOrbit_m22_designAction d) ≤
        MulAction.stabilizer m22DesignAut B := by
  have hC : (L ⊓ centralizer ({(z : G)} : Set G)) ⊔ (T : Subgroup G) ≤
      centralizer ({(z : G)} : Set G) :=
    sup_le inf_le_right (fun t ht => mem_centralizer_singleton_iff.mpr (hz t ht))
  rintro _ ⟨g,hg,rfl⟩
  exact (D.sourceOrbit_m22_designAction_mem_hexad_iff d z hB hzB g).mpr (hC hg)

/-- The complete original join action and actual central hexad, for the
point-local core product. Its sole kernel premise is supplied by 8.2.10. -/
theorem sourceOrbit_m22_code_join_action
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (hker : D.orbitComponentHom.ker = pCore 2 L)
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    ∃ B : Finset (Fin 22), ∃ hB : B ∈ m22Blocks,
      ∃ a : (L ⊔ (T : Subgroup G) : Subgroup G) →* m22DesignAut,
        (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
          (Additive.ofMul z) = m22HexadVector hB ∧
        a.ker = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) ∧
        (∀ l : L, a (inclusion le_sup_left l) =
          M22ValueBound.Concrete.inclusion (d.componentEquiv (D.orbitComponentHom l))) ∧
        ((L ⊓ centralizer ({(z : G)} : Set G)).subgroupOf
          (L ⊔ (T : Subgroup G))).map a =
          (MulAction.stabilizer M22 B).map M22ValueBound.Concrete.inclusion ∧
        (((L ⊓ centralizer ({(z : G)} : Set G)) ⊔ (T : Subgroup G)).subgroupOf
          (L ⊔ (T : Subgroup G))).map a ≤ MulAction.stabilizer m22DesignAut B := by
  have hex := @sourceOrbit_m22_code_central_hexad G _ _ T L V D d z hz hne
  rcases hex with ⟨B,hB,hzB⟩
  exact ⟨B,hB,D.sourceOrbit_m22_designAction d,hzB,
    D.sourceOrbit_m22_designAction_kernel h d hker,
    D.sourceOrbit_m22_designAction_component d,
    D.sourceOrbit_m22_designAction_centralizer_image d z hB hzB,
    D.sourceOrbit_m22_designAction_point_join d z hz hB hzB⟩

/-- The native inner and outer hexad core calculation gives the actual
point-local core product. The full-centralizer equality is independent of
the chosen whole-code coordinates. -/
theorem sourceOrbit_m22_code_point_local_core
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (hker : D.orbitComponentHom.ker = pCore 2 L)
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hRC : Chapter8.Section02.Centralizer.localResidual L z =
      L ⊓ centralizer ({(z : G)} : Set G)) :
    (Chapter8.Section02.Centralizer.localResidual L z ⊔ (T : Subgroup G)).pCoreIn 2 =
      Chapter8.Section02.Centralizer.localTwoCore L z ⊔
        (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨B,hB,a,_,hak,_,hR,hRT⟩ := D.sourceOrbit_m22_code_join_action h d hker z hz hne
  have hTR : (T : Subgroup G) ≤ normalizer
      (Chapter8.Section02.Centralizer.localResidual L z : Set G) := by
    rw [hRC]
    apply (le_inf D.sylow_normalizes_component ?_).trans inf_normalizer_le_normalizer_inf
    apply le_trans ?_ (centralizer ({(z : G)} : Set G)).le_normalizer
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hz t ht)
  apply Chapter8.Section02.MathieuShadowRows.m22_point_local_core_product L T z hTR hB a hak
  · simpa only [hRC] using hR
  · simpa only [hRC] using hRT

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
