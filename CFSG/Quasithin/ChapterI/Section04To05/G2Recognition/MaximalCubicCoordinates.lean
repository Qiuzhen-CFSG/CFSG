module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCoreNonquadratic
public import Theory.SpecificGroups.G2.TernaryRootCoordinates

/-!
# Cubic-equivariant coordinates on the original core abelianization

An element of the aligned opposite core outside the first core has a
nonquadratic action on the original elementary abelianization of order81.
The length-three Jordan construction identifies this actual automorphism
with the short or long Atlas root action. Its square image is the original
opposite derived line, and the coordinates place that line on the correct
literal root coordinate.

The whole abelianization action factors through the original GL₂(3) quotient.
An inner change of that marking places the chosen cubic at the specified
Atlas root generator, constructing the first generator equation in the
full-action comparison. The actual opposite actor is retained as an equality
of automorphisms. Neither form preservation nor the Weyl generator equation
is asserted for these coordinates. Both and whole-middle compatibility remain
necessary for the endpoint maps in Aschbacher–Smith I.4.5, printed p.417.
The literal source consumer is Chapter14CubicCoordinates.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus
variable (t : CubicTorus c)

/-- The whole Levi action on the literal abelianization, using its original GL₂ marking. -/
noncomputable def cubicGLAbelianizationAction (hc : Nat.card (cubicOddCore c t.x)=243) :
    Atlas.G2.TernaryLevi.GL23 →* MulAut (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :=
  t.cubicAbelianizationAction.comp ((inclusion t.cubicLevi_le_normalizer).comp
    (t.cubicLeviLinearEquiv hc).symm.toMonoidHom)

/-- The full quotient action factors through the already marked endpoint quotient. -/
theorem cubicAbelianizationAction_factor (hc : Nat.card (cubicOddCore c t.x)=243)
    (a : cubicNormalizer c t.x) :
    t.cubicAbelianizationAction a=t.cubicGLAbelianizationAction hc (t.cubicLinearAction hc a) := by
  let b := inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm
    (t.cubicLinearAction hc a))
  have hb : t.cubicLinearAction hc b=t.cubicLinearAction hc a :=
    (t.cubicLeviLinearEquiv hc).apply_symm_apply _
  have hk : a*b⁻¹∈(t.cubicLinearAction hc).ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv,hb,mul_inv_cancel]
  rw [t.cubicLinearAction_kernel hc,←t.cubicAbelianizationAction_kernel hc,
    MonoidHom.mem_ker,map_mul,map_inv,mul_inv_eq_one] at hk
  exact hk

end CubicTorus
namespace AlignedCubicPair
variable {t : CubicTorus c} (p : AlignedCubicPair t)

private theorem right_core_le_middle : p.rightCore≤t.leftCubicBorel := by
  rw [←t.maximal_aligned_borels p.core_order p.aligner p.aligned]
  exact map_mono (le_sup_left.trans le_sup_left)

/-- The literal opposite-core actor on the left four-dimensional abelianization. -/
@[expose] def oppositeAbelianizationActor (r : p.rightCore) :
    MulAut (p.leftCore ⧸ cubicCoreLine c t.x) :=
  t.cubicAbelianizationAction ⟨r,by exact t.leftCubicBorel_le (p.right_core_le_middle r.property)⟩

/-- Its displacement is the previously constructed map with the opposite derived-line image. -/
theorem oppositeAbelianizationActor_displacement (r : p.rightCore)
    (v : p.leftCore ⧸ cubicCoreLine c t.x) :
    p.oppositeDisplacement r v=p.oppositeAbelianizationActor r v*v⁻¹ := rfl

private theorem opposite_core_cube (r : p.rightCore) : (r:G)^3=1 := by
  obtain ⟨w,hw,he⟩ := r.property
  rw [←he,←map_pow]
  have hh := congrArg Subtype.val (t.swap.left_oddCore_cube ⟨w,hw⟩)
  change w^3=1 at hh
  rw [hh,map_one]

/-- Every actor used here is an actual cubic element of the opposite original core. -/
theorem oppositeAbelianizationActor_cube (r : p.rightCore) :
    p.oppositeAbelianizationActor r ^ 3=1 := by
  change (t.cubicAbelianizationAction
    ⟨r,t.leftCubicBorel_le (p.right_core_le_middle r.property)⟩)^3=1
  rw [←map_pow,show (⟨(r:G),t.leftCubicBorel_le (p.right_core_le_middle r.property)⟩:
    cubicNormalizer c t.x)^3=1 from Subtype.ext (p.opposite_core_cube r),map_one]

/-- Coordinates identifying the actual opposite cubic with the Atlas short-root action. -/
theorem exists_oppositeShortCoordinates (r : p.rightCore) (hr : (r:G)∉p.leftCore) :
    ∃ e : (p.leftCore ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V,
      (∀ v,e (p.oppositeAbelianizationActor r v)=Atlas.G2.TernaryCore.shortRoot (e v)) ∧
      (∀ v,v∈(⁅p.rightCore,p.rightCore⁆.subgroupOf p.leftCore).map
        (QuotientGroup.mk' (cubicCoreLine c t.x)) ↔
          (e v).toAdd 0=0 ∧ (e v).toAdd 2=0 ∧ (e v).toAdd 3=0) := by
  let := t.left_oddCore_quotient_elementary
  have hn : ∃ v,p.oppositeAbelianizationActor r
      (p.oppositeAbelianizationActor r v*v⁻¹)*
        (p.oppositeAbelianizationActor r v*v⁻¹)⁻¹≠1 := by
    by_contra h
    push Not at h
    apply p.oppositeDisplacement_square_ne_one r hr
    apply MonoidHom.ext
    exact h
  obtain ⟨e,he⟩ := Atlas.G2.TernaryCore.exists_shortRoot_coordinates
    (p.oppositeAbelianizationActor r) (p.oppositeAbelianizationActor_cube r)
    (t.maximal_core_abelianization_card p.core_order) hn
  have hdouble (v) : e (p.oppositeDisplacement r (p.oppositeDisplacement r v))=
      Multiplicative.ofAdd ![0,-(e v).toAdd 3,0,0] := by
    rw [p.oppositeAbelianizationActor_displacement,map_mul,map_inv,he,
      p.oppositeAbelianizationActor_displacement,map_mul,map_inv,he]
    exact Atlas.G2.TernaryCore.shortRoot_double (e v)
  refine ⟨e,he,?_⟩
  intro v
  rw [←p.oppositeDisplacement_square_range r hr]
  constructor
  · rintro ⟨w,rfl⟩
    change (e (p.oppositeDisplacement r (p.oppositeDisplacement r w))).toAdd 0=0 ∧ _
    simp only [MonoidHom.comp_apply,hdouble]
    simp
  · rintro ⟨h0,h2,h3⟩
    let w := e.symm (Multiplicative.ofAdd ![0,0,0,-(e v).toAdd 1])
    refine ⟨w,e.injective ?_⟩
    change e (p.oppositeDisplacement r (p.oppositeDisplacement r w))=e v
    rw [hdouble]
    have hw : e w=Multiplicative.ofAdd ![0,0,0,-(e v).toAdd 1] := e.apply_symm_apply _
    rw [hw]
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp [h0,h2,h3]

/-- Coordinates using the Atlas long-root convention, with the same original actor and line. -/
theorem exists_oppositeLongCoordinates (r : p.rightCore) (hr : (r:G)∉p.leftCore) :
    ∃ e : (p.leftCore ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V,
      (∀ v,e (p.oppositeAbelianizationActor r v)=Atlas.G2.TernaryCore.longRoot (e v)) ∧
      (∀ v,v∈(⁅p.rightCore,p.rightCore⁆.subgroupOf p.leftCore).map
        (QuotientGroup.mk' (cubicCoreLine c t.x)) ↔
          (e v).toAdd 1=0 ∧ (e v).toAdd 2=0 ∧ (e v).toAdd 3=0) := by
  let := t.left_oddCore_quotient_elementary
  have hn : ∃ v,p.oppositeAbelianizationActor r
      (p.oppositeAbelianizationActor r v*v⁻¹)*
        (p.oppositeAbelianizationActor r v*v⁻¹)⁻¹≠1 := by
    by_contra h
    push Not at h
    apply p.oppositeDisplacement_square_ne_one r hr
    apply MonoidHom.ext
    exact h
  obtain ⟨e,he⟩ := Atlas.G2.TernaryCore.exists_longRoot_coordinates
    (p.oppositeAbelianizationActor r) (p.oppositeAbelianizationActor_cube r)
    (t.maximal_core_abelianization_card p.core_order) hn
  have hdouble (v) : e (p.oppositeDisplacement r (p.oppositeDisplacement r v))=
      Multiplicative.ofAdd ![-(e v).toAdd 3,0,0,0] := by
    rw [p.oppositeAbelianizationActor_displacement,map_mul,map_inv,he,
      p.oppositeAbelianizationActor_displacement,map_mul,map_inv,he]
    exact Atlas.G2.TernaryCore.longRoot_double (e v)
  refine ⟨e,he,?_⟩
  intro v
  rw [←p.oppositeDisplacement_square_range r hr]
  constructor
  · rintro ⟨w,rfl⟩
    change (e (p.oppositeDisplacement r (p.oppositeDisplacement r w))).toAdd 1=0 ∧ _
    simp only [MonoidHom.comp_apply,hdouble]
    simp
  · rintro ⟨h1,h2,h3⟩
    let w := e.symm (Multiplicative.ofAdd ![0,0,0,-(e v).toAdd 0])
    refine ⟨w,e.injective ?_⟩
    change e (p.oppositeDisplacement r (p.oppositeDisplacement r w))=e v
    rw [hdouble]
    have hw : e w=Multiplicative.ofAdd ![0,0,0,-(e v).toAdd 0] := e.apply_symm_apply _
    rw [hw]
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp [h1,h2,h3]

/-- An actual inner change of the GL₂ marking places the original opposite cubic
at the specified Atlas root generator. The full original quotient action is retained. -/
theorem opposite_root_actor_marking (r : p.rightCore) (hr : (r:G)∉p.leftCore) :
    ∃ κ : Atlas.G2.TernaryLevi.GL23 ≃* Atlas.G2.TernaryLevi.GL23,
      t.cubicGLAbelianizationAction p.core_order
        (κ.symm (Atlas.G2.TernaryLevi.generator false))=p.oppositeAbelianizationActor r := by
  let n : cubicNormalizer c t.x :=
    ⟨r,t.leftCubicBorel_le (p.right_core_le_middle r.property)⟩
  let a := t.cubicLinearAction p.core_order n
  have ha3 : a^3=1 := by
    rw [←map_pow,show n^3=1 from Subtype.ext (p.opposite_core_cube r),map_one]
  have hane : a≠1 := by
    intro h
    have hk : n∈(t.cubicLinearAction p.core_order).ker := h
    rw [t.cubicLinearAction_kernel p.core_order] at hk
    exact hr hk
  obtain ⟨g,hg⟩ := isConj_iff.mp
    (Atlas.G2.TernaryLevi.isConj_generator_of_order_three a (orderOf_eq_prime ha3 hane))
  let κ := MulAut.conj g
  have hκ : κ a=Atlas.G2.TernaryLevi.generator false := hg
  refine ⟨κ,?_⟩
  rw [←hκ,MulEquiv.symm_apply_apply]
  exact (t.cubicAbelianizationAction_factor p.core_order n).symm

/-- The first generator equation for the full quotient comparison is constructed,
with the original opposite derived line in its literal short-root coordinate. -/
theorem exists_shortRoot_comparison (r : p.rightCore) (hr : (r:G)∉p.leftCore) :
    ∃ (κ : Atlas.G2.TernaryLevi.GL23 ≃* Atlas.G2.TernaryLevi.GL23)
      (e : (p.leftCore ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V),
      t.cubicGLAbelianizationAction p.core_order
        (κ.symm (Atlas.G2.TernaryLevi.generator false))=p.oppositeAbelianizationActor r ∧
      (∀ v,e (t.cubicGLAbelianizationAction p.core_order
        (κ.symm (Atlas.G2.TernaryLevi.generator false)) v)=
          Atlas.G2.TernaryLevi.shortQuotientAction
            (Atlas.G2.TernaryLevi.generator false) (e v)) ∧
      (∀ v,v∈(⁅p.rightCore,p.rightCore⁆.subgroupOf p.leftCore).map
        (QuotientGroup.mk' (cubicCoreLine c t.x)) ↔
          (e v).toAdd 0=0 ∧ (e v).toAdd 2=0 ∧ (e v).toAdd 3=0) := by
  obtain ⟨e,he,hline⟩ := p.exists_oppositeShortCoordinates r hr
  obtain ⟨κ,hκ⟩ := p.opposite_root_actor_marking r hr
  exact ⟨κ,e,hκ,fun v=>by rw [hκ,he,Atlas.G2.TernaryLevi.shortQuotientAction_root],hline⟩

/-- The first generator equation with the literal long-root action and coordinate line. -/
theorem exists_longRoot_comparison (r : p.rightCore) (hr : (r:G)∉p.leftCore) :
    ∃ (κ : Atlas.G2.TernaryLevi.GL23 ≃* Atlas.G2.TernaryLevi.GL23)
      (e : (p.leftCore ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V),
      t.cubicGLAbelianizationAction p.core_order
        (κ.symm (Atlas.G2.TernaryLevi.generator false))=p.oppositeAbelianizationActor r ∧
      (∀ v,e (t.cubicGLAbelianizationAction p.core_order
        (κ.symm (Atlas.G2.TernaryLevi.generator false)) v)=
          Atlas.G2.TernaryLevi.longQuotientAction
            (Atlas.G2.TernaryLevi.generator false) (e v)) ∧
      (∀ v,v∈(⁅p.rightCore,p.rightCore⁆.subgroupOf p.leftCore).map
        (QuotientGroup.mk' (cubicCoreLine c t.x)) ↔
          (e v).toAdd 1=0 ∧ (e v).toAdd 2=0 ∧ (e v).toAdd 3=0) := by
  obtain ⟨e,he,hline⟩ := p.exists_oppositeLongCoordinates r hr
  obtain ⟨κ,hκ⟩ := p.opposite_root_actor_marking r hr
  exact ⟨κ,e,hκ,fun v=>by rw [hκ,he,Atlas.G2.TernaryLevi.longQuotientAction_root],hline⟩

end AlignedCubicPair
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
