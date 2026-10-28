module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCoreReconstruction
public import Theory.SpecificGroups.G2.TernaryCoreRepresentation

/-!
# Original cubic cores compared with the literal ternary Atlas radicals

The original cubic generator fixes the scalar coordinates on its derived
line. The concrete Atlas radical extensions now discharge the target-group,
central-kernel, involution and commutator-construction premises of the
previous reconstruction theorem. A form-preserving quotient comparison
therefore gives an actual core equivalence preserving the original generator
and the literal quotient maps, on either side.

Constructing those quotient comparisons with full actor equivariance and
compatibility on the whole original middle remains necessary. This is a
reduction within Aschbacher–Smith I.4.5, p.417, not completed recognition.
The literal Chapter14 application is Chapter14AtlasCoreComparison.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
namespace CubicTorus
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
variable (t : CubicTorus c)

/-- The original marked generator, inside its literal derived line. -/
def cubicLineGenerator : cubicCoreLine c t.x :=
  ⟨⟨t.x,cubic_line_le_oddCore c t.x t.x_order (mem_zpowers _)⟩,mem_zpowers _⟩

omit [Finite G] in
theorem cubicLineGenerator_order : orderOf t.cubicLineGenerator=3 := by
  rw [orderOf_mk,orderOf_mk]
  exact (orderOf_coe (t.x:c.H)).trans ((orderOf_coe t.x).trans t.x_order)

theorem cubicLineGenerator_generates (x : cubicCoreLine c t.x) :
    x∈zpowers t.cubicLineGenerator := by
  have he : zpowers t.cubicLineGenerator=⊤ := eq_of_le_of_card_ge le_top (by
    rw [card_top,cubicCoreLine_card c t.x t.x_order,Nat.card_zpowers,t.cubicLineGenerator_order])
  rw [he]
  trivial

/-- Scalar coordinates normalized by the original marked cubic generator. -/
noncomputable def cubicLineScalar : cubicCoreLine c t.x ≃* Multiplicative (ZMod 3) :=
  (zmodMulEquivOfGenerator t.cubicLineGenerator_generates
    (cubicCoreLine_card c t.x t.x_order)).symm

@[simp] theorem cubicLineScalar_generator :
    t.cubicLineScalar t.cubicLineGenerator=Multiplicative.ofAdd 1 := by
  apply (zmodMulEquivOfGenerator t.cubicLineGenerator_generates
    (cubicCoreLine_card c t.x t.x_order)).injective
  rw [cubicLineScalar,MulEquiv.apply_symm_apply,zmodMulEquivOfGenerator_apply_ofAdd_one]


/-- Reconstruct the actual Atlas short radical from the original quotient form,
with no unspecified target extension or cubic-line map. -/
noncomputable def cubicAtlasShortEquiv (hc : Nat.card (cubicOddCore c t.x)=243)
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V)
    (hform : ∀ v w,t.cubicLineScalar (t.cubicCommutatorLine hc v w)=
      Multiplicative.ofAdd (Atlas.G2.TernaryCore.shortForm (e v) (e w))) :
    cubicOddCore c t.x ≃* Atlas.G2.LieParabolicSetup.radical₁ (F:=ZMod 3) :=
  t.cubicCoreEquivOfForm Atlas.G2.TernaryCore.shortExtension hc e
    (t.cubicLineScalar.trans Atlas.G2.TernaryCore.shortKernelEquiv) (by
      intro v w
      change Atlas.G2.TernaryCore.shortKernelEquiv
        (t.cubicLineScalar (t.cubicCommutatorLine hc v w))=_
      rw [hform,Atlas.G2.TernaryCore.shortExtension_form])

theorem cubicAtlasShortEquiv_quotient (hc : Nat.card (cubicOddCore c t.x)=243)
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V)
    (hform : ∀ v w,t.cubicLineScalar (t.cubicCommutatorLine hc v w)=
      Multiplicative.ofAdd (Atlas.G2.TernaryCore.shortForm (e v) (e w)))
    (x : cubicOddCore c t.x) :
    Atlas.G2.TernaryCore.shortQuotient (t.cubicAtlasShortEquiv hc e hform x)=
      e (QuotientGroup.mk' (cubicCoreLine c t.x) x) :=
  t.cubicCoreEquivOfForm_quotient Atlas.G2.TernaryCore.shortExtension hc e _ _ x

/-- The comparison preserves the original cubic marking in literal root coordinates. -/
theorem cubicAtlasShortEquiv_generator (hc : Nat.card (cubicOddCore c t.x)=243)
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V)
    (hform : ∀ v w,t.cubicLineScalar (t.cubicCommutatorLine hc v w)=
      Multiplicative.ofAdd (Atlas.G2.TernaryCore.shortForm (e v) (e w))) :
    t.cubicAtlasShortEquiv hc e hform t.cubicLineGenerator=Atlas.G2.TernaryCore.short 1 1 := by
  rw [cubicAtlasShortEquiv,t.cubicCoreEquivOfForm_line]
  change (Atlas.G2.TernaryCore.shortKernelEquiv
    (t.cubicLineScalar t.cubicLineGenerator):Atlas.G2.LieParabolicSetup.radical₁ (F:=ZMod 3))=_
  rw [t.cubicLineScalar_generator,Atlas.G2.TernaryCore.shortKernelEquiv_apply]
  rfl

/-- Reconstruct the actual Atlas long radical from the original quotient form,
with no unspecified target extension or cubic-line map. -/
noncomputable def cubicAtlasLongEquiv (hc : Nat.card (cubicOddCore c t.x)=243)
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V)
    (hform : ∀ v w,t.cubicLineScalar (t.cubicCommutatorLine hc v w)=
      Multiplicative.ofAdd (Atlas.G2.TernaryCore.longForm (e v) (e w))) :
    cubicOddCore c t.x ≃* Atlas.G2.LieParabolicSetup.radical₂ (F:=ZMod 3) :=
  t.cubicCoreEquivOfForm Atlas.G2.TernaryCore.longExtension hc e
    (t.cubicLineScalar.trans Atlas.G2.TernaryCore.longKernelEquiv) (by
      intro v w
      change Atlas.G2.TernaryCore.longKernelEquiv
        (t.cubicLineScalar (t.cubicCommutatorLine hc v w))=_
      rw [hform,Atlas.G2.TernaryCore.longExtension_form])

theorem cubicAtlasLongEquiv_quotient (hc : Nat.card (cubicOddCore c t.x)=243)
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V)
    (hform : ∀ v w,t.cubicLineScalar (t.cubicCommutatorLine hc v w)=
      Multiplicative.ofAdd (Atlas.G2.TernaryCore.longForm (e v) (e w)))
    (x : cubicOddCore c t.x) :
    Atlas.G2.TernaryCore.longQuotient (t.cubicAtlasLongEquiv hc e hform x)=
      e (QuotientGroup.mk' (cubicCoreLine c t.x) x) :=
  t.cubicCoreEquivOfForm_quotient Atlas.G2.TernaryCore.longExtension hc e _ _ x

/-- The comparison preserves the original cubic marking in literal root coordinates. -/
theorem cubicAtlasLongEquiv_generator (hc : Nat.card (cubicOddCore c t.x)=243)
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V)
    (hform : ∀ v w,t.cubicLineScalar (t.cubicCommutatorLine hc v w)=
      Multiplicative.ofAdd (Atlas.G2.TernaryCore.longForm (e v) (e w))) :
    t.cubicAtlasLongEquiv hc e hform t.cubicLineGenerator=Atlas.G2.TernaryCore.long 1 1 := by
  rw [cubicAtlasLongEquiv,t.cubicCoreEquivOfForm_line]
  change (Atlas.G2.TernaryCore.longKernelEquiv
    (t.cubicLineScalar t.cubicLineGenerator):Atlas.G2.LieParabolicSetup.radical₂ (F:=ZMod 3))=_
  rw [t.cubicLineScalar_generator,Atlas.G2.TernaryCore.longKernelEquiv_apply]
  rfl


/-- Compatibility of the concrete quotient actions lifts to the full core actions. -/
theorem cubicAtlasShortEquiv_action (hc : Nat.card (cubicOddCore c t.x)=243)
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V)
    (hform : ∀ v w,t.cubicLineScalar (t.cubicCommutatorLine hc v w)=
      Multiplicative.ofAdd (Atlas.G2.TernaryCore.shortForm (e v) (e w)))
    (a : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (b : Atlas.G2.LieParabolicSetup.parabolic₁ (F:=ZMod 3))
    (hb : Commute (b:Atlas.G2.Model (ZMod 3)) (Atlas.G2.torus (-1) (-1)))
    (he : ∀ v,e (t.cubicAbelianizationAction
      (inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm a)) v)=
      Atlas.G2.TernaryCore.shortQuotientAction b (e v))
    (x : cubicOddCore c t.x) :
    t.cubicAtlasShortEquiv hc e hform (t.cubicGLCoreAction hc a x)=
      Atlas.G2.TernaryCore.shortCoreAction b (t.cubicAtlasShortEquiv hc e hform x) := by
  apply t.cubicCoreEquivOfForm_GL Atlas.G2.TernaryCore.shortExtension hc e _ _ a
    (Atlas.G2.TernaryCore.shortCoreAction b) (Atlas.G2.TernaryCore.shortQuotientAction b)
  · exact Atlas.G2.TernaryCore.shortCoreAction_involution b hb
  · intro v
    exact (Atlas.G2.TernaryCore.shortQuotientAction_quotient b v).symm
  · exact he

/-- Compatibility of the concrete quotient actions lifts to the full core actions. -/
theorem cubicAtlasLongEquiv_action (hc : Nat.card (cubicOddCore c t.x)=243)
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V)
    (hform : ∀ v w,t.cubicLineScalar (t.cubicCommutatorLine hc v w)=
      Multiplicative.ofAdd (Atlas.G2.TernaryCore.longForm (e v) (e w)))
    (a : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (b : Atlas.G2.LieParabolicSetup.parabolic₂ (F:=ZMod 3))
    (hb : Commute (b:Atlas.G2.Model (ZMod 3)) (Atlas.G2.torus 1 (-1)))
    (he : ∀ v,e (t.cubicAbelianizationAction
      (inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm a)) v)=
      Atlas.G2.TernaryCore.longQuotientAction b (e v))
    (x : cubicOddCore c t.x) :
    t.cubicAtlasLongEquiv hc e hform (t.cubicGLCoreAction hc a x)=
      Atlas.G2.TernaryCore.longCoreAction b (t.cubicAtlasLongEquiv hc e hform x) := by
  apply t.cubicCoreEquivOfForm_GL Atlas.G2.TernaryCore.longExtension hc e _ _ a
    (Atlas.G2.TernaryCore.longCoreAction b) (Atlas.G2.TernaryCore.longQuotientAction b)
  · exact Atlas.G2.TernaryCore.longCoreAction_involution b hb
  · intro v
    exact (Atlas.G2.TernaryCore.longQuotientAction_quotient b v).symm
  · exact he

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
