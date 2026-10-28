module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.AtlasCoreComparison
public import Theory.ElementaryAbelian.TernaryAlternatingCoordinates
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalAlignedLinear

/-!
# Constructed Atlas models of the original marked cubic cores

The full original abelianization has order81 and its alternating commutator
form has the original center plane of order9 as radical. Splitting that
radical and normalizing the complementary plane constructs form-preserving
coordinates with the scalar map fixed by the original cubic generator.
The two literal Atlas root conventions give actual core isomorphisms,
preserving quotient maps, cubic generators and the distinguished involution.
The opposite core map is transported by the original Sylow aligner.

This discharges the quotient-form existence premises of
`AtlasCoreComparison`, including in the literal Chapter14 application
`Chapter14AtlasCoreModels`. The chosen coordinates need not intertwine the
full endpoint actors or agree on the whole common middle. Those compatible
endpoint maps, and the independent strongly-three-embedded exclusion,
remain necessary for Aschbacher–Smith I.4.5, printed p.417.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
namespace CubicTorus
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
variable (t : CubicTorus c)

private noncomputable def cubicScalarPairing (hc : Nat.card (cubicOddCore c t.x)=243) :
    (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) →*
      ((cubicOddCore c t.x ⧸ cubicCoreLine c t.x) →* Multiplicative (ZMod 3)) where
  toFun v := {
    toFun w := t.cubicLineScalar (t.cubicCommutatorLine hc v w)
    map_one' := by
      rw [←t.cubicLineScalar.map_one]
      apply congrArg t.cubicLineScalar
      apply Subtype.ext
      exact congrArg (fun z : center (cubicOddCore c t.x) => (z:cubicOddCore c t.x)) ((t.cubicCommutatorPairing v).map_one)
    map_mul' w u := by
      rw [←map_mul]
      apply congrArg t.cubicLineScalar
      apply Subtype.ext
      exact congrArg (fun z : center (cubicOddCore c t.x) => (z:cubicOddCore c t.x)) ((t.cubicCommutatorPairing v).map_mul w u) }
  map_one' := by
    apply MonoidHom.ext
    intro w
    change t.cubicLineScalar (t.cubicCommutatorLine hc 1 w)=1
    rw [←t.cubicLineScalar.map_one]
    apply congrArg t.cubicLineScalar
    apply Subtype.ext
    have h := DFunLike.congr_fun t.cubicCommutatorPairing.map_one w
    exact congrArg (fun z : center (cubicOddCore c t.x) => (z:cubicOddCore c t.x)) h
  map_mul' v w := by
    apply MonoidHom.ext
    intro u
    change t.cubicLineScalar (t.cubicCommutatorLine hc (v*w) u)=
      t.cubicLineScalar (t.cubicCommutatorLine hc v u)*
      t.cubicLineScalar (t.cubicCommutatorLine hc w u)
    rw [←map_mul]
    apply congrArg t.cubicLineScalar
    apply Subtype.ext
    have h := DFunLike.congr_fun (t.cubicCommutatorPairing.map_mul v w) u
    exact congrArg (fun z : center (cubicOddCore c t.x) => (z:cubicOddCore c t.x)) h

private theorem cubicScalarPairing_eq_one (hc : Nat.card (cubicOddCore c t.x)=243)
    (v w : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    t.cubicScalarPairing hc v w=1 ↔ t.cubicCommutatorPairing v w=1 := by
  change t.cubicLineScalar (t.cubicCommutatorLine hc v w)=1 ↔ _
  rw [map_eq_one_iff _ t.cubicLineScalar.injective]
  constructor
  · intro h
    apply Subtype.ext
    exact congrArg (fun z : cubicCoreLine c t.x => (z:cubicOddCore c t.x)) h
  · intro h
    apply Subtype.ext
    exact congrArg (fun z : center (cubicOddCore c t.x) => (z:cubicOddCore c t.x)) h

/-- Construct the short quotient comparison from the original commutator form;
no form equivalence or basis is assumed. -/
theorem exists_cubicAtlasShortForm (hc : Nat.card (cubicOddCore c t.x)=243) :
    ∃ e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V,
      ∀ v w,t.cubicLineScalar (t.cubicCommutatorLine hc v w)=
        Multiplicative.ofAdd (Atlas.G2.TernaryCore.shortForm (e v) (e w)) := by
  let := t.left_oddCore_quotient_elementary
  apply IsElementaryAbelian.exists_ternary_alternating_coordinates
    (t.cubicScalarPairing hc) (fun v => (t.cubicScalarPairing_eq_one hc v v).mpr
      (t.cubicCommutatorPairing_self v)) t.cubicCenterPlane
  · intro v
    simpa only [t.cubicScalarPairing_eq_one hc] using t.cubicCommutatorPairing_radical v
  · exact t.maximal_core_abelianization_card hc
  · exact t.cubicCenterPlane_card hc

private def shortToLong : Atlas.G2.TernaryCore.V ≃* Atlas.G2.TernaryCore.V where
  toFun v := Multiplicative.ofAdd ![v.toAdd 1,v.toAdd 2,v.toAdd 3,v.toAdd 0]
  invFun v := Multiplicative.ofAdd ![v.toAdd 3,v.toAdd 0,v.toAdd 1,v.toAdd 2]
  left_inv v := by apply Multiplicative.toAdd.injective; ext i; fin_cases i <;> rfl
  right_inv v := by apply Multiplicative.toAdd.injective; ext i; fin_cases i <;> rfl
  map_mul' v w := by apply Multiplicative.toAdd.injective; ext i; fin_cases i <;> rfl

/-- Construct the long quotient comparison with its different literal root convention. -/
theorem exists_cubicAtlasLongForm (hc : Nat.card (cubicOddCore c t.x)=243) :
    ∃ e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V,
      ∀ v w,t.cubicLineScalar (t.cubicCommutatorLine hc v w)=
        Multiplicative.ofAdd (Atlas.G2.TernaryCore.longForm (e v) (e w)) := by
  obtain ⟨e,he⟩ := t.exists_cubicAtlasShortForm hc
  refine ⟨e.trans shortToLong,?_⟩
  intro v w
  rw [he]
  simp [Atlas.G2.TernaryCore.shortForm,Atlas.G2.TernaryCore.longForm,shortToLong,mul_comm]

/-- Fixed chosen coordinates for the short radical, normalized by the original cubic line. -/
noncomputable def cubicAtlasShortCoordinates (hc : Nat.card (cubicOddCore c t.x)=243) :
    (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V :=
  (t.exists_cubicAtlasShortForm hc).choose

theorem cubicAtlasShortCoordinates_form (hc : Nat.card (cubicOddCore c t.x)=243)
    (v w : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    t.cubicLineScalar (t.cubicCommutatorLine hc v w)=Multiplicative.ofAdd
      (Atlas.G2.TernaryCore.shortForm (t.cubicAtlasShortCoordinates hc v)
        (t.cubicAtlasShortCoordinates hc w)) :=
  (t.exists_cubicAtlasShortForm hc).choose_spec v w

/-- Fixed chosen coordinates for the long radical with its literal root convention. -/
noncomputable def cubicAtlasLongCoordinates (hc : Nat.card (cubicOddCore c t.x)=243) :
    (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V :=
  (t.exists_cubicAtlasLongForm hc).choose

theorem cubicAtlasLongCoordinates_form (hc : Nat.card (cubicOddCore c t.x)=243)
    (v w : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    t.cubicLineScalar (t.cubicCommutatorLine hc v w)=Multiplicative.ofAdd
      (Atlas.G2.TernaryCore.longForm (t.cubicAtlasLongCoordinates hc v)
        (t.cubicAtlasLongCoordinates hc w)) :=
  (t.exists_cubicAtlasLongForm hc).choose_spec v w

/-- The constructed quotient coordinates identify the original order-nine center plane. -/
theorem cubicAtlasShortCoordinates_center (hc : Nat.card (cubicOddCore c t.x)=243)
    (v : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    v∈t.cubicCenterPlane ↔
      (t.cubicAtlasShortCoordinates hc v).toAdd 0=0 ∧
      (t.cubicAtlasShortCoordinates hc v).toAdd 3=0 := by
  have h (w : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
      t.cubicCommutatorPairing v w=1 ↔
        Atlas.G2.TernaryCore.shortForm (t.cubicAtlasShortCoordinates hc v)
          (t.cubicAtlasShortCoordinates hc w)=0 := by
    rw [←t.cubicScalarPairing_eq_one hc]
    change t.cubicLineScalar (t.cubicCommutatorLine hc v w)=1 ↔ _
    rw [t.cubicAtlasShortCoordinates_form]
    rfl
  rw [←t.cubicCommutatorPairing_radical]
  simp_rw [h]
  rw [←Atlas.G2.TernaryCore.shortForm_radical]
  constructor
  · intro hh w
    obtain ⟨w,rfl⟩ := (t.cubicAtlasShortCoordinates hc).surjective w
    exact hh w
  · intro hh w
    exact hh _

/-- The long coordinates retain the same original center plane in the long-root convention. -/
theorem cubicAtlasLongCoordinates_center (hc : Nat.card (cubicOddCore c t.x)=243)
    (v : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    v∈t.cubicCenterPlane ↔
      (t.cubicAtlasLongCoordinates hc v).toAdd 2=0 ∧
      (t.cubicAtlasLongCoordinates hc v).toAdd 3=0 := by
  have h (w : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
      t.cubicCommutatorPairing v w=1 ↔
        Atlas.G2.TernaryCore.longForm (t.cubicAtlasLongCoordinates hc v)
          (t.cubicAtlasLongCoordinates hc w)=0 := by
    rw [←t.cubicScalarPairing_eq_one hc]
    change t.cubicLineScalar (t.cubicCommutatorLine hc v w)=1 ↔ _
    rw [t.cubicAtlasLongCoordinates_form]
    rfl
  rw [←t.cubicCommutatorPairing_radical]
  simp_rw [h]
  rw [←Atlas.G2.TernaryCore.longForm_radical]
  constructor
  · intro hh w
    obtain ⟨w,rfl⟩ := (t.cubicAtlasLongCoordinates hc).surjective w
    exact hh w
  · intro hh w
    exact hh _

/-- An actual original-core isomorphism to the Atlas short radical, with no comparison premise. -/
noncomputable def cubicAtlasShortModel (hc : Nat.card (cubicOddCore c t.x)=243) :
    cubicOddCore c t.x ≃* Atlas.G2.LieParabolicSetup.radical₁ (F:=ZMod 3) :=
  t.cubicAtlasShortEquiv hc (t.cubicAtlasShortCoordinates hc)
    (t.cubicAtlasShortCoordinates_form hc)

/-- An actual original-core isomorphism to the Atlas long radical, with no comparison premise. -/
noncomputable def cubicAtlasLongModel (hc : Nat.card (cubicOddCore c t.x)=243) :
    cubicOddCore c t.x ≃* Atlas.G2.LieParabolicSetup.radical₂ (F:=ZMod 3) :=
  t.cubicAtlasLongEquiv hc (t.cubicAtlasLongCoordinates hc)
    (t.cubicAtlasLongCoordinates_form hc)

theorem cubicAtlasShortModel_quotient (hc : Nat.card (cubicOddCore c t.x)=243)
    (x : cubicOddCore c t.x) :
    Atlas.G2.TernaryCore.shortQuotient (t.cubicAtlasShortModel hc x)=
      t.cubicAtlasShortCoordinates hc (QuotientGroup.mk' (cubicCoreLine c t.x) x) :=
  t.cubicAtlasShortEquiv_quotient hc _ _ x

theorem cubicAtlasLongModel_quotient (hc : Nat.card (cubicOddCore c t.x)=243)
    (x : cubicOddCore c t.x) :
    Atlas.G2.TernaryCore.longQuotient (t.cubicAtlasLongModel hc x)=
      t.cubicAtlasLongCoordinates hc (QuotientGroup.mk' (cubicCoreLine c t.x) x) :=
  t.cubicAtlasLongEquiv_quotient hc _ _ x

theorem cubicAtlasShortModel_generator (hc : Nat.card (cubicOddCore c t.x)=243) :
    t.cubicAtlasShortModel hc t.cubicLineGenerator=Atlas.G2.TernaryCore.short 1 1 :=
  t.cubicAtlasShortEquiv_generator hc _ _

theorem cubicAtlasLongModel_generator (hc : Nat.card (cubicOddCore c t.x)=243) :
    t.cubicAtlasLongModel hc t.cubicLineGenerator=Atlas.G2.TernaryCore.long 1 1 :=
  t.cubicAtlasLongEquiv_generator hc _ _

/-- The constructed short comparison intertwines the original involution and Atlas torus. -/
theorem cubicAtlasShortModel_involution (hc : Nat.card (cubicOddCore c t.x)=243)
    (x : cubicOddCore c t.x) :
    t.cubicAtlasShortModel hc (t.cubicInvolutionExtension.involution x)=
      Atlas.G2.TernaryCore.shortInvolution (t.cubicAtlasShortModel hc x) := by
  let := t.left_oddCore_quotient_elementary
  apply CubicInvolutionExtension.liftEquiv_involution
  intro v w
  change Atlas.G2.TernaryCore.shortKernelEquiv
    (t.cubicLineScalar (t.cubicExtensionKernelEquiv
      (t.cubicInvolutionExtension.commutatorValue v w)))=_
  rw [t.cubicExtensionPairing_eq hc,t.cubicAtlasShortCoordinates_form,
    Atlas.G2.TernaryCore.shortExtension_form]

/-- The constructed long comparison intertwines the original involution and Atlas torus. -/
theorem cubicAtlasLongModel_involution (hc : Nat.card (cubicOddCore c t.x)=243)
    (x : cubicOddCore c t.x) :
    t.cubicAtlasLongModel hc (t.cubicInvolutionExtension.involution x)=
      Atlas.G2.TernaryCore.longInvolution (t.cubicAtlasLongModel hc x) := by
  let := t.left_oddCore_quotient_elementary
  apply CubicInvolutionExtension.liftEquiv_involution
  intro v w
  change Atlas.G2.TernaryCore.longKernelEquiv
    (t.cubicLineScalar (t.cubicExtensionKernelEquiv
      (t.cubicInvolutionExtension.commutatorValue v w)))=_
  rw [t.cubicExtensionPairing_eq hc,t.cubicAtlasLongCoordinates_form,
    Atlas.G2.TernaryCore.longExtension_form]

end CubicTorus
namespace AlignedCubicPair
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
variable {t : CubicTorus c} (p : AlignedCubicPair t)

/-- The actual opposite core under the same conjugation as the original endpoint alignment. -/
def rightCoreTransport : cubicOddCore (swapFactors c) t.swap.x ≃* p.rightCore :=
  (MulAut.conj p.aligner).subgroupMap _

omit [Finite G] in
@[simp] theorem rightCoreTransport_apply (x : cubicOddCore (swapFactors c) t.swap.x) :
    (p.rightCoreTransport x:G)=MulAut.conj p.aligner (x:G) := rfl

/-- The first actual aligned core, identified with the literal Atlas short radical. -/
noncomputable def leftAtlasCoreModel : p.leftCore ≃*
    Atlas.G2.LieParabolicSetup.radical₁ (F:=ZMod 3) :=
  t.cubicAtlasShortModel p.core_order

/-- The opposite actual aligned core, identified with the literal Atlas long radical. -/
noncomputable def rightAtlasCoreModel : p.rightCore ≃*
    Atlas.G2.LieParabolicSetup.radical₂ (F:=ZMod 3) :=
  p.rightCoreTransport.symm.trans (t.swap.cubicAtlasLongModel p.right_core_order)

@[simp] theorem rightAtlasCoreModel_transport (x : cubicOddCore (swapFactors c) t.swap.x) :
    p.rightAtlasCoreModel (p.rightCoreTransport x)=t.swap.cubicAtlasLongModel p.right_core_order x := by
  change t.swap.cubicAtlasLongModel p.right_core_order
    (p.rightCoreTransport.symm (p.rightCoreTransport x))=_
  rw [MulEquiv.symm_apply_apply]

theorem leftAtlasCoreModel_generator :
    p.leftAtlasCoreModel t.cubicLineGenerator=Atlas.G2.TernaryCore.short 1 1 :=
  t.cubicAtlasShortModel_generator p.core_order

/-- The opposite cubic generator is transported by the original Sylow aligner. -/
theorem rightAtlasCoreModel_generator :
    p.rightAtlasCoreModel (p.rightCoreTransport t.swap.cubicLineGenerator)=
      Atlas.G2.TernaryCore.long 1 1 := by
  rw [p.rightAtlasCoreModel_transport,t.swap.cubicAtlasLongModel_generator]

/-- The literal short-core quotient square. -/
theorem leftAtlasCoreModel_quotient (x : p.leftCore) :
    Atlas.G2.TernaryCore.shortQuotient (p.leftAtlasCoreModel x)=
      t.cubicAtlasShortCoordinates p.core_order (QuotientGroup.mk' (cubicCoreLine c t.x) x) :=
  t.cubicAtlasShortModel_quotient p.core_order x

/-- The opposite quotient square uses exactly the same original alignment as the endpoint. -/
theorem rightAtlasCoreModel_quotient (x : p.rightCore) :
    Atlas.G2.TernaryCore.longQuotient (p.rightAtlasCoreModel x)=
      t.swap.cubicAtlasLongCoordinates p.right_core_order
        (QuotientGroup.mk' (cubicCoreLine (swapFactors c) t.swap.x)
          (p.rightCoreTransport.symm x)) :=
  t.swap.cubicAtlasLongModel_quotient p.right_core_order _

end AlignedCubicPair

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
