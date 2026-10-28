module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.BruhatCollection

/-!
# GlobalRealizations

The existing native signed charts verify every finite relation. On the same marked source quotient, only the two explicit Gauss equations are added to the previously required source equations.

Source: GLS3 2.3.5--8 and Table 2.4; Steinberg, section 11, Lemmas 62--64.
The source fields, local equations and exhaustive row selection remain source
producer obligations; binary type tags do not supply these data.
-/

@[expose] public noncomputable section

namespace ReeF4.RootPresentationRecognition.Global
open Subgroup SignedGeometry WeylPresentation
open Theory.GroupTheory OrderedRootPresentation CentralCovers.TwoPrimary
open CentralCovers.OddPrimary.Order
open LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData

/-- The alphabet is evaluated on the existing full exceptional-twist fixed carrier. -/
def native (m : ℕ) : Data m (Model m) where
  x := SignedCharts.rootHom m
  h := (Parabolics.fixedTorus m).subtype
  n := NormalizerPresentation.weyl m

@[simp] theorem native_pair (m : ℕ) (r : Index) (a : CoefficientField m) :
    (native m).pair r a = SignedCharts.pair m r a := rfl
@[simp] theorem native_quartet (m : ℕ) (r : Index) (a b : CoefficientField m) :
    (native m).quartet r a b = SignedCharts.quartet m r a b := rfl
@[simp] theorem native_reflection (m : ℕ) (s : Bool) :
    (native m).reflection s = RootPresentationRecognition.reflection m (NormalizerPresentation.side s) :=
  NormalizerPresentation.weyl_simple m s

@[simp] theorem native_torus (m : ℕ) (t : TorusParameter m) :
    (native m).torus t = RootPresentationRecognition.torus m t := rfl

/-- Every finite relation, including both literal Gauss equations, holds natively. -/
theorem native_relations (m : ℕ) : (native m).Relations where
  positive := AngularPresentation.native_equations m
  torus_root _ _ _ := rfl
  weyl_torus s t := rfl
  pair s r a := by
    simpa only [native_reflection,native_pair] using SignedCharts.reflection_pair m s r a
  quartet s r a b := by
    simpa only [native_reflection,native_quartet] using SignedCharts.reflection_quartet m s r a b
  linear_gauss a := by
    simpa only [native_reflection,native_pair,native_torus,NormalizerPresentation.side] using SignedCharts.pair_gauss m a
  suzuki_gauss a b hn := by
    simpa only [native_reflection,native_quartet,native_torus,NormalizerPresentation.side] using SignedCharts.quartet_gauss m a b hn

theorem native_unipotent (m : ℕ) : (native m).unipotent = Parabolics.unipotent m :=
  AngularPresentation.native_join_eq m

theorem native_borel (m : ℕ) : (native m).borel = Parabolics.borel m := by
  change (native m).unipotent ⊔ (Parabolics.fixedTorus m).subtype.range = _
  rw [native_unipotent,range_subtype]
  exact (SectionGeometry.BNPair.borel_eq_unipotent_sup_fixedTorus m).symm

open Theory.AlgebraicGroup.TitsSystem.SourceBinary
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)
variable {m : ℕ} (d : SourcePositive.Charts Q split m)
variable (T : SourceBorel.TorusData Q split d) (W : SourceNormalizer.WeylData Q split d T)

/-- Signed local root maps and the constructed full torus/Weyl maps in the SAME quotient. -/
def source : Data m (X ⧸ Q.D) where
  x := SourceSigned.rootHom Q split d T W
  h := SourceNormalizer.torus Q split d T
  n := SourceSigned.weyl Q split d T W

@[simp] theorem source_pair (r : Index) (a : CoefficientField m) :
    (source Q split d T W).pair r a = SourceSigned.pair Q split d T W r a :=
  SourceSigned.rootHom_pair Q split d T W r.1 r.2 a
@[simp] theorem source_quartet (r : Index) (a b : CoefficientField m) :
    (source Q split d T W).quartet r a b = SourceSigned.quartet Q split d T W r a b :=
  SourceSigned.rootHom_quartet Q split d T W r.1 r.2 a b
@[simp] theorem source_reflection (s : Bool) :
    (source Q split d T W).reflection s = W.n s := SourceSigned.weyl_simple Q split d T W s
@[simp] theorem source_torus (t : TorusParameter m) :
    (source Q split d T W).torus t = T.h t := by
  change T.h ((fixedTorusEquiv m).symm (fixedTorusEquiv m t)) = _
  rw [MulEquiv.symm_apply_apply]

/-- Two finite local source obligations. Their coefficients and full Cartan
are fixed by the native calculation; no global map or kernel is supplied. -/
structure SourceGauss : Prop where
  linear : ∀ a : (CoefficientField m)ˣ,
    (W.n false : X ⧸ Q.D) * SourceSigned.pair Q split d T W (false,0) a =
      SourceSigned.pair Q split d T W (false,0) (a⁻¹ : (CoefficientField m)ˣ) * T.h (linearTau a) *
        SourceSigned.pair Q split d T W (true,0) (a⁻¹ : (CoefficientField m)ˣ)
  suzuki : ∀ a b : CoefficientField m, ∀ hn : norm a b ≠ 0,
    (W.n true : X ⧸ Q.D) * SourceSigned.quartet Q split d T W (false,0) a b =
      SourceSigned.quartet Q split d T W (false,0) (negativeFirst a b) (negativeSecond a b) *
        T.h (suzukiTau (Units.mk0 (norm a b) hn)) *
          SourceSigned.quartet Q split d T W (true,0) (positiveFirst a b) (positiveSecond a b)

variable (E : SourceAngular.Equations Q split d)
variable (R : SourceSigned.Equations Q split d T W) (A : SourceGauss Q split d T W)

include E R A in
/-- Existing source equations and the two Gauss equations instantiate the abstract collector. -/
theorem source_relations : (source Q split d T W).Relations where
  positive := E
  torus_root t i a := SourceSigned.torus_root Q split d T W true t i a
  weyl_torus s t := by
    change SourceSigned.weyl Q split d T W (simple s) * _ *
      (SourceSigned.weyl Q split d T W (simple s))⁻¹ = _
    rw [SourceSigned.weyl_simple]
    exact W.action s t
  pair s r a := by simpa only [source_reflection,source_pair] using R.pair s r a
  quartet s r a b := by simpa only [source_reflection,source_quartet] using R.quartet s r a b
  linear_gauss a := by simpa only [source_reflection,source_pair,source_torus] using A.linear a
  suzuki_gauss a b hn := by
    simpa only [source_reflection,source_quartet,source_torus] using A.suzuki a b hn

include E in
theorem source_unipotent : (source Q split d T W).unipotent = split.U := by
  change join (AngularPresentation.Parameter m) (SourceAngular.sourceRoot Q split d) sourceOrder = _
  rw [← OrderedRootPresentation.eval_range (AngularPresentation.table m) E
    AngularPresentation.order_nodup mem_sourceOrder]
  exact SourceAngular.eval_range Q split d E

include E in
theorem source_borel : (source Q split d T W).borel = Q.tits.B := by
  change (source Q split d T W).unipotent ⊔ (SourceNormalizer.torus Q split d T).range = _
  rw [source_unipotent Q split d T W E]
  have he : (SourceNormalizer.torus Q split d T).range = T.h.range := by
    ext y
    constructor
    · rintro ⟨t,rfl⟩; exact ⟨(fixedTorusEquiv m).symm t,rfl⟩
    · rintro ⟨t,rfl⟩
      refine ⟨fixedTorusEquiv m t,?_⟩
      change T.h ((fixedTorusEquiv m).symm (fixedTorusEquiv m t)) = _
      rw [MulEquiv.symm_apply_apply]
  rw [he,T.range_eq]
  exact split.factorization

end ReeF4.RootPresentationRecognition.Global
