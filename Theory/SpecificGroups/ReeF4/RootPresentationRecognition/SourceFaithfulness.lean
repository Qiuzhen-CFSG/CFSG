module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.NativeFaithfulness

/-!
# SourceFaithfulness

The independent source kernel proof uses the same marked Weyl quotient, Carter coordinates and full Cartan. Composing the two constructed evaluations yields an actual equivalence with the full native Model m.

Source: GLS3 2.3.5--8 and Table 2.4; Steinberg, section 11, Lemmas 62--64.
The source fields, local equations and exhaustive row selection remain source
producer obligations; binary type tags do not supply these data.
-/

@[expose] public noncomputable section

namespace ReeF4.RootPresentationRecognition.Global
open Subgroup Theory.GroupTheory OrderedRootPresentation
open SignedGeometry WeylPresentation CentralCovers.TwoPrimary
open CentralCovers.OddPrimary.Order
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)
variable {m : ℕ} (d : SourcePositive.Charts Q split m)
variable (T : SourceBorel.TorusData Q split d) (W : SourceNormalizer.WeylData Q split d T)
variable (E : SourceAngular.Equations Q split d)
variable (R : SourceSigned.Equations Q split d T W) (A : SourceGauss Q split d T W)

include E in
/-- Coverage of the original N and original B proves source generation. -/
theorem source_whole : (source Q split d T W).whole = ⊤ := by
  apply top_unique
  rw [← Q.tits.generate]
  apply (closure_le _).mpr
  intro g hg
  rcases hg with hg | hg
  · exact (source Q split d T W).borel_le_whole ((source_borel Q split d T W E).symm ▸ hg)
  · obtain ⟨a,ha⟩ := SourceNormalizer.eval_surjective Q split d T W ⟨g,hg⟩
    have he := congrArg Subtype.val ha
    rw [SourceNormalizer.eval_apply] at he
    change SourceNormalizer.torus Q split d T a.left * SourceSigned.weyl Q split d T W a.right = g at he
    rw [← he]
    exact mul_mem ((source Q split d T W).borel_le_whole ((source Q split d T W).torus_mem_borel a.left))
      ((source Q split d T W).weyl_mem_whole a.right)

/-- Constructed source evaluation; its only extra premises are the local equations. -/
def sourceEval : Presentation.Group m →* X ⧸ Q.D :=
  Presentation.eval (source Q split d T W) (source_relations Q split d T W E R A)

@[simp] theorem sourceEval_torus (t : Parabolics.fixedTorus m) :
    sourceEval Q split d T W E R A (Presentation.torus m t) = SourceNormalizer.torus Q split d T t :=
  Presentation.eval_torus _ _ t
@[simp] theorem sourceEval_weyl (w : Weyl) :
    sourceEval Q split d T W E R A (Presentation.weyl m w) = SourceSigned.weyl Q split d T W w :=
  Presentation.eval_weyl _ _ w

theorem sourceEval_surjective : Function.Surjective (sourceEval Q split d T W E R A) := by
  apply MonoidHom.range_eq_top.mp
  rw [sourceEval,Presentation.eval_range,source_whole Q split d T W E]

private theorem sourceEval_positive (a : AngularPresentation.Presentation m) :
    sourceEval Q split d T W E R A (Presentation.positiveMap m a) = SourceAngular.eval Q split d E a :=
  DFunLike.congr_fun (Presentation.eval_positiveMap (source Q split d T W)
    (source_relations Q split d T W E R A)) a

/-- Carter's source coordinates kill the abstract positive kernel. -/
theorem sourceEval_unipotent_kernel (u : Presentation.Group m)
    (hu : u ∈ (Presentation.generators m).unipotent) (he : sourceEval Q split d T W E R A u = 1) : u = 1 := by
  rw [← Presentation.positiveMap_range] at hu
  obtain ⟨a,rfl⟩ := hu
  have ha : a = 1 := (SourceAngular.evalU_bijective Q split d E).injective
    (by
      apply Subtype.ext
      change SourceAngular.eval Q split d E a = _
      simpa only [sourceEval_positive,map_one,coe_one] using he)
  rw [ha,map_one]

theorem sourceEval_unipotent_mem (u : Presentation.Group m)
    (hu : u ∈ (Presentation.generators m).unipotent) : sourceEval Q split d T W E R A u ∈ split.U := by
  rw [← Presentation.positiveMap_range] at hu
  obtain ⟨a,rfl⟩ := hu
  rw [sourceEval_positive]
  exact (SourceAngular.evalU Q split d E a).property

/-- The SAME split U and full H = B ∩ N separate the source Borel kernel. -/
theorem sourceEval_borel_kernel (b : Presentation.Group m)
    (hb : b ∈ (Presentation.generators m).borel) (he : sourceEval Q split d T W E R A b = 1) : b = 1 := by
  obtain ⟨t,u,hu,rfl⟩ := ((Presentation.generators m).mem_borel_iff (Presentation.relations m) b).mp hb
  change sourceEval Q split d T W E R A (Presentation.torus m t * u) = 1 at he
  change Presentation.torus m t * u = 1
  rw [map_mul,sourceEval_torus] at he
  have htH : SourceNormalizer.torus Q split d T t ∈ Q.tits.B ⊓ Q.tits.N := by
    rw [← T.range_eq]
    exact ⟨(fixedTorusEquiv m).symm t,rfl⟩
  have htU : SourceNormalizer.torus Q split d T t ∈ split.U := by
    rw [eq_inv_of_mul_eq_one_left he]
    exact split.U.inv_mem (sourceEval_unipotent_mem Q split d T W E R A u hu)
  have ht : SourceNormalizer.torus Q split d T t = 1 :=
    (unipotent_disjoint_torus split).symm.le_bot ⟨htH,htU⟩
  have hi : Function.Injective (SourceNormalizer.torus Q split d T) :=
    T.injective.comp (fixedTorusEquiv m).symm.injective
  have ht1 : t = 1 := hi (ht.trans (map_one _).symm)
  have hu1 : u = 1 := sourceEval_unipotent_kernel Q split d T W E R A u hu
    (by simpa only [ht,one_mul] using he)
  rw [ht1,hu1,map_one,mul_one]

/-- The actual source Weyl quotient separates its literal Weyl lifts from B. -/
theorem source_weyl_mem_borel (w : WeylPresentation.Weyl)
    (hw : SourceSigned.weyl Q split d T W w ∈ Q.tits.B) : w = 1 := by
  have he : SourceNormalizer.quotientWeyl Q split d T W w = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨hw,(SourceNormalizer.weyl Q split d T W w).property⟩
  exact (SourceNormalizer.quotientWeyl_bijective Q split d T W).injective
    (he.trans (map_one _).symm)

/-- The second whole-group kernel is proved from the original source Borel
and Weyl quotient, independently of the native kernel argument. -/
theorem sourceEval_injective : Function.Injective (sourceEval Q split d T W E R A) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  obtain ⟨a,b,s,k,ha,hb,hk,rfl⟩ := Presentation.bruhat m g
  have hB {c : Presentation.Group m} (hc : c ∈ (Presentation.generators m).borel) :
      sourceEval Q split d T W E R A c ∈ Q.tits.B := by
    rw [← source_borel Q split d T W E]
    exact Presentation.eval_mem_borel (source Q split d T W) (source_relations Q split d T W E R A) hc
  have hw : SourceSigned.weyl Q split d T W (alternating s k) ∈ Q.tits.B := by
    have he : SourceSigned.weyl Q split d T W (alternating s k) =
        (sourceEval Q split d T W E R A a)⁻¹ * (sourceEval Q split d T W E R A b)⁻¹ := by
      change sourceEval Q split d T W E R A (a * Presentation.weyl m (alternating s k) * b) = 1 at hg
      rw [map_mul,map_mul,sourceEval_weyl] at hg
      calc
        _ = (sourceEval Q split d T W E R A a)⁻¹ *
          (sourceEval Q split d T W E R A a * SourceSigned.weyl Q split d T W (alternating s k) *
            sourceEval Q split d T W E R A b) * (sourceEval Q split d T W E R A b)⁻¹ := by group
        _ = _ := by rw [hg,mul_one]
    rw [he]
    exact mul_mem (inv_mem (hB ha)) (inv_mem (hB hb))
  have hw1 := source_weyl_mem_borel Q split d T W (alternating s k) hw
  change a * Presentation.weyl m (alternating s k) * b = 1
  rw [hw1,map_one,mul_one] at hg ⊢
  exact sourceEval_borel_kernel Q split d T W E R A (a*b) (mul_mem ha hb) hg

def sourceEquiv : Presentation.Group m ≃* X ⧸ Q.D :=
  MulEquiv.ofBijective (sourceEval Q split d T W E R A)
    ⟨sourceEval_injective Q split d T W E R A,sourceEval_surjective Q split d T W E R A⟩

/-- An actual full Ree comparison, including Model 0, constructed from finite
source equations. Constructing those equations remains a separate source obligation. -/
def comparison : (X ⧸ Q.D) ≃* Model m :=
  (sourceEquiv Q split d T W E R A).symm.trans (nativeEquiv m)

@[simp] theorem comparison_root (p : Bool) (i : PositiveTables.Root) (a : AngularPresentation.Parameter m i) :
    comparison Q split d T W E R A (SourceSigned.rootHom Q split d T W p i a) =
      SignedCharts.rootHom m p i a := by
  have he : sourceEquiv Q split d T W E R A (Presentation.root m p i a) =
      SourceSigned.rootHom Q split d T W p i a := Presentation.eval_root (source Q split d T W) (source_relations Q split d T W E R A) p i a
  rw [← he]
  change nativeEquiv m ((sourceEquiv Q split d T W E R A).symm (sourceEquiv Q split d T W E R A _)) = _
  rw [MulEquiv.symm_apply_apply]
  exact Presentation.eval_root (native m) (native_relations m) p i a

@[simp] theorem comparison_torus (t : Parabolics.fixedTorus m) :
    comparison Q split d T W E R A (SourceNormalizer.torus Q split d T t) = t := by
  have he : sourceEquiv Q split d T W E R A (Presentation.torus m t) =
      SourceNormalizer.torus Q split d T t := sourceEval_torus Q split d T W E R A t
  rw [← he]
  change nativeEquiv m ((sourceEquiv Q split d T W E R A).symm (sourceEquiv Q split d T W E R A _)) = _
  rw [MulEquiv.symm_apply_apply]
  exact nativeEval_torus m t

@[simp] theorem comparison_weyl (w : WeylPresentation.Weyl) :
    comparison Q split d T W E R A (SourceSigned.weyl Q split d T W w) = NormalizerPresentation.weyl m w := by
  have he : sourceEquiv Q split d T W E R A (Presentation.weyl m w) =
      SourceSigned.weyl Q split d T W w := sourceEval_weyl Q split d T W E R A w
  rw [← he]
  change nativeEquiv m ((sourceEquiv Q split d T W E R A).symm (sourceEquiv Q split d T W E R A _)) = _
  rw [MulEquiv.symm_apply_apply]
  exact nativeEval_weyl m w

end ReeF4.RootPresentationRecognition.Global
