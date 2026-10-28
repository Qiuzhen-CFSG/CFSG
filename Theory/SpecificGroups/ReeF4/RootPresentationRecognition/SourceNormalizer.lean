module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.NormalizerTables
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourceBorel

/-!
# Faithful torus--Weyl evaluation on the same marked source quotient

The literal source lifts are involutions in N satisfying the eighth-power
relation there. Their placements in the original marked Weyl quotient and
its proved sixteen-element coordinates make the constructed Weyl evaluation
faithful. The two finite full-torus action equations then construct evaluation
of the native normalizer presentation. Passing to the SAME N/(B ∩ N) kills
the Weyl part of its kernel; faithful full-Cartan parameters kill the rest.
Coverage of that quotient and the entire Cartan proves surjectivity onto N.

The resulting native/source normalizer comparison retains both simple lifts
and agrees with the already constructed Borel comparison on their entire
intersection. All m, including zero, are covered. The source owner still must
construct these local lifts and verify their finite equations. No full-model
map or global presentation kernel is assumed or proved here; signed-root
Bruhat reduction and the full marked comparison remain required.

Source: GLS3 2.3.2--5, `refs/KGroup/GLS3/chapter2.tex`; the literal finite
quotient of DGS, *Groups and Graphs*, Theorem D, printed p.224.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.SourceNormalizer
open Subgroup WeylPresentation NormalizerPresentation
open Parabolics CentralCovers.OddPrimary.Order
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)
variable {m : ℕ} (d : SourcePositive.Charts Q split m) (T : SourceBorel.TorusData Q split d)

/-- The original orientation is retained for the two literal simple lifts. -/
def index (orientation s : Bool) : Fin 2 := if (if s then !orientation else orientation) then 1 else 0

/-- The entire original Cartan, with parameters in the actual native torus. -/
def torus : fixedTorus m →* X ⧸ Q.D := T.h.comp (fixedTorusEquiv m).symm.toMonoidHom

/-- Only literal reflection, mixed-Weyl, and two full-torus action equations.
The eighth-power relation is imposed in N itself, not only in N/H. -/
structure WeylData where
  n : Bool → Q.tits.N
  square : ∀ s, n s ^ 2 = 1
  mixed : (n false * n true)^8 = 1
  placement : ∀ s, QuotientGroup.mk' _ (n s) = Q.simple (index d.orientation s)
  action : ∀ s t, (n s : X ⧸ Q.D) * torus Q split d T t * (n s : X ⧸ Q.D)⁻¹ =
    torus Q split d T (NormalizerPresentation.action m (simple s) t)

/-- Construct the local Weyl data directly from the prescribed two-parameter
field-unit equations. No native-to-source normalizer map is supplied. -/
def WeylData.ofFieldRelations (n : Bool → Q.tits.N)
    (hsq : ∀ s, n s ^ 2 = 1) (hmix : (n false * n true)^8 = 1)
    (hp : ∀ s, QuotientGroup.mk' _ (n s) = Q.simple (index d.orientation s))
    (ha : ∀ s (a : (CoefficientField m)ˣ × (CoefficientField m)ˣ),
      (n s : X ⧸ Q.D) * T.h a * (n s : X ⧸ Q.D)⁻¹ = T.h (NormalizerTables.table m s a)) :
    WeylData Q split d T where
  n := n
  square := hsq
  mixed := hmix
  placement := hp
  action s t := by
    obtain ⟨a,rfl⟩ := (fixedTorusEquiv m).surjective t
    simpa only [torus, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, NormalizerTables.table, NormalizerTables.fieldAction_apply] using ha s a

variable (W : WeylData Q split d T)

def weyl : WeylPresentation.Weyl →* Q.tits.N := lift W.n W.square W.mixed

@[simp] theorem weyl_simple (s : Bool) : weyl Q split d T W (simple s) = W.n s :=
  lift_simple _ _ _ s

/-- The Weyl-coordinate map is constructed from the same original quotient. -/
def quotientWeyl : WeylPresentation.Weyl →* RootCoordinates.Weyl Q :=
  (QuotientGroup.mk' _).comp (weyl Q split d T W)

@[simp] theorem quotientWeyl_simple (s : Bool) :
    quotientWeyl Q split d T W (simple s) = Q.simple (index d.orientation s) := by
  change QuotientGroup.mk' _ (weyl Q split d T W (simple s)) = _
  rw [weyl_simple, W.placement]

theorem quotientWeyl_surjective : Function.Surjective (quotientWeyl Q split d T W) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← Q.tits.quotient_generate]
  apply (closure_le _).mpr
  intro x hx
  obtain ⟨i,rfl⟩ := Q.simple_range.symm ▸ hx
  have hi : ∃ s, index d.orientation s = i := by
    cases ho : d.orientation <;> fin_cases i
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩
    · exact ⟨true,rfl⟩
    · exact ⟨false,rfl⟩
  obtain ⟨s,rfl⟩ := hi
  exact ⟨simple s,quotientWeyl_simple Q split d T W s⟩

/-- Both marked Weyl groups have order sixteen by proved dihedral coordinates. -/
theorem quotientWeyl_bijective : Function.Bijective (quotientWeyl Q split d T W) := by
  apply (quotientWeyl_surjective Q split d T W).bijective_of_nat_card_le
  rw [DihedralGroup.nat_card, weyl_card, d.rotation_eight]

/-- In particular the literal source lifts generate a genuine complement. -/
theorem weyl_injective : Function.Injective (weyl Q split d T W) := by
  intro a b he
  apply (quotientWeyl_bijective Q split d T W).injective
  exact congrArg (QuotientGroup.mk' _) he

def torusN : fixedTorus m →* Q.tits.N :=
  (torus Q split d T).codRestrict _ (fun t => by
    have ht : torus Q split d T t ∈ T.h.range := ⟨(fixedTorusEquiv m).symm t,rfl⟩
    rw [T.range_eq] at ht
    exact ht.2)

@[simp] theorem torusN_coe (t : fixedTorus m) :
    (torusN Q split d T t : X ⧸ Q.D) = torus Q split d T t := rfl

theorem torusN_injective : Function.Injective (torusN Q split d T) := by
  intro a b he
  apply (fixedTorusEquiv m).symm.injective
  exact T.injective (congrArg Subtype.val he)

@[simp] theorem torusN_quotient (t : fixedTorus m) :
    QuotientGroup.mk' _ (torusN Q split d T t) = (1 : RootCoordinates.Weyl Q) := by
  apply (QuotientGroup.eq_one_iff _).mpr
  have ht : torus Q split d T t ∈ T.h.range := ⟨(fixedTorusEquiv m).symm t,rfl⟩
  rw [T.range_eq] at ht
  exact ht

theorem compatible (w : WeylPresentation.Weyl) :
    (torusN Q split d T).comp (NormalizerPresentation.action m w).toMonoidHom =
      (MulAut.conj (weyl Q split d T W w)).toMonoidHom.comp (torusN Q split d T) := by
  apply action_compatible
  intro s t
  apply Subtype.ext
  change torus Q split d T (NormalizerPresentation.action m (simple s) t) = _
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, weyl_simple, torusN_coe] using (W.action s t).symm

/-- The finite torus/Weyl equations construct evaluation on the same N. -/
def eval : NormalizerPresentation.Presentation m →* Q.tits.N :=
  SemidirectProduct.lift (torusN Q split d T) (weyl Q split d T W) (compatible Q split d T W)

@[simp] theorem eval_apply (a : NormalizerPresentation.Presentation m) :
    eval Q split d T W a = torusN Q split d T a.left * weyl Q split d T W a.right := rfl

@[simp] theorem eval_torus (t : fixedTorus m) :
    eval Q split d T W (SemidirectProduct.inl t) = torusN Q split d T t :=
  SemidirectProduct.lift_inl ..

@[simp] theorem eval_weyl (w : WeylPresentation.Weyl) :
    eval Q split d T W (SemidirectProduct.inr w) = weyl Q split d T W w :=
  SemidirectProduct.lift_inr ..

/-- The same original Weyl quotient detects the right factor of evaluation. -/
theorem eval_quotient (a : NormalizerPresentation.Presentation m) :
    QuotientGroup.mk' _ (eval Q split d T W a) = quotientWeyl Q split d T W a.right := by
  rw [eval_apply,map_mul,torusN_quotient,one_mul]
  rfl

/-- Weyl-coordinate injectivity and faithful full-Cartan parameters kill the
constructed evaluation kernel; neither is a global faithfulness assumption. -/
theorem eval_injective : Function.Injective (eval Q split d T W) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  have hw : a.right = 1 := by
    apply (quotientWeyl_bijective Q split d T W).injective
    rw [← eval_quotient, ha, map_one, map_one]
  have ht : a.left = 1 := by
    apply torusN_injective Q split d T
    rw [eval_apply,hw,map_one,mul_one] at ha
    exact ha.trans (map_one _).symm
  exact SemidirectProduct.ext ht hw

/-- Generation of N/H and coverage of the entire H give coverage of N. -/
theorem eval_surjective : Function.Surjective (eval Q split d T W) := by
  intro n
  obtain ⟨w,hw⟩ := quotientWeyl_surjective Q split d T W (QuotientGroup.mk' _ n)
  have hh : n * (weyl Q split d T W w)⁻¹ ∈ (Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' _ (n * (weyl Q split d T W w)⁻¹) = (1 : RootCoordinates.Weyl Q)
    rw [map_mul,map_inv,← hw]
    exact mul_inv_cancel _
  have hh' : (n : X ⧸ Q.D) * (weyl Q split d T W w : X ⧸ Q.D)⁻¹ ∈ T.h.range := by
    rw [T.range_eq]
    exact hh
  obtain ⟨t,ht⟩ := hh'
  refine ⟨⟨fixedTorusEquiv m t,w⟩,?_⟩
  apply Subtype.ext
  change T.h ((fixedTorusEquiv m).symm (fixedTorusEquiv m t)) *
    (weyl Q split d T W w : X ⧸ Q.D) = n
  rw [MulEquiv.symm_apply_apply, ht, inv_mul_cancel_right]

/-- The proved normalizer presentation on the literal original quotient. -/
def sourceEquiv : NormalizerPresentation.Presentation m ≃* Q.tits.N :=
  MulEquiv.ofBijective (eval Q split d T W)
    ⟨eval_injective Q split d T W,eval_surjective Q split d T W⟩

/-- Both constructed evaluations identify the complete native and source N. -/
def comparison : SectionGeometry.BNPair.normalizerWords m ≃* Q.tits.N :=
  (NormalizerPresentation.nativeEquiv m).symm.trans (sourceEquiv Q split d T W)

/-- The normalizer comparison retains the same entire Cartan map as the Borel. -/
theorem comparison_torus (t : fixedTorus m) :
    (comparison Q split d T W ⟨t, SectionGeometry.BNPair.fixedTorus_le_normalizerWords m t.property⟩ :
      X ⧸ Q.D) = torus Q split d T t := by
  have hn : NormalizerPresentation.nativeEquiv m (SemidirectProduct.inl t) =
      ⟨t, SectionGeometry.BNPair.fixedTorus_le_normalizerWords m t.property⟩ := by
    apply Subtype.ext
    exact NormalizerPresentation.nativeEval_torus m t
  rw [← hn]
  change (sourceEquiv Q split d T W
    ((NormalizerPresentation.nativeEquiv m).symm
      (NormalizerPresentation.nativeEquiv m (SemidirectProduct.inl t))) : X ⧸ Q.D) = _
  rw [MulEquiv.symm_apply_apply]
  exact congrArg Subtype.val (eval_torus Q split d T W t)

/-- All sixteen chosen Weyl words, not only their quotient classes, are fixed. -/
theorem comparison_weyl (w : WeylPresentation.Weyl) :
    (comparison Q split d T W
      ⟨NormalizerPresentation.weyl m w, NormalizerPresentation.weyl_le_normalizerWords m
        (by rw [← NormalizerPresentation.weyl_range]; exact ⟨w,rfl⟩)⟩ : X ⧸ Q.D) =
      (weyl Q split d T W w : X ⧸ Q.D) := by
  have hn : NormalizerPresentation.nativeEquiv m (SemidirectProduct.inr w) =
      ⟨NormalizerPresentation.weyl m w, NormalizerPresentation.weyl_le_normalizerWords m
        (by rw [← NormalizerPresentation.weyl_range]; exact ⟨w,rfl⟩)⟩ := by
    apply Subtype.ext
    exact NormalizerPresentation.nativeEval_weyl m w
  rw [← hn]
  change (sourceEquiv Q split d T W
    ((NormalizerPresentation.nativeEquiv m).symm
      (NormalizerPresentation.nativeEquiv m (SemidirectProduct.inr w))) : X ⧸ Q.D) = _
  rw [MulEquiv.symm_apply_apply]
  exact congrArg Subtype.val (eval_weyl Q split d T W w)

@[simp] theorem comparison_simple (s : Bool) :
    comparison Q split d T W
      (SectionGeometry.BNPair.simpleLift m (NormalizerPresentation.side s)) = W.n s := by
  apply Subtype.ext
  have he := comparison_weyl Q split d T W (simple s)
  simpa only [NormalizerPresentation.weyl_simple, weyl_simple, SectionGeometry.BNPair.simpleLift] using he

/-- The constructed Borel and normalizer maps agree on their whole overlap. -/
theorem comparison_borel (E : SourceAngular.Equations Q split d) (t : fixedTorus m) :
    (comparison Q split d T W ⟨t, SectionGeometry.BNPair.fixedTorus_le_normalizerWords m t.property⟩ :
      X ⧸ Q.D) =
    (SourceBorel.comparison Q split d E T ⟨t, fixedTorus_le_borel m t.property⟩ : X ⧸ Q.D) := by
  rw [comparison_torus, SourceBorel.comparison_torus]
  rfl

/-- Literal source Weyl coordinates of every full-normalizer element. -/
theorem comparison_quotient (n : SectionGeometry.BNPair.normalizerWords m) :
    QuotientGroup.mk' _ (comparison Q split d T W n) =
      quotientWeyl Q split d T W ((NormalizerPresentation.nativeEquiv m).symm n).right :=
  eval_quotient Q split d T W _

/-- Compatibility is on the entire literal Borel/normalizer intersection. -/
theorem overlap_compatible (E : SourceAngular.Equations Q split d)
    (b : borel m) (n : SectionGeometry.BNPair.normalizerWords m)
    (he : (b : Model m) = n) :
    (SourceBorel.comparison Q split d E T b : X ⧸ Q.D) =
      (comparison Q split d T W n : X ⧸ Q.D) := by
  have ht : (b : Model m) ∈ fixedTorus m := by
    rw [← SectionGeometry.BNPair.borel_inf_normalizerWords]
    exact ⟨b.property, he.symm ▸ n.property⟩
  have hh := (comparison_borel Q split d T W E ⟨b,ht⟩).symm
  change (SourceBorel.comparison Q split d E T b : X ⧸ Q.D) =
    (comparison Q split d T W
      ⟨b,SectionGeometry.BNPair.fixedTorus_le_normalizerWords m ht⟩ : X ⧸ Q.D) at hh
  have hn : (⟨b,SectionGeometry.BNPair.fixedTorus_le_normalizerWords m ht⟩ :
      SectionGeometry.BNPair.normalizerWords m) = n := Subtype.ext he
  rw [hn] at hh
  exact hh

/-- No extra Cartan elements appear under the normalizer comparison. -/
theorem comparison_mem_borel_iff (n : SectionGeometry.BNPair.normalizerWords m) :
    (comparison Q split d T W n : X ⧸ Q.D) ∈ Q.tits.B ↔ (n : Model m) ∈ borel m := by
  constructor
  · intro hn
    have hh : (comparison Q split d T W n : X ⧸ Q.D) ∈ T.h.range := by
      rw [T.range_eq]
      exact ⟨hn,(comparison Q split d T W n).property⟩
    obtain ⟨t,ht⟩ := hh
    let a := fixedTorusEquiv m t
    have he : comparison Q split d T W
        ⟨a,SectionGeometry.BNPair.fixedTorus_le_normalizerWords m a.property⟩ =
          comparison Q split d T W n := by
      apply Subtype.ext
      rw [comparison_torus]
      change T.h ((fixedTorusEquiv m).symm (fixedTorusEquiv m t)) = _
      rw [MulEquiv.symm_apply_apply]
      exact ht
    have he' := congrArg Subtype.val ((comparison Q split d T W).injective he)
    exact he' ▸ fixedTorus_le_borel m a.property
  · intro hn
    have ht : (n : Model m) ∈ fixedTorus m := by
      rw [← SectionGeometry.BNPair.borel_inf_normalizerWords]
      exact ⟨hn,n.property⟩
    have he := comparison_torus Q split d T W ⟨n,ht⟩
    change (comparison Q split d T W n : X ⧸ Q.D) = _ at he
    rw [he]
    have hh : torus Q split d T ⟨n,ht⟩ ∈ T.h.range := ⟨_,rfl⟩
    rw [T.range_eq] at hh
    exact hh.1

end ReeF4.RootPresentationRecognition.SourceNormalizer
