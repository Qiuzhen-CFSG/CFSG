module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.TauNormalization
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.TorusCharts
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.TorusAssembly

/-!
# Native and source Weyl normalizer assembly

The native torus charts determine the two explicit finite normalizer tables
from four root characters.  Transport through the supplied signed reflections
then gives the source action on the synchronized Cartan.  The final constructor
uses the literal involution lifts, their square and mixed relations, and their
marked quotient placements to construct `SourceNormalizer.WeylData`.

Source: Fong--Seitz II, Section 10 and GLS3 2.3.2--8, Table 2.4.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open RootPresentationRecognition
open LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open SignedGeometry NormalizerPresentation
variable {m : ℕ}

private theorem native_table_torus (s : Bool) (t : TorusParameter m) :
    reflection m (side s) * torus m t * (reflection m (side s))⁻¹ =
      torus m (NormalizerTables.table m s t) := by
  exact (NormalizerTables.native_equation m s t).symm

private theorem native_pair_positive_action (t : TorusParameter m)
    (i : Fin 4) (x : CoefficientField m) :
    torus m t * SignedCharts.pair m (true,i) x * (torus m t)⁻¹ =
      SignedCharts.pair m (true,i) ((TorusCharts.character t (.inl i) : CoefficientField m)*x) := by
  exact congrArg (fun z : AngularPresentation.Parameter m (.inl i) => (z.val : Model m))
    (TorusCharts.pair_action t i x)

private theorem native_quartet_positive_action (t : TorusParameter m)
    (i : Fin 4) (x y : CoefficientField m) :
    torus m t * SignedCharts.quartet m (true,i) x y * (torus m t)⁻¹ =
      SignedCharts.quartet m (true,i)
        ((TorusCharts.character t (.inr i) : CoefficientField m)*x)
        ((TorusCharts.character t (.inr i) : CoefficientField m)*
          titsEnd m (TorusCharts.character t (.inr i))*y) := by
  exact congrArg (fun z : AngularPresentation.Parameter m (.inr i) => (z.val : Model m))
    (TorusCharts.quartet_action t i x y)

private theorem native_pair_negative_simple_action (t : TorusParameter m)
    (x : CoefficientField m) :
    torus m t * SignedCharts.pair m (false,0) x * (torus m t)⁻¹ =
      SignedCharts.pair m (false,0) ((t.1 : CoefficientField m)⁻¹*x) := by
  simp only [SignedCharts.pair_simple]
  simpa only [signedScale, Bool.false_eq_true, if_false, Units.val_inv_eq_inv_val] using
    torus_linear t false x

private theorem native_quartet_negative_simple_action (t : TorusParameter m)
    (x : CoefficientField m) :
    torus m t * SignedCharts.quartet m (false,0) x 0 * (torus m t)⁻¹ =
      SignedCharts.quartet m (false,0) ((t.2 : CoefficientField m)⁻¹*x) 0 := by
  simp only [SignedCharts.quartet_simple]
  simpa only [signedScale, Bool.false_eq_true, if_false, Units.val_inv_eq_inv_val, mul_zero] using
    torus_suzuki t false x 0

private theorem native_pair_transport (s : Bool) (t : TorusParameter m)
    (r : SignedGeometry.Index) (k : CoefficientField m)
    (hstep : SignedGeometry.step false s r = (true,0))
    (ha : torus m t * SignedCharts.pair m r 1 * (torus m t)⁻¹ = SignedCharts.pair m r k) :
    ((NormalizerTables.table m s t).1 : CoefficientField m) = k := by
  have h := congrArg (MulAut.conj (reflection m (side s))) ha
  simp only [map_mul, map_inv] at h
  change (reflection m (side s)*torus m t*(reflection m (side s))⁻¹) *
    (reflection m (side s)*SignedCharts.pair m r 1*(reflection m (side s))⁻¹) *
    (reflection m (side s)*torus m t*(reflection m (side s))⁻¹)⁻¹ =
      reflection m (side s)*SignedCharts.pair m r k*(reflection m (side s))⁻¹ at h
  rw [native_table_torus, SignedCharts.reflection_pair, SignedCharts.reflection_pair, hstep] at h
  rw [native_pair_positive_action, TorusCharts.character_pair] at h
  simp only [Matrix.cons_val_zero, mul_one] at h
  exact SignedCharts.pair_injective m (true,0) h

private theorem native_quartet_first_injective (x y : CoefficientField m)
    (h : SignedCharts.quartet m (true,0) x 0 = SignedCharts.quartet m (true,0) y 0) : x = y := by
  have h' : PositiveTables.root m (.inr (0 : Fin 4)) (x,0) =
      PositiveTables.root m (.inr (0 : Fin 4)) (y,0) := by
    apply Subtype.ext
    simpa only [PositiveTables.root, SignedCharts.quartet_positive] using h
  have hi := PositiveTables.root_injective (.inr (0 : Fin 4)) h'
  exact congrArg Prod.fst hi

private theorem native_quartet_transport (s : Bool) (t : TorusParameter m)
    (r : SignedGeometry.Index) (k : CoefficientField m)
    (hstep : SignedGeometry.step true s r = (true,0))
    (ha : torus m t * SignedCharts.quartet m r 1 0 * (torus m t)⁻¹ =
      SignedCharts.quartet m r k 0) :
    ((NormalizerTables.table m s t).2 : CoefficientField m) = k := by
  have h := congrArg (MulAut.conj (reflection m (side s))) ha
  simp only [map_mul, map_inv] at h
  change (reflection m (side s)*torus m t*(reflection m (side s))⁻¹) *
    (reflection m (side s)*SignedCharts.quartet m r 1 0*(reflection m (side s))⁻¹) *
    (reflection m (side s)*torus m t*(reflection m (side s))⁻¹)⁻¹ =
      reflection m (side s)*SignedCharts.quartet m r k 0*(reflection m (side s))⁻¹ at h
  rw [native_table_torus, SignedCharts.reflection_quartet, SignedCharts.reflection_quartet, hstep] at h
  rw [native_quartet_positive_action, TorusCharts.character_quartet] at h
  simp only [Matrix.cons_val, Fin.isValue, mul_one, mul_zero] at h
  exact native_quartet_first_injective _ _ h

theorem normalizerTable_linear (t : TorusParameter m) :
    NormalizerTables.table m false t = (t.1⁻¹,t.1*t.2) := by
  apply Prod.ext
  · apply Units.ext
    simpa only [Units.val_inv_eq_inv_val] using
      native_pair_transport false t (false,0) (t.1 : CoefficientField m)⁻¹ (by decide)
        (by simpa only [mul_one] using native_pair_negative_simple_action t 1)
  · apply Units.ext
    simpa only [Units.val_mul] using
      native_quartet_transport false t (true,2) ((t.1 : CoefficientField m)*t.2) (by decide)
        (by simpa [TorusCharts.character_quartet] using
            native_quartet_positive_action t 2 1 0)

theorem normalizerTable_suzuki (t : TorusParameter m) :
    NormalizerTables.table m true t = (t.1*t.2^(2+2*2^m),t.2⁻¹) := by
  apply Prod.ext
  · apply Units.ext
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using
      native_pair_transport true t (true,1) ((t.1 : CoefficientField m)*t.2^(2+2*2^m)) (by decide)
        (by simpa only [TorusCharts.character_pair, Matrix.cons_val_one,
          Matrix.cons_val_zero, mul_one, Units.val_mul, Units.val_pow_eq_pow_val] using
            native_pair_positive_action t 1 1)
  · apply Units.ext
    simpa only [Units.val_inv_eq_inv_val] using
      native_quartet_transport true t (false,0) (t.2 : CoefficientField m)⁻¹ (by decide)
        (by simpa only [mul_one] using native_quartet_negative_simple_action t 1)

private theorem nativeTable_characters_linear (a b : (CoefficientField m)ˣ) :
    NormalizerTables.table m false (torusCharacters (a,b)) =
      torusCharacters (a⁻¹*(b^(1+2^m))⁻¹,b) := by
  rw [normalizerTable_linear]
  apply Prod.ext <;> apply Units.ext
  all_goals
    simp only [torusCharacters, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, mul_pow, mul_inv,
      inv_pow, pow_add, pow_one]
    field_simp

private theorem nativeTable_characters_suzuki (a b : (CoefficientField m)ˣ) :
    NormalizerTables.table m true (torusCharacters (a,b)) =
      torusCharacters (a,a⁻¹*a⁻¹*b⁻¹) := by
  rw [normalizerTable_suzuki]
  apply Prod.ext
  · apply Units.ext
    simp only [torusCharacters, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, mul_pow, mul_inv,
      inv_pow, pow_add, pow_one, pow_mul]
    field_simp
    simp only [← pow_mul]
    ac_rfl
  · apply Units.ext
    simp only [torusCharacters, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul,
      Units.val_inv_eq_inv_val, mul_pow, mul_inv,
      inv_pow, pow_add, pow_one]
    field_simp

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n : ℕ}
  (c : ReeSixHData Q split n m)

private theorem synchronizedTorus_factors_commute (a b : (CoefficientField m)ˣ) :
    Commute (synchronizedLinearTorus Q split c a) (synchronizedSuzukiTorus Q split c b) := by
  have h := (Commute.all (a, (1 : (CoefficientField m)ˣ)) ((1 : (CoefficientField m)ˣ), b)).map
    (synchronizedTorus Q split c)
  simpa only [synchronizedTorus_apply, map_one, mul_one, one_mul] using h

theorem synchronizedTorus_linearReflection (a b : (CoefficientField m)ˣ) :
    (sourceSimpleReflection Q split c false : X ⧸ Q.D) *
      synchronizedTorus Q split c (a,b) *
      (sourceSimpleReflection Q split c false : X ⧸ Q.D)⁻¹ =
    synchronizedTorus Q split c (a⁻¹*(b^(1+2^m))⁻¹,b) := by
  change ((c.reflections 0).val : X ⧸ Q.D) * _ *
    ((c.reflections 0).val : X ⧸ Q.D)⁻¹ = _
  rw [synchronizedTorus_apply]
  calc
    _ = (((c.reflections 0).val : X ⧸ Q.D) * synchronizedLinearTorus Q split c a *
          ((c.reflections 0).val : X ⧸ Q.D)⁻¹) *
        (((c.reflections 0).val : X ⧸ Q.D) * synchronizedSuzukiTorus Q split c b *
          ((c.reflections 0).val : X ⧸ Q.D)⁻¹) := by group
    _ = _ := by
      rw [synchronizedLinearTorus_reflection, synchronizedSuzukiTorus_linearReflection,
        synchronizedTorus_apply, map_mul, map_inv]
      simp only [map_inv]
      rw [mul_assoc, (synchronizedTorus_factors_commute Q split c (b^(1+2^m)) b).symm.inv_right.eq,
        ← mul_assoc]

theorem synchronizedTorus_suzukiReflection (a b : (CoefficientField m)ˣ) :
    (sourceSimpleReflection Q split c true : X ⧸ Q.D) *
      synchronizedTorus Q split c (a,b) *
      (sourceSimpleReflection Q split c true : X ⧸ Q.D)⁻¹ =
    synchronizedTorus Q split c (a,a⁻¹*a⁻¹*b⁻¹) := by
  change ((c.reflections 1).val : X ⧸ Q.D) * _ *
    ((c.reflections 1).val : X ⧸ Q.D)⁻¹ = _
  rw [synchronizedTorus_apply]
  calc
    _ = (((c.reflections 1).val : X ⧸ Q.D) * synchronizedLinearTorus Q split c a *
          ((c.reflections 1).val : X ⧸ Q.D)⁻¹) *
        (((c.reflections 1).val : X ⧸ Q.D) * synchronizedSuzukiTorus Q split c b *
          ((c.reflections 1).val : X ⧸ Q.D)⁻¹) := by group
    _ = _ := by
      rw [synchronizedLinearTorus_suzukiReflection, synchronizedSuzukiTorus_reflection,
        synchronizedTorus_apply]
      simp only [map_mul, map_inv]
      group

theorem normalizedSynchronizedTorus_reflection (s : Bool) (t : TorusParameter m) :
    (sourceSimpleReflection Q split c s : X ⧸ Q.D) *
      normalizedSynchronizedTorus Q split c t *
      (sourceSimpleReflection Q split c s : X ⧸ Q.D)⁻¹ =
    normalizedSynchronizedTorus Q split c (NormalizerTables.table m s t) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := (torusCharacterEquiv (m := m)).surjective t
  change _ = normalizedSynchronizedTorus Q split c
    (NormalizerTables.table m s (torusCharacters (a,b)))
  change (sourceSimpleReflection Q split c s : X ⧸ Q.D) *
    normalizedSynchronizedTorus Q split c (torusCharacters (a,b)) *
    (sourceSimpleReflection Q split c s : X ⧸ Q.D)⁻¹ = _
  cases s
  · rw [nativeTable_characters_linear, normalizedSynchronizedTorus_characters,
      normalizedSynchronizedTorus_characters, ←synchronizedTorus_apply,
      ←synchronizedTorus_apply]
    exact synchronizedTorus_linearReflection Q split c a b
  · rw [nativeTable_characters_suzuki, normalizedSynchronizedTorus_characters,
      normalizedSynchronizedTorus_characters, ←synchronizedTorus_apply,
      ←synchronizedTorus_apply]
    exact synchronizedTorus_suzukiReflection Q split c a b

/-- The supplied reflections provide all source normalizer data once the
positive charts and their torus action have been assembled. -/
def normalizedSynchronizedWeylData (d : SourcePositive.Charts Q split m)
    (T : SourceBorel.TorusData Q split d) (ho : d.orientation = false)
    (hT : T.h = normalizedSynchronizedTorus Q split c) :
    SourceNormalizer.WeylData Q split d T :=
  SourceNormalizer.WeylData.ofFieldRelations Q split d T
    (sourceSimpleReflection Q split c) (sourceSimpleReflection_sq Q split c)
    (sourceSimpleReflection_mixed Q split c)
    (by
      intro s
      rw [ho]
      cases s
      · exact (c.reflections 0).class_eq
      · exact (c.reflections 1).class_eq)
    (by
      intro s t
      rw [hT]
      exact normalizedSynchronizedTorus_reflection Q split c s t)
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
