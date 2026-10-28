module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.TorusParameters
/-!
# Native simple-root characters of the synchronized source torus

The right-conjugation entries of (10.10) give the product torus actions.
After the proved change of unit parameters, left conjugation acts on the
simple linear root by the first native character and on the whole simple
Suzuki root by the second character and its Tits norm.  These are literal
source equations, including the binary field and the nonlinear center.

Source: Fong–Seitz II (1974), printed pp.223–224, (10.10) and (10.12).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open RootPresentationRecognition
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

@[simp] theorem normalizedSynchronizedTorus_characters (a b : (CoefficientField m)ˣ) :
    normalizedSynchronizedTorus Q split c (torusCharacters (a,b)) =
      synchronizedLinearTorus Q split c a * synchronizedSuzukiTorus Q split c b := by
  change synchronizedTorus Q split c
    ((torusCharacterEquiv (m := m)).symm (torusCharacterEquiv (m := m) (a,b))) = _
  rw [MulEquiv.symm_apply_apply, synchronizedTorus_apply]

theorem synchronizedTorus_linear_right (a b : (CoefficientField m)ˣ)
    (x : CoefficientField m) :
    (synchronizedTorus Q split c (a,b))⁻¹ *
      (synchronizedLinearChart Q split c (.ofAdd x) : X ⧸ Q.D) *
        synchronizedTorus Q split c (a,b) =
      synchronizedLinearChart Q split c
        (.ofAdd (((a : CoefficientField m)^2*(b : CoefficientField m)^(1+2^m))⁻¹*x)) := by
  rw [synchronizedTorus_apply]
  calc
    _ = (synchronizedSuzukiTorus Q split c b)⁻¹ *
      ((synchronizedLinearTorus Q split c a)⁻¹ *
        (synchronizedLinearChart Q split c (.ofAdd x) : X ⧸ Q.D) *
        synchronizedLinearTorus Q split c a) * synchronizedSuzukiTorus Q split c b := by group
    _ = _ := by
      rw [synchronizedLinearTorus_simple, synchronizedSuzukiTorus_linear]
      congr 2
      simp only [mul_inv_rev, inv_pow, mul_assoc]

theorem synchronizedTorus_suzuki_right (a b : (CoefficientField m)ˣ)
    (x y : CoefficientField m) :
    (synchronizedTorus Q split c (a,b))⁻¹ *
      (suzukiChart Q split (pinnedInput Q split c) (x,y) : X ⧸ Q.D) *
        synchronizedTorus Q split c (a,b) =
      suzukiChart Q split (pinnedInput Q split c)
        ((a : CoefficientField m)*b*x, ((a : CoefficientField m)*b)*titsEnd m ((a : CoefficientField m)*b)*y) := by
  rw [synchronizedTorus_apply]
  calc
    _ = (synchronizedSuzukiTorus Q split c b)⁻¹ *
      ((synchronizedLinearTorus Q split c a)⁻¹ *
        (suzukiChart Q split (pinnedInput Q split c) (x,y) : X ⧸ Q.D) *
        synchronizedLinearTorus Q split c a) * synchronizedSuzukiTorus Q split c b := by group
    _ = _ := by
      rw [synchronizedLinearTorus_suzuki, synchronizedSuzukiTorus_simple]
      simp only [map_mul]
      congr 2
      ring

theorem normalizedSynchronizedTorus_linear (t : TorusParameter m)
    (x : CoefficientField m) :
    normalizedSynchronizedTorus Q split c t *
      (synchronizedLinearChart Q split c (.ofAdd x) : X ⧸ Q.D) *
        (normalizedSynchronizedTorus Q split c t)⁻¹ =
      synchronizedLinearChart Q split c (.ofAdd ((t.1 : CoefficientField m)*x)) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := (torusCharacterEquiv (m := m)).surjective t
  change normalizedSynchronizedTorus Q split c (torusCharacters (a,b)) * _ *
      (normalizedSynchronizedTorus Q split c (torusCharacters (a,b)))⁻¹ = _
  rw [normalizedSynchronizedTorus_characters, ←synchronizedTorus_apply]
  have h := synchronizedTorus_linear_right Q split c a⁻¹ b⁻¹ x
  have he : synchronizedTorus Q split c (a⁻¹,b⁻¹) =
      (synchronizedTorus Q split c (a,b))⁻¹ := map_inv _ (a,b)
  rw [he,inv_inv] at h
  simpa only [torusCharacterEquiv, torusCharacters, MulEquiv.ofBijective_apply,
    MonoidHom.coe_mk,OneHom.coe_mk, Units.val_inv_eq_inv_val,inv_pow,mul_inv_rev,
    inv_inv,Units.val_mul,Units.val_pow_eq_pow_val,mul_comm] using h

theorem normalizedSynchronizedTorus_suzuki (t : TorusParameter m)
    (x y : CoefficientField m) :
    normalizedSynchronizedTorus Q split c t *
      (suzukiChart Q split (pinnedInput Q split c) (x,y) : X ⧸ Q.D) *
        (normalizedSynchronizedTorus Q split c t)⁻¹ =
      suzukiChart Q split (pinnedInput Q split c)
        ((t.2 : CoefficientField m)*x, (t.2 : CoefficientField m)*titsEnd m t.2*y) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := (torusCharacterEquiv (m := m)).surjective t
  change normalizedSynchronizedTorus Q split c (torusCharacters (a,b)) * _ *
      (normalizedSynchronizedTorus Q split c (torusCharacters (a,b)))⁻¹ = _
  rw [normalizedSynchronizedTorus_characters, ←synchronizedTorus_apply]
  have h := synchronizedTorus_suzuki_right Q split c a⁻¹ b⁻¹ x y
  have he : synchronizedTorus Q split c (a⁻¹,b⁻¹) =
      (synchronizedTorus Q split c (a,b))⁻¹ := map_inv _ (a,b)
  rw [he,inv_inv] at h
  simpa only [torusCharacterEquiv, torusCharacters, MulEquiv.ofBijective_apply,
    MonoidHom.coe_mk,OneHom.coe_mk, Units.val_inv_eq_inv_val,Units.val_mul,mul_inv] using h
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
