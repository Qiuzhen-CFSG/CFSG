module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.CartanActions
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.CubicCoefficient

/-!
# Covariance from the two actual coroot actions

Conjugate the full four-factor mixed product by the short and long
coroots. Their six positive characters transform each of the first three
factors to the same factor at the transformed input parameters. Cancel
those common factors and use faithfulness of the highest root to identify
its coefficient. Substituting inverse units gives Fong--Seitz (9.31) in
the source convention. This uses a group equality, not quotient coordinates.

TensorPositiveApplication discharges every action and product premise on
the literal source quotient. The calculation uses the given extension
field, its same fixed-field inclusion and its cubic norm, without any
restriction on the size of the fixed field.

Source: Fong--Seitz II (9.29)(ii), (9.31), printed p.219.
-/

@[expose] public noncomputable section
open Theory.PSL2.SemilinearCoverage
open Triality.Standard Triality.Standard.RootPresentationRecognition
open Theory.GroupTheory
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
variable {F Y : Type*} [Field F] [CharP F 2] [Group Y]
  {σ : F ≃+* F} (p : RankOnePair σ Y) {n : ℕ} {hn : 0 < n}
  (e : ScalarMarking (binaryParameters n hn) σ)
local notation "K" => ScalarMarking.SourceFixed (σ := σ)
variable (g : F → (ScalarMarking.SourceFixed (σ := σ)) → (ScalarMarking.SourceFixed (σ := σ)))
  (hmixed : ∀ (a : F) (b : (ScalarMarking.SourceFixed (σ := σ))), (p.l 0 b)⁻¹*(p.s 0 a)⁻¹*p.l 0 b*p.s 0 a =
    p.s 1 (a*b.val)*p.s 2 (σ a*σ (σ a)*b.val)*p.l 1 (e.norm a*b)*p.l 2 (g a b))
  (hf : Function.Injective (p.l 2))
  (hAs : ∀ (t : Fˣ) (r : Fin 3) (a : F),
    p.shortMap (tor t)*p.s r a*(p.shortMap (tor t))⁻¹ =
      p.s r (![t.val^2,t.val*(σ t.val)⁻¹*(σ (σ t.val))⁻¹,t.val⁻¹*σ t.val*σ (σ t.val)] r*a))
  (hAl : ∀ (t : Fˣ) (r : Fin 3) (a : (ScalarMarking.SourceFixed (σ := σ))),
    p.shortMap (tor t)*p.l r a*(p.shortMap (tor t))⁻¹ =
      p.l r (![(e.norm t.val)⁻¹,e.norm t.val,1] r*a))
  (hBs : ∀ (t : (ScalarMarking.SourceFixed (σ := σ))ˣ) (r : Fin 3) (a : F),
    p.longMap (tor t)*p.s r a*(p.longMap (tor t))⁻¹ =
      p.s r (![t.val.val⁻¹,t.val.val,1] r*a))
  (hBl : ∀ (t : (ScalarMarking.SourceFixed (σ := σ))ˣ) (r : Fin 3) (a : (ScalarMarking.SourceFixed (σ := σ))),
    p.longMap (tor t)*p.l r a*(p.longMap (tor t))⁻¹ =
      p.l r (![t.val^2,t.val⁻¹,t.val] r*a))

include hmixed hf hAs hAl hBs hBl in
theorem mixed_torus_coefficient (t : Fˣ) (u : Kˣ) (a : F) (b : K) :
    g (t.val^2*(u.val.val⁻¹*a)) ((e.norm t.val)⁻¹*(u.val^2*b)) = u.val*g a b := by
  let A := MulAut.conj (p.shortMap (tor t))
  let B := MulAut.conj (p.longMap (tor u))
  have hAs' (r : Fin 3) (x : F) : A (p.s r x) =
      p.s r (![t.val^2,t.val*(σ t.val)⁻¹*(σ (σ t.val))⁻¹,t.val⁻¹*σ t.val*σ (σ t.val)] r*x) := hAs t r x
  have hAl' (r : Fin 3) (x : K) : A (p.l r x) =
      p.l r (![(e.norm t.val)⁻¹,e.norm t.val,1] r*x) := hAl t r x
  have hBs' (r : Fin 3) (x : F) : B (p.s r x) =
      p.s r (![u.val.val⁻¹,u.val.val,1] r*x) := hBs u r x
  have hBl' (r : Fin 3) (x : K) : B (p.l r x) =
      p.l r (![u.val^2,u.val⁻¹,u.val] r*x) := hBl u r x
  have hh := congrArg A (congrArg B (hmixed a b))
  simp only [map_mul,map_inv,hBs',hBl',hAs',hAl',
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.succ_zero_eq_one,one_mul] at hh
  let a' := t.val^2*(u.val.val⁻¹*a)
  let b' := (e.norm t.val)⁻¹*(u.val^2*b)
  have ht := t.ne_zero
  have ht1 := (map_ne_zero σ).mpr ht
  have ht2 := (map_ne_zero σ).mpr ht1
  have hu := u.ne_zero
  have hu' : u.val.val ≠ 0 := Subtype.coe_ne_coe.mpr hu
  have hN := norm_ne_zero e ht
  have huσ : σ u.val.val = u.val.val := u.val.property
  have hc : a'*b'.val = (t.val*(σ t.val)⁻¹*(σ (σ t.val))⁻¹)*(u.val.val*(a*b.val)) := by
    simp only [a',b',Subfield.coe_mul,Subfield.coe_inv,SubmonoidClass.coe_pow,ScalarMarking.norm]
    field_simp
  have hd : σ a'*σ (σ a')*b'.val =
      (t.val⁻¹*σ t.val*σ (σ t.val))*(σ a*σ (σ a)*b.val) := by
    simp only [a',b',Subfield.coe_mul,Subfield.coe_inv,SubmonoidClass.coe_pow,ScalarMarking.norm,
      map_mul,map_pow,map_inv₀,huσ]
    field_simp
  have he : e.norm a'*b' = e.norm t.val*(u.val⁻¹*(e.norm a*b)) := by
    simp only [a',b',pow_two,norm_mul,norm_inv,norm_fixed]
    field_simp
  have hh' : (p.l 0 b')⁻¹*(p.s 0 a')⁻¹*p.l 0 b'*p.s 0 a' =
      p.s 1 (a'*b'.val)*p.s 2 (σ a'*σ (σ a')*b'.val)*p.l 1 (e.norm a'*b')*p.l 2 (u.val*g a b) := by
    rw [hc,hd,he]
    exact hh
  rw [hmixed] at hh'
  exact hf (mul_left_cancel hh')

include hmixed hf hAs hAl hBs hBl in
/-- Covariance of the highest mixed coefficient follows by conjugating
its actual four-factor product by the two source coroots. -/
theorem coefficient_covariance_of_weights : CoefficientCovariance e g := by
  intro l μ hl hμ a b
  let t : Fˣ := (Units.mk0 μ hμ)⁻¹
  let u : Kˣ := (Units.mk0 l hl)⁻¹
  have hh := mixed_torus_coefficient p e g hmixed hf hAs hAl hBs hBl t u a b
  have he : t.val^2*(u.val.val⁻¹*a) = l.val/μ^2*a := by
    simp only [t,u,Units.val_inv_eq_inv_val,Units.val_mk0,Subfield.coe_inv,inv_inv,div_eq_mul_inv,inv_pow]
    ring
  have he' : (e.norm t.val)⁻¹*(u.val^2*b) = l⁻¹^2*e.norm μ*b := by
    simp only [t,u,Units.val_inv_eq_inv_val,Units.val_mk0,norm_inv,inv_inv]
    ring
  rw [he,he'] at hh
  exact hh

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
