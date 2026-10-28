module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.RankOneTorus
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.TorusRelations

/-!
# The short Weyl action determined by opposite-root weights

Conjugate the three-root Weyl word using the known weights on a positive
simple root and its negative. The parameterized SL₂ word identifies the
result with a diagonal times the Weyl element. Rearranging gives the
cross-Weyl action on the original torus element. Multiplication by the
short coroot and rank-one Weyl inversion then give the complete arms law.

The final theorem is the literal arms equation of the signed presentation.
It retains the inclusion of the source fixed field and the common scalar
marking. GeometricWeylTorus discharges its weight inputs from the previously
constructed natural action on the original quotient. Keeping this root-word
calculation at RankOnePair avoids expanding the large geometric pinning
while elaborating the group identities.

Source: Fong--Seitz II §7 and (9.31), printed p.219, converted from right
to left conjugation; GLS3 2.4.7--8. The other torus equations are separate
source obligations. Characteristic two includes the binary field.
-/

@[expose] public noncomputable section
open Theory.PSL2.SemilinearCoverage
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
variable {F Y : Type*} [Field F] [CharP F 2] [Group Y]

/-- Opposite-root weights determine conjugation of the actor by the Weyl word. -/
theorem weyl_conj_of_root_weights (f : SL2 F →* Y) (T : Y) (k : Fˣ)
    (hU : ∀ a, T*f (uni a)*T⁻¹ = f (uni (k.val*a)))
    (hV : ∀ a, T*f (weyl F*uni a*(weyl F)⁻¹)*T⁻¹ =
      f (weyl F*uni (k.val⁻¹*a)*(weyl F)⁻¹)) :
    f (weyl F)*T*(f (weyl F))⁻¹ = f (tor k⁻¹)*T := by
  have hword (u : Fˣ) : f (uni u.val)*f (weyl F*uni (u⁻¹).val*(weyl F)⁻¹)*f (uni u.val) =
      f (tor u)*f (weyl F) := by
    rw [← map_mul,← map_mul,weyl_parameter_word,map_mul]
  have ht1 : tor (1 : Fˣ) = 1 := torHom.map_one
  have hh := congrArg (MulAut.conj T) (hword 1)
  simp only [Units.val_one,inv_one,ht1,map_one,one_mul] at hh
  rw [map_mul,map_mul] at hh
  change (T*f (uni 1)*T⁻¹)*(T*f (weyl F*uni 1*(weyl F)⁻¹)*T⁻¹)*
    (T*f (uni 1)*T⁻¹) = T*f (weyl F)*T⁻¹ at hh
  rw [hU,hV,mul_one,mul_one] at hh
  have he : T*f (weyl F)*T⁻¹ = f (tor k)*f (weyl F) :=
    hh.symm.trans (by simpa only [Units.val_inv_eq_inv_val] using hword k)
  have he' := congrArg (fun z => (f (tor k))⁻¹*z*T*(f (weyl F))⁻¹) he
  have hh' : f (weyl F)*T*(f (weyl F))⁻¹ = (f (tor k))⁻¹*T := by
    simpa only [mul_assoc,inv_mul_cancel,inv_mul_cancel_left,mul_inv_cancel,one_mul,mul_one] using he'.symm
  rw [hh']
  have hi : (f (tor k))⁻¹ = f (tor k⁻¹) := (map_inv (f.comp torHom) k).symm
  rw [hi]

open Triality.Standard Triality.Standard.RootPresentationRecognition
open Triality.Standard.ConcreteBruhat.TorusCoordinates
namespace RankOnePair
variable {σ : F ≃+* F} (p : RankOnePair σ Y) {n : ℕ} {hn : 0 < n}
  (e : ScalarMarking (binaryParameters n hn) σ)
local notation "K" => ScalarMarking.SourceFixed (σ := σ)
local notation "L" => RankOnePair.signedRoots p e

/-- The signed simple-root weights give the cross-Weyl action on the long torus. -/
theorem short_weyl_long_torus_of_weights (u : Kˣ)
    (hw : ∀ (positive : Bool) (a : F),
      (L).hB (Units.map e.fixed.toMonoidHom u)*(L).shortSigned positive 0 (e.extension a)*
        ((L).hB (Units.map e.fixed.toMonoidHom u))⁻¹ =
      (L).shortSigned positive 0
        (e.extension ((if positive then u.val.val⁻¹ else u.val.val)*a))) :
    p.dihedral.A (p.longMap (tor u)) =
      p.shortMap (tor (Units.map (ScalarMarking.SourceFixed (σ := σ)).subtype.toMonoidHom u))*
        p.longMap (tor u) := by
  let v : Fˣ := Units.map (ScalarMarking.SourceFixed (σ := σ)).subtype.toMonoidHom u
  have hU (a : F) : p.longMap (tor u)*p.shortMap (uni a)*(p.longMap (tor u))⁻¹ =
      p.shortMap (uni ((v⁻¹).val*a)) := by
    have hh := hw true a
    rw [p.hB_parameter,p.signedRoots_short,p.signedRoots_short] at hh
    rw [Units.val_inv_eq_inv_val]
    change p.longMap (tor u)*p.s 0 a*(p.longMap (tor u))⁻¹ = p.s 0 (u.val.val⁻¹*a)
    exact hh
  have hV (a : F) : p.longMap (tor u)*p.shortMap (weyl F*uni a*(weyl F)⁻¹)*
      (p.longMap (tor u))⁻¹ = p.shortMap (weyl F*uni ((v⁻¹).val⁻¹*a)*(weyl F)⁻¹) := by
    have hh := hw false a
    rw [p.hB_parameter,p.signedRoots_short,p.signedRoots_short] at hh
    change p.longMap (tor u)*p.dihedral.W (p.s 0 a)*(p.longMap (tor u))⁻¹ =
      p.dihedral.W (p.s 0 (u.val.val*a)) at hh
    rw [p.W_shortBase,p.W_shortBase] at hh
    rw [Units.val_inv_eq_inv_val,inv_inv]
    change p.longMap (tor u)*p.shortMap (weyl F*uni a*(weyl F)⁻¹)*(p.longMap (tor u))⁻¹ =
      p.shortMap (weyl F*uni (u.val.val*a)*(weyl F)⁻¹)
    change p.longMap (tor u)*(p.shortMap (weyl F)*p.shortMap (uni a)*(p.shortMap (weyl F))⁻¹)*
      (p.longMap (tor u))⁻¹ = p.shortMap (weyl F)*p.shortMap (uni (u.val.val*a))*(p.shortMap (weyl F))⁻¹ at hh
    simpa only [map_mul,map_inv] using hh
  have hh := weyl_conj_of_root_weights p.shortMap (p.longMap (tor u)) v⁻¹ hU hV
  change p.shortMap (weyl F)*p.longMap (tor u)*(p.shortMap (weyl F))⁻¹ =
    p.shortMap (tor v)*p.longMap (tor u)
  simpa only [inv_inv] using hh

/-- Multiply by the same short coroot to obtain the full source-coordinate law. -/
theorem short_weyl_torus_of_weights (t : Fˣ) (u : Kˣ)
    (hw : ∀ (positive : Bool) (a : F),
      (L).hB (Units.map e.fixed.toMonoidHom u)*(L).shortSigned positive 0 (e.extension a)*
        ((L).hB (Units.map e.fixed.toMonoidHom u))⁻¹ =
      (L).shortSigned positive 0
        (e.extension ((if positive then u.val.val⁻¹ else u.val.val)*a))) :
    p.dihedral.A (p.shortMap (tor t)*p.longMap (tor u)) =
      p.shortMap (tor (Units.map (ScalarMarking.SourceFixed (σ := σ)).subtype.toMonoidHom u/t))*
        p.longMap (tor u) := by
  rw [map_mul,p.short_weyl_long_torus_of_weights e u hw]
  have he : p.dihedral.A (p.shortMap (tor t)) = p.shortMap (tor t⁻¹) := by
    change p.shortMap (weyl F)*p.shortMap (tor t)*(p.shortMap (weyl F))⁻¹ = _
    rw [← map_inv,← map_mul,← map_mul,weyl_tor]
  rw [he,← mul_assoc,← map_mul,← tor_mul]
  have heq : t⁻¹*Units.map (ScalarMarking.SourceFixed (σ := σ)).subtype.toMonoidHom u =
      Units.map (ScalarMarking.SourceFixed (σ := σ)).subtype.toMonoidHom u/t := by
    rw [div_eq_mul_inv,mul_comm]
  rw [heq]

/-- The presentation's exact arms equation follows from signed simple-root weights. -/
theorem arms_of_weights
    (hw : ∀ (u : Kˣ) (positive : Bool) (a : F),
      (L).hB (Units.map e.fixed.toMonoidHom u)*(L).shortSigned positive 0 (e.extension a)*
        ((L).hB (Units.map e.fixed.toMonoidHom u))⁻¹ =
      (L).shortSigned positive 0
        (e.extension ((if positive then u.val.val⁻¹ else u.val.val)*a)))
    (a : TorusParameters n hn) :
    (L).nA 1*(L).torus a*((L).nA 1)⁻¹ =
      (L).torus (fixedUnit (binaryParameters n hn) a.2/a.1,a.2) := by
  let t : Fˣ := Units.map e.extension.symm.toMonoidHom a.1
  let u : Kˣ := Units.map e.fixed.symm.toMonoidHom a.2
  have ht : Units.map e.extension.toMonoidHom t = a.1 := by ext; simp [t]
  have hu : Units.map e.fixed.toMonoidHom u = a.2 := by ext; simp [u]
  have htu : Units.map e.extension.toMonoidHom
      (Units.map (ScalarMarking.SourceFixed (σ := σ)).subtype.toMonoidHom u/t) =
      fixedUnit (binaryParameters n hn) a.2/a.1 := by
    rw [map_div,ht,← hu]
    rfl
  change (L).nA 1*((L).hA a.1*(L).hB a.2)*((L).nA 1)⁻¹ =
    (L).hA (fixedUnit (binaryParameters n hn) a.2/a.1)*(L).hB a.2
  rw [← htu,← ht,← hu,p.nA_one,p.hA_parameter,p.hB_parameter,p.hA_parameter]
  exact p.short_weyl_torus_of_weights e t u (hw u)
end RankOnePair
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
