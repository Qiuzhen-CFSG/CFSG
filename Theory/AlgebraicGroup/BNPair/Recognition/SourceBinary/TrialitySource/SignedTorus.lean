module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.CartanActions
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.Relabeling
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.WeylTorus
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.TorusCharacterAlgebra

/-!
# Signed source torus actions from the positive characters

The longest Weyl word acts on either rank-one image as its own simple
reflection, hence inverts both coroots. Applying it to a positive-root
weight gives the inverse character on the corresponding negative root.
Conjugating the three-root long Weyl word then proves the central
Weyl--torus equation, using only the proved positive weights and torus
multiplication. No additional negative weight or cross-Weyl law is input.

The final transport lemmas combine the two coroot actions in the original
cubic field and its actual fixed subfield. They preserve the Frobenius
shift on the third short root and the restriction of one scalar marking.
The literal quotient application is in TrialitySource/SignedTorusApplication.

Source: Fong--Seitz II §7 and (9.31), printed p.219; GLS3 2.4.7--8.
All calculations include the binary field.
-/

@[expose] public noncomputable section
open Theory.PSL2.SemilinearCoverage
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.RankOnePair
variable {F Y : Type*} [Field F] [CharP F 2] [Group Y]
  {σ : F ≃+* F} (p : RankOnePair σ Y) {n : ℕ} {hn : 0 < n}
  (e : ScalarMarking (binaryParameters n hn) σ)
local notation "K" => ScalarMarking.SourceFixed (σ := σ)
local notation "L" => p.signedRoots e

/-- Relabeling the whole long actor preserves the short coroot word. -/
theorem relabelLong_hA (η : K ≃+* K) (a : (ExtensionField (binaryParameters n hn))ˣ) :
    ((p.relabelLong η).signedRoots e).hA a = (p.signedRoots e).hA a := by
  let t : Fˣ := Units.map e.extension.symm.toMonoidHom a
  have ht : Units.map e.extension.toMonoidHom t = a := by ext; simp [t]
  rw [← ht,hA_parameter,hA_parameter]
  rfl

/-- The longest word inverts the short coroot in the same source pinning. -/
theorem W_hA (a : (ExtensionField (binaryParameters n hn))ˣ) :
    p.dihedral.W ((L).hA a) = (L).hA a⁻¹ := by
  let t : Fˣ := Units.map e.extension.symm.toMonoidHom a
  have ht : Units.map e.extension.toMonoidHom t = a := by ext; simp [t]
  rw [← ht, ← map_inv, p.hA_parameter, p.hA_parameter, p.W_shortMap]
  change p.shortMap (weyl F)*p.shortMap (tor t)*(p.shortMap (weyl F))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, weyl_tor]

/-- The longest word inverts the long coroot in the same source pinning. -/
theorem W_hB (a : (fixedField (binaryParameters n hn))ˣ) :
    p.dihedral.W ((L).hB a) = (L).hB a⁻¹ := by
  let t : Kˣ := Units.map e.fixed.symm.toMonoidHom a
  have ht : Units.map e.fixed.toMonoidHom t = a := by ext; simp [t]
  rw [← ht, ← map_inv, p.hB_parameter, p.hB_parameter, p.W_longMap]
  change p.longMap (weyl K)*p.longMap (tor t)*(p.longMap (weyl K))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, weyl_tor]

/-- The longest word acts by simultaneous inversion on the two parameters. -/
theorem W_torus (a : TorusParameters n hn) :
    p.dihedral.W ((L).torus a) = (L).torus a⁻¹ := by
  change p.dihedral.W ((L).hA a.1*(L).hB a.2) = _
  rw [map_mul,p.W_hA,p.W_hB]
  rfl

/-- Sign change preserves the marked short-root parameter. -/
theorem W_positive_short (i : Fin 3) (x : ExtensionField (binaryParameters n hn)) :
    p.dihedral.W ((L).shortSigned true i x) = (L).shortSigned false i x := by
  obtain ⟨a,rfl⟩ := e.extension.surjective x
  rw [p.signedRoots_short,p.signedRoots_short]
  rfl

/-- Sign change preserves the actual fixed-field parameter. -/
theorem W_positive_long (i : Fin 3) (x : fixedField (binaryParameters n hn)) :
    p.dihedral.W ((L).longSigned true i x) = (L).longSigned false i x := by
  obtain ⟨a,rfl⟩ := e.fixed.surjective x
  rw [p.signedRoots_long,p.signedRoots_long]
  rfl

theorem signed_short_of_positive
    (h : ∀ a i x, (L).torus a*(L).shortSigned true i x*((L).torus a)⁻¹ =
      (L).shortSigned true i ((shortCharacter a i).val*x))
    (a : TorusParameters n hn) (s : Bool) (i : Fin 3) (x : ExtensionField (binaryParameters n hn)) :
    (L).torus a*(L).shortSigned s i x*((L).torus a)⁻¹ =
      (L).shortSigned s i ((if s then (shortCharacter a i).val else
        ((shortCharacter a i)⁻¹).val)*x) := by
  cases s
  · have hh := congrArg p.dihedral.W (h a⁻¹ i x)
    simpa only [map_mul,map_inv,p.W_torus,inv_inv,shortCharacter_inv,p.W_positive_short,Bool.false_eq_true,if_false] using hh
  · exact h a i x

theorem signed_long_of_positive
    (h : ∀ a i x, (L).torus a*(L).longSigned true i x*((L).torus a)⁻¹ =
      (L).longSigned true i ((longCharacter a i).val*x))
    (a : TorusParameters n hn) (s : Bool) (i : Fin 3) (x : fixedField (binaryParameters n hn)) :
    (L).torus a*(L).longSigned s i x*((L).torus a)⁻¹ =
      (L).longSigned s i ((if s then (longCharacter a i).val else
        ((longCharacter a i)⁻¹).val)*x) := by
  cases s
  · have hh := congrArg p.dihedral.W (h a⁻¹ i x)
    simpa only [map_mul,map_inv,p.W_torus,inv_inv,longCharacter_inv,p.W_positive_long,Bool.false_eq_true,if_false] using hh
  · exact h a i x

/-- The short coroot at one is the identity. -/
theorem hA_one : (L).hA 1 = 1 := by
  simpa only [show tor (1 : Fˣ) = 1 from torHom.map_one, map_one] using p.hA_parameter e 1

/-- The long coroot at one is the identity. -/
theorem hB_one : (L).hB 1 = 1 := by
  simpa only [show tor (1 : Kˣ) = 1 from torHom.map_one, map_one] using p.hB_parameter e 1

theorem central_of_long_weights
    (hmul : ∀ a b, (L).torus (a*b) = (L).torus a*(L).torus b)
    (h : ∀ a i x, (L).torus a*(L).longSigned true i x*((L).torus a)⁻¹ =
      (L).longSigned true i ((longCharacter a i).val*x))
    (a : TorusParameters n hn) :
    (L).nB 1*(L).torus a*((L).nB 1)⁻¹ =
      (L).torus (a.1,normUnit a.1/a.2) := by
  let k := longCharacter a 0
  have hpos := p.signed_long_of_positive e h a true 0 1
  have hneg := p.signed_long_of_positive e h a false 0 1
  have hw : (L).torus a*(L).nB 1*((L).torus a)⁻¹ = (L).nB k := by
    change (MulAut.conj ((L).torus a)) ((L).nB 1) = _
    simp only [SignedRoots.nB,map_mul,Units.val_one,inv_one]
    change ((L).torus a*(L).longSigned true 0 1*((L).torus a)⁻¹)*
      ((L).torus a*(L).longSigned false 0 1*((L).torus a)⁻¹)*
      ((L).torus a*(L).longSigned true 0 1*((L).torus a)⁻¹) = _
    rw [hpos,hneg]
    simp only [↓reduceIte,mul_one]
    rfl
  have ht (v : (fixedField (binaryParameters n hn))ˣ) : (L).torus (1,v) = (L).hB v := by
    change (L).hA 1*(L).hB v = _
    rw [p.hA_one,one_mul]
  have hi : ((L).hB k)⁻¹ = (L).hB k⁻¹ := by
    apply inv_eq_of_mul_eq_one_left
    rw [← ht,← ht,← hmul]
    simp only [Prod.mk_mul_mk,one_mul,inv_mul_cancel]
    rw [ht,p.hB_one]
  have hh : (L).nB k = (L).hB k*((L).nB 1)⁻¹ := by
    simp only [SignedRoots.hB,mul_inv_cancel_right]
  rw [hh] at hw
  have hni : ((L).nB 1)⁻¹ = (L).nB 1 := by
    rw [p.nB_one]
    exact p.dihedral.b_inv
  rw [hni] at hw
  have he := congrArg (fun z => ((L).hB k)⁻¹*z*(L).torus a*((L).nB 1)⁻¹) hw
  have he' : (L).nB 1*(L).torus a*((L).nB 1)⁻¹ = ((L).hB k)⁻¹*(L).torus a := by
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel,inv_mul_cancel,one_mul,mul_one] using he.symm
  rw [he',hi,← ht,← hmul]
  congr 1
  apply Prod.ext
  · exact one_mul _
  · change (a.2^2/normUnit a.1)⁻¹*a.2 = normUnit a.1/a.2
    apply Additive.ofMul.injective
    simp only [ofMul_mul,ofMul_div,ofMul_inv,ofMul_pow]
    abel

theorem hA_positive_marked
    (h : ∀ (t : Fˣ) (i : Fin 3) (a : F),
      p.shortMap (tor t)*p.s i a*(p.shortMap (tor t))⁻¹ =
        p.s i (![t.val^2,t.val*(σ t.val)⁻¹*(σ (σ t.val))⁻¹,
          t.val⁻¹*σ t.val*σ (σ t.val)] i*a))
    (t : Fˣ) (i : Fin 3) (a : F) :
    (L).hA (Units.map e.extension.toMonoidHom t)*(L).shortSigned true i (e.extension a)*
      ((L).hA (Units.map e.extension.toMonoidHom t))⁻¹ =
      (L).shortSigned true i
        (e.extension ((![t.val^2,t.val*(σ t.val)⁻¹*(σ (σ t.val))⁻¹,
          t.val*σ t.val*(σ (σ t.val))⁻¹] i)*a)) := by
  rw [p.hA_parameter,p.signedRoots_short,p.signedRoots_short]
  fin_cases i
  · exact h t 0 a
  · exact h t 1 a
  · change p.shortMap (tor t)*p.s 2 (σ a)*(p.shortMap (tor t))⁻¹ =
      p.s 2 (σ ((t.val*σ t.val*(σ (σ t.val))⁻¹)*a))
    rw [h]
    congr 1
    change (t.val⁻¹*σ t.val*σ (σ t.val))*σ a = σ ((t.val*σ t.val*(σ (σ t.val))⁻¹)*a)
    simp only [map_mul,map_inv₀,e.cubic]
    ring

theorem positive_short_of_weights
    (hA : ∀ (t : Fˣ) (i : Fin 3) (a : F),
      p.shortMap (tor t)*p.s i a*(p.shortMap (tor t))⁻¹ =
        p.s i (![t.val^2,t.val*(σ t.val)⁻¹*(σ (σ t.val))⁻¹,
          t.val⁻¹*σ t.val*σ (σ t.val)] i*a))
    (hB : ∀ (u : Kˣ) (i : Fin 3) (a : F),
      (L).hB (Units.map e.fixed.toMonoidHom u)*(L).shortSigned true i (e.extension a)*
        ((L).hB (Units.map e.fixed.toMonoidHom u))⁻¹ =
      (L).shortSigned true i (e.extension ((![u.val.val⁻¹,u.val.val,1] i)*a)))
    (a : TorusParameters n hn) (i : Fin 3) (x : ExtensionField (binaryParameters n hn)) :
    (L).torus a*(L).shortSigned true i x*((L).torus a)⁻¹ =
      (L).shortSigned true i ((shortCharacter a i).val*x) := by
  let t : Fˣ := Units.map e.extension.symm.toMonoidHom a.1
  let u : Kˣ := Units.map e.fixed.symm.toMonoidHom a.2
  have ht : Units.map e.extension.toMonoidHom t = a.1 := by ext; simp [t]
  have hu : Units.map e.fixed.toMonoidHom u = a.2 := by ext; simp [u]
  obtain ⟨z,rfl⟩ := e.extension.surjective x
  have ha : a = (Units.map e.extension.toMonoidHom t,Units.map e.fixed.toMonoidHom u) := by
    rw [ht,hu]
  rw [ha]
  change ((L).hA _*(L).hB _)*(L).shortSigned true i (e.extension z)*((L).hA _*(L).hB _)⁻¹ = _
  rw [mul_inv_rev]
  have he : ∀ A B v : Y, (A*B)*v*(B⁻¹*A⁻¹) = A*(B*v*B⁻¹)*A⁻¹ := by intros; group
  rw [he,hB,p.hA_positive_marked e hA]
  congr 1
  fin_cases i <;>
    simp [shortCharacter,ConcreteBruhat.TorusCoordinates.fixedUnit,
      ConcreteBruhat.TorusCoordinates.frobenius,← e.frobenius,div_eq_mul_inv] <;> ring

theorem positive_long_of_weights
    (hA : ∀ (t : Fˣ) (i : Fin 3) (a : K),
      p.shortMap (tor t)*p.l i a*(p.shortMap (tor t))⁻¹ =
        p.l i (![ (e.norm t.val)⁻¹,e.norm t.val,1] i*a))
    (hB : ∀ (u : Kˣ) (i : Fin 3) (a : K),
      (L).hB (Units.map e.fixed.toMonoidHom u)*(L).longSigned true i (e.fixed a)*
        ((L).hB (Units.map e.fixed.toMonoidHom u))⁻¹ =
      (L).longSigned true i (e.fixed ((![u.val^2,u.val⁻¹,u.val] i)*a)))
    (a : TorusParameters n hn) (i : Fin 3) (x : fixedField (binaryParameters n hn)) :
    (L).torus a*(L).longSigned true i x*((L).torus a)⁻¹ =
      (L).longSigned true i ((longCharacter a i).val*x) := by
  let t : Fˣ := Units.map e.extension.symm.toMonoidHom a.1
  let u : Kˣ := Units.map e.fixed.symm.toMonoidHom a.2
  have ht : Units.map e.extension.toMonoidHom t = a.1 := by ext; simp [t]
  have hu : Units.map e.fixed.toMonoidHom u = a.2 := by ext; simp [u]
  obtain ⟨z,rfl⟩ := e.fixed.surjective x
  have ha : a = (Units.map e.extension.toMonoidHom t,Units.map e.fixed.toMonoidHom u) := by rw [ht,hu]
  have hw (b : K) :
      (L).hA (Units.map e.extension.toMonoidHom t)*(L).longSigned true i (e.fixed b)*
        ((L).hA (Units.map e.extension.toMonoidHom t))⁻¹ =
      (L).longSigned true i (e.fixed ((![ (e.norm t.val)⁻¹,e.norm t.val,1] i)*b)) := by
    rw [p.hA_parameter,p.signedRoots_long,p.signedRoots_long]
    exact hA t i b
  rw [ha]
  change ((L).hA _*(L).hB _)*(L).longSigned true i (e.fixed z)*((L).hA _*(L).hB _)⁻¹ = _
  rw [mul_inv_rev]
  have he : ∀ A B v : Y, (A*B)*v*(B⁻¹*A⁻¹) = A*(B*v*B⁻¹)*A⁻¹ := by intros; group
  rw [he,hB,hw]
  congr 1
  apply Subtype.ext
  fin_cases i <;>
    simp [longCharacter,Triality.Standard.RootPresentationRecognition.normUnit,ConcreteBruhat.TorusCoordinates.restrictUnit,
      ConcreteBruhat.TorusCoordinates.frobenius,ScalarMarking.norm,← e.frobenius,
      div_eq_mul_inv] <;> ring

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.RankOnePair
