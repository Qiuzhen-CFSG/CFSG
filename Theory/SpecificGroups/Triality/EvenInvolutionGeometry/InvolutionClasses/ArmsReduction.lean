module

public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.ArmsReduction.Transport
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.ArmsReduction.Weyl
/-!
# Arms-radical involutions in genuine binary triality

Write the coordinates as (c,d;b,e,f). When b is nonzero, a short-root shear
kills c and the involution square forces e to vanish. A fixed Weyl word then
moves d to the first central short root; the pure-long case reduces to the
highest root. When b vanishes, a central reflection handles nonzero c, and
trace-pairing surjectivity handles nonzero d. The remaining long-root pairs
are collected directly. Every conjugacy occurs in the actual carrier.

Source: Aschbacher–Smith 16.1.4(1), printed p.1171; GLS3 §§2.4–2.6.
-/

public section
open Triality.Standard.RadicalCoordinates Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.RadicalCoordinates.LeviCommutators
namespace Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
open Parabolics ConcreteBruhat Parabolics.CentralRootSquare
noncomputable section

private theorem conjugate_mul {G : Type*} [Group G] (g x y : G) :
    g * (x*y) * g⁻¹ = (g*x*g⁻¹) * (g*y*g⁻¹) := by group

private theorem central_factorization (P : Parameters) (hp : P.prime=2)
    (v : RootOrbitParameters P .central) :
    (coordinates P hp v).val = short P hp 0 (v.1 0) * short P hp 1 (v.1 1) *
      short P hp 2 (v.1 2) * long P hp 1 (v.2 0) * long P hp 2 (v.2 1) := by
  rw [coordinates_val,rootElement_factorization]
  simp [extendOrbit]

private theorem central_image (P : Parameters) (hp : P.prime=2)
    (c d : ExtensionField P) (e f : fixedField P) :
    weylRepresentative P hp (.sr 1) * (armsCoordinates P hp (![c,d],![0,e,f])).val *
      (weylRepresentative P hp (.sr 1))⁻¹ =
      (coordinates P hp (![c,0,d],![f,e])).val := by
  rw [armsCoordinates_factorization,central_factorization]
  change weylRepresentative P hp (.sr 1) *
    (long P hp 0 0 * short P hp 1 c * short P hp 2 d * long P hp 1 e * long P hp 2 f) *
      (weylRepresentative P hp (.sr 1))⁻¹ =
    short P hp 0 c * short P hp 1 0 * short P hp 2 d * long P hp 1 f * long P hp 2 e
  simp only [long_zero,short_zero,one_mul,mul_one]
  rw [conjugate_mul,conjugate_mul,conjugate_mul,central_short_one,central_short_two,
    central_long_one,central_long_two]
  rw [mul_assoc _ _ (long P hp 1 f), (highest_commute_long P hp e 1 f).eq,
    ← mul_assoc]

private theorem rotation_image (P : Parameters) (hp : P.prime=2)
    (d : ExtensionField P) (b f : fixedField P) :
    weylRepresentative P hp (.r 5) * (armsCoordinates P hp (![0,d],![b,0,f])).val *
      (weylRepresentative P hp (.r 5))⁻¹ =
      (coordinates P hp (![fieldFrobenius P d,0,0],![f,b])).val := by
  rw [armsCoordinates_factorization,central_factorization]
  change weylRepresentative P hp (.r 5) *
    (long P hp 0 b * short P hp 1 0 * short P hp 2 d * long P hp 1 0 * long P hp 2 f) *
      (weylRepresentative P hp (.r 5))⁻¹ =
    short P hp 0 (fieldFrobenius P d) * short P hp 1 0 * short P hp 2 0 *
      long P hp 1 f * long P hp 2 b
  simp only [long_zero,short_zero,mul_one]
  rw [conjugate_mul,conjugate_mul,rotation_long_zero,rotation_short_two,rotation_long_two]
  rw [(highest_commute_short P hp b 0 (fieldFrobenius P d)).eq,mul_assoc,
    (highest_commute_long P hp b 1 f).eq,← mul_assoc]

private theorem long_mem_highest (P : Parameters) (hp : P.prime=2) (f : fixedField P) :
    long P hp 2 f ∈ highestRoot P := by
  refine ⟨longElementary P hp 2 f,?_,rfl⟩
  change elementaryInclusion P (longElementary P hp 2 f) ∈ splitHighestRoot P
  rw [longElementary_val]
  exact ⟨Multiplicative.ofAdd f.val,rfl⟩

private theorem long_inv (P : Parameters) (hp : P.prime=2) (i : Fin 3) (t : fixedField P) :
    (long P hp i t)⁻¹ = long P hp i t := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  apply inv_eq_of_mul_eq_one_left
  rw [← long_add,CharTwo.add_self_eq_zero,long_zero]

private theorem conjugate_of_exchange {G : Type*} [Group G] (x y z : G)
    (h : x*y = y*x*z) (hc : Commute z x) : x*y*x⁻¹ = y*z := by
  rw [h,mul_assoc y x z,← hc.eq]
  group

private theorem long_pair_zero (P : Parameters) (hp : P.prime=2)
    (b f : fixedField P) (hb : b≠0) :
    IsConj (long P hp 0 b * long P hp 2 f) (long P hp 0 b) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  let t := f / b
  have ht : b*t=f := mul_div_cancel₀ f hb
  have hex : long P hp 1 t * long P hp 0 b =
      long P hp 0 b * long P hp 1 t * long P hp 2 (b*t) := by
    have h := congrArg (fun x => x * (long P hp 2 (b*t))⁻¹)
      (long_zero_one_exchange P hp b t).symm
    simp only [mul_inv_cancel_right] at h
    rw [long_inv P hp 2 (b*t)] at h
    exact h
  refine isConj_iff.mpr ⟨long P hp 1 t,?_⟩
  rw [conjugate_mul,conjugate_of_exchange _ _ _ hex (highest_commute_long P hp (b*t) 1 t)]
  rw [← (highest_commute_long P hp f 1 t).eq]
  simp only [mul_inv_cancel_right]
  rw [mul_assoc,← long_add,ht,CharTwo.add_self_eq_zero,long_zero,mul_one]

private theorem long_pair_one (P : Parameters) (hp : P.prime=2)
    (e f : fixedField P) (he : e≠0) :
    IsConj (long P hp 1 e * long P hp 2 f) (long P hp 1 e) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  let t := f / e
  have ht : t*e=f := div_mul_cancel₀ f he
  refine isConj_iff.mpr ⟨long P hp 0 t,?_⟩
  rw [conjugate_mul,conjugate_of_exchange _ _ _ (long_zero_one_exchange P hp t e)
    (highest_commute_long P hp (t*e) 0 t)]
  rw [← (highest_commute_long P hp f 0 t).eq]
  simp only [mul_inv_cancel_right]
  rw [mul_assoc,← long_add,ht,CharTwo.add_self_eq_zero,long_zero,mul_one]

private def Reduced (P : Parameters) (hp : P.prime=2) (x : Carrier P) : Prop :=
  (∃ z : highestRoot P, IsConj x z.val) ∨
  (∃ v : radical P .central, (firstLayer P hp v).1 ≠ 0 ∧ IsConj x v.val)

private theorem Reduced.of_isConj {P : Parameters} {hp : P.prime=2}
    {x y : Carrier P} (hy : Reduced P hp y) (h : IsConj x y) : Reduced P hp x := by
  rcases hy with ⟨z,hz⟩ | ⟨v,hv,hc⟩
  · exact Or.inl ⟨z,h.trans hz⟩
  · exact Or.inr ⟨v,hv,h.trans hc⟩

private theorem reduced_long_zero (P : Parameters) (hp : P.prime=2) (b f : fixedField P) :
    Reduced P hp (long P hp 0 b * long P hp 2 f) := by
  by_cases hb : b=0
  · exact Or.inl ⟨⟨long P hp 2 f,long_mem_highest P hp f⟩,by simpa only [hb,long_zero,one_mul] using (IsConj.refl (long P hp 2 f))⟩
  · exact Or.inl ⟨⟨long P hp 2 b,long_mem_highest P hp b⟩,
      (long_pair_zero P hp b f hb).trans (isConj_iff.mpr
        ⟨weylRepresentative P hp (.r 5),rotation_long_zero P hp b⟩)⟩

private theorem reduced_long_one (P : Parameters) (hp : P.prime=2) (e f : fixedField P) :
    Reduced P hp (long P hp 1 e * long P hp 2 f) := by
  by_cases he : e=0
  · exact Or.inl ⟨⟨long P hp 2 f,long_mem_highest P hp f⟩,by simpa only [he,long_zero,one_mul] using (IsConj.refl (long P hp 2 f))⟩
  · exact Or.inl ⟨⟨long P hp 2 e,long_mem_highest P hp e⟩,
      (long_pair_one P hp e f he).trans (isConj_iff.mpr
        ⟨weylRepresentative P hp (.sr 1),central_long_one P hp e⟩)⟩

private theorem reduced_of_short_one (P : Parameters) (hp : P.prime=2)
    (c d : ExtensionField P) (e f : fixedField P) (hc : c≠0) :
    Reduced P hp (armsCoordinates P hp (![c,d],![0,e,f])).val := by
  refine Or.inr ⟨coordinates P hp (![c,0,d],![f,e]),?_,?_⟩
  · rw [firstLayer_coordinates P hp]
    exact hc
  · exact isConj_iff.mpr ⟨weylRepresentative P hp (.sr 1),central_image P hp c d e f⟩

private theorem reduced_of_short_two (P : Parameters) (hp : P.prime=2)
    (d : ExtensionField P) (b f : fixedField P) :
    Reduced P hp (armsCoordinates P hp (![0,d],![b,0,f])).val := by
  by_cases hd : d=0
  · have hv : (armsCoordinates P hp (![0,d],![b,0,f])).val =
        long P hp 0 b * long P hp 2 f := by
      rw [armsCoordinates_factorization]
      simp [hd]
    rw [hv]
    exact reduced_long_zero P hp b f
  · refine Or.inr ⟨coordinates P hp (![fieldFrobenius P d,0,0],![f,b]),?_,?_⟩
    · rw [firstLayer_coordinates P hp]
      exact (map_ne_zero (fieldFrobenius P)).mpr hd
    · exact isConj_iff.mpr ⟨weylRepresentative P hp (.r 5),rotation_image P hp d b f⟩

private theorem shear_preserves_square (P : Parameters) (hp : P.prime=2)
    (a : ExtensionField P) (v : ArmsParameters P)
    (hs : (armsCoordinates P hp v)^2=1) :
    (armsCoordinates P hp (shearParameters P a v))^2=1 := by
  apply Subtype.ext
  change (armsCoordinates P hp (shearParameters P a v)).val ^ 2 = 1
  rw [← short_shear,conj_pow]
  have h := congrArg (fun x : radical P .arms => x.val) hs
  change (armsCoordinates P hp v).val ^2=1 at h
  rw [h,mul_one,mul_inv_cancel]

private theorem reduced_of_long_zero (P : Parameters) (hp : P.prime=2)
    (v : ArmsParameters P) (hb : v.2 0 ≠ 0) (hs : (armsCoordinates P hp v)^2=1) :
    Reduced P hp (armsCoordinates P hp v).val := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  let a := v.1 0 / (v.2 0).val
  let w := shearParameters P a v
  have hbval : (v.2 0).val ≠ 0 := by exact_mod_cast hb
  have hwa : w.1 0=0 := by
    change v.1 0 + (v.2 0).val * (v.1 0 / (v.2 0).val)=0
    rw [mul_div_cancel₀ _ hbval,CharTwo.add_self_eq_zero]
  have hwb : w.2 0 = v.2 0 := rfl
  have hwe : w.2 1=0 := by
    have hz := arms_square_condition P hp w (shear_preserves_square P hp a v hs)
    rw [hwa,armsPairing_zero_left,add_zero,hwb] at hz
    exact (mul_eq_zero.mp hz).resolve_right hb
  have hw : w=(![0,w.1 1],![w.2 0,0,w.2 2]) := by
    apply Prod.ext
    · funext i; fin_cases i <;> simp [hwa]
    · funext i; fin_cases i <;> simp [hwe]
  have hr : Reduced P hp (armsCoordinates P hp w).val := by
    rw [hw]
    exact reduced_of_short_two P hp _ _ _
  exact hr.of_isConj (isConj_iff.mpr ⟨short P hp 0 a,short_shear P hp a v⟩)

private theorem reduced_of_long_zero_eq_zero (P : Parameters) (hp : P.prime=2)
    (v : ArmsParameters P) (hb : v.2 0=0) :
    Reduced P hp (armsCoordinates P hp v).val := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  by_cases hc : v.1 0=0
  · by_cases hd : v.1 1=0
    · have hv : (armsCoordinates P hp v).val = long P hp 1 (v.2 1) * long P hp 2 (v.2 2) := by
        rw [armsCoordinates_factorization]
        simp [hb,hc,hd]
      rw [hv]
      exact reduced_long_one P hp _ _
    · obtain ⟨a,ha⟩ := armsPairing_surjective_left P hp (v.1 1) hd (v.2 1)
      have hw : shearParameters P a v = (![0,v.1 1],![0,0,v.2 2]) := by
        apply Prod.ext
        · funext i; fin_cases i <;> simp [shearParameters,hb,hc,higherCoefficient,-fieldFrobenius_apply]
        · funext i; fin_cases i <;>
            simp [shearParameters,hb,hc,ha,CharTwo.add_self_eq_zero,-fieldFrobenius_apply]
      apply (reduced_of_short_two P hp (v.1 1) 0 (v.2 2)).of_isConj
      exact isConj_iff.mpr ⟨short P hp 0 a,by rw [← hw]; exact short_shear P hp a v⟩
  · have hv : v=(![v.1 0,v.1 1],![0,v.2 1,v.2 2]) := by
      apply Prod.ext
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> simp [hb]
    rw [hv]
    exact reduced_of_short_one P hp _ _ _ _ hc

/-- Every arms-radical involution reduces to a highest-root element or a central
radical element with nonzero first short coordinate, on the literal carrier. -/
theorem arms_reduction (P : Parameters) (hp : P.prime=2)
    (u : radical P .arms) (hu : orderOf u.val=2) :
    (∃ z : highestRoot P, IsConj u.val z.val) ∨
    (∃ v : radical P .central, (firstLayer P hp v).1≠0 ∧ IsConj u.val v.val) := by
  obtain ⟨v,rfl⟩ := (armsCoordinates P hp).surjective u
  change Reduced P hp (armsCoordinates P hp v).val
  by_cases hb : v.2 0=0
  · exact reduced_of_long_zero_eq_zero P hp v hb
  · apply reduced_of_long_zero P hp v hb
    apply Subtype.ext
    change (armsCoordinates P hp v).val ^2=1
    rw [← hu]
    exact pow_orderOf_eq_one _
end
end Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
