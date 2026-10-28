module
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.ArmsReduction.Transport
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.ArmsReduction.Weyl

/-!
# Sylow-fixed vectors in the actual triality arms-core quotient

The positive short-root shear formulas force the first long coordinate and
both cubic-field coordinates of a fixed quotient vector to vanish. The
nondegenerate cubic trace pairing and nontrivial field Frobenius prove this
symbolically, without enumerating the field or the group. The surviving
coordinates are the two highest long roots; a long-root shear and a central
Weyl reflection conjugate every nonidentity survivor into the highest root.

This is the fixed-space assertion used in the triality branch of
Aschbacher--Smith F.4.35, printed p.292. The theorem concerns the genuine
root radical, central subgroup and long-root class, including q=2. Its
original ambient application is in Chapter14/Section02/EightLargeParabolic/
FusionFixed.lean. It does not identify an arbitrary ambient completion.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
open Parabolics RadicalCoordinates RadicalCoordinates.Centers RadicalCoordinates.LeviCommutators

private theorem frobenius_moves (P : Parameters) :
    ∃ a : ExtensionField P, fieldFrobenius P a ≠ a := by
  by_contra! h
  have hi : Function.Injective (fun a : ExtensionField P => (⟨a,h a⟩ : fixedField P)) :=
    fun _ _ he => congrArg Subtype.val he
  have hc := Nat.card_le_card_of_injective _ hi
  rw [card_extensionField,card_fixedField] at hc
  have hq := P.q_ge_two
  nlinarith [sq_nonneg (P.q : ℤ)]

private theorem higher_nondegenerate (P : Parameters) (hp : P.prime=2)
    (c : ExtensionField P) (h : ∀ a, higherCoefficient P a c=0) : c=0 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have hc : fieldFrobenius P c=c := by
    have hh := h 1
    simpa only [higherCoefficient,map_one,one_mul,mul_one,CharTwo.add_eq_zero] using hh
  obtain ⟨a,ha⟩ := frobenius_moves P
  have hh := h a
  simp only [higherCoefficient,hc] at hh
  have he : c*(a+fieldFrobenius P a)=0 := by
    simpa only [mul_add,mul_comm] using hh
  exact (mul_eq_zero.mp he).resolve_right (fun he => ha (CharTwo.add_eq_zero.mp he).symm)

/-- The quotient coordinates fixed by every positive arms shear have only the
penultimate long-root coordinate remaining. -/
theorem shear_fixed_coordinates (P : Parameters) (hp : P.prime=2)
    (v : ArmsParameters P)
    (h : ∀ a, (shearParameters P a v).1=v.1 ∧
      (shearParameters P a v).2 1=v.2 1) :
    v.2 0=0 ∧ v.1=0 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have hb : v.2 0=0 := by
    have hh := congrFun (h 1).1 0
    have hz : (v.2 0 : ExtensionField P)=0 := by
      simpa only [shearParameters,Matrix.cons_val_zero,mul_one,add_eq_left] using hh
    exact Subtype.ext hz
  have hc : v.1 0=0 := higher_nondegenerate P hp _ (fun a => by
    have hh := congrFun (h a).1 1
    simpa only [shearParameters,Matrix.cons_val_one,Matrix.cons_val_zero,hb,
      Subfield.coe_zero,zero_mul,add_zero,add_eq_left] using hh)
  have hd : v.1 1=0 := armsPairing_right_nondegenerate P hp _ (fun a => by
    have hh := (h a).2
    simpa only [shearParameters,Matrix.cons_val_one,Matrix.cons_val_zero,hb,hc,
      zero_mul,map_zero,add_zero,add_eq_left] using hh)
  refine ⟨hb,?_⟩
  funext i
  fin_cases i <;> assumption

private theorem coordinates_multiply (P : Parameters) (hp : P.prime=2)
    (v w : ArmsParameters P) :
    armsCoordinates P hp (armsMultiply P v w)=armsCoordinates P hp v*armsCoordinates P hp w := by
  exact congrArg (MulEquiv.subgroupCongr (radical_eq_descendedRootSubgroup P hp .arms).symm)
    (armsEquiv_multiply P hp v w)

private theorem coordinates_central (P : Parameters) (hp : P.prime=2)
    (z : fixedField P) :
    (armsCoordinates P hp (centralParameters P z)).val=highestHom P hp (Multiplicative.ofAdd z) :=
  armsEquiv_centralParameters P hp z

/-- Equality modulo the actual highest-root center preserves the first eight
binary coordinates of the radical. -/
theorem coordinates_eq_of_central_difference (P : Parameters) (hp : P.prime=2)
    (v w : ArmsParameters P)
    (h : (armsCoordinates P hp w).val*(armsCoordinates P hp v).val⁻¹∈highestRoot P) :
    w.1=v.1 ∧ w.2 0=v.2 0 ∧ w.2 1=v.2 1 := by
  rw [←highestHom_range P hp] at h
  obtain ⟨z,hz⟩ := h
  have he : armsCoordinates P hp w =
      armsCoordinates P hp (centralParameters P z.toAdd)*armsCoordinates P hp v := by
    apply Subtype.ext
    change (armsCoordinates P hp w).val =
      (armsCoordinates P hp (centralParameters P z.toAdd)).val*(armsCoordinates P hp v).val
    rw [coordinates_central]
    exact (eq_mul_inv_iff_mul_eq.mp hz).symm
  rw [←coordinates_multiply] at he
  have hh := (armsCoordinates P hp).injective he
  rw [hh]
  simp [armsMultiply,centralParameters]

/-- The Sylow-fixed part of the actual arms-core quotient is precisely supported
on the two highest long roots; the last root is the center itself. -/
theorem fixed_mod_center_long_support (P : Parameters) (hp : P.prime=2)
    (u : radical P .arms)
    (h : ∀ a : ExtensionField P, ⁅short P hp 0 a,u.val⁆∈highestRoot P) :
    ∃ e f : fixedField P, u.val=long P hp 1 e*long P hp 2 f := by
  obtain ⟨v,rfl⟩ := (armsCoordinates P hp).surjective u
  have hh (a : ExtensionField P) :
      (shearParameters P a v).1=v.1 ∧ (shearParameters P a v).2 1=v.2 1 := by
    have hd := h a
    rw [commutatorElement_def,short_shear] at hd
    have he := coordinates_eq_of_central_difference P hp v (shearParameters P a v) hd
    exact ⟨he.1,he.2.2⟩
  obtain ⟨hb,hv⟩ := shear_fixed_coordinates P hp v hh
  refine ⟨v.2 1,v.2 2,?_⟩
  rw [armsCoordinates_factorization]
  simp only [hb,hv,Pi.zero_apply,long_zero,short_zero,one_mul]

private theorem long_pair_conjugate (P : Parameters) (hp : P.prime=2)
    (e f : fixedField P) (he : e≠0) :
    IsConj (long P hp 1 e*long P hp 2 f) (long P hp 2 e) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  let t := f/e
  have ht : t*e=f := div_mul_cancel₀ f he
  have hh : long P hp 0 t*long P hp 1 e*(long P hp 0 t)⁻¹ =
      long P hp 1 e*long P hp 2 (t*e) := by
    rw [long_zero_one_exchange P hp t e,mul_assoc (long P hp 1 e),
      ←(highest_commute_long P hp (t*e) 0 t).eq]
    group
  have hc : IsConj (long P hp 1 e*long P hp 2 f) (long P hp 1 e) := by
    refine isConj_iff.mpr ⟨long P hp 0 t,?_⟩
    rw [show long P hp 0 t*(long P hp 1 e*long P hp 2 f)*(long P hp 0 t)⁻¹ =
        (long P hp 0 t*long P hp 1 e*(long P hp 0 t)⁻¹)*
        (long P hp 0 t*long P hp 2 f*(long P hp 0 t)⁻¹) by group,
      hh,←(highest_commute_long P hp f 0 t).eq,mul_inv_cancel_right,ht,
      mul_assoc,←long_add,CharTwo.add_self_eq_zero,long_zero,mul_one]
  exact hc.trans (isConj_iff.mpr ⟨ConcreteBruhat.weylRepresentative P hp (.sr 1),
    central_long_one P hp e⟩)

/-- The fixed quotient elements are conjugate to the actual highest root,
with symbolic field parameters throughout the calculation. -/
theorem fixed_mod_center_conjugate_highest (P : Parameters) (hp : P.prime=2)
    (u : radical P .arms)
    (h : ∀ a : ExtensionField P, ⁅short P hp 0 a,u.val⁆∈highestRoot P) :
    ∃ z : highestRoot P, IsConj u.val z.val := by
  obtain ⟨e,f,huf⟩ := fixed_mod_center_long_support P hp u h
  have hz (t : fixedField P) : long P hp 2 t ∈ highestRoot P := by
    refine ⟨longElementary P hp 2 t,?_,rfl⟩
    change elementaryInclusion P (longElementary P hp 2 t) ∈ splitHighestRoot P
    rw [longElementary_val]
    exact ⟨Multiplicative.ofAdd t.val,rfl⟩
  by_cases he : e=0
  · refine ⟨⟨long P hp 2 f,hz f⟩,?_⟩
    have hu : u.val=long P hp 2 f := by simpa only [he,long_zero,one_mul] using huf
    rw [hu]
  · exact ⟨⟨long P hp 2 e,hz e⟩,huf.symm ▸ long_pair_conjugate P hp e f he⟩

/-- Every nonidentity element fixed modulo the arms center by the unipotent
shears belongs to the genuine long-root conjugacy class. -/
theorem fixed_mod_center_isLongRoot (n : ℕ) (hn : 0<n)
    (u : radical (binaryParameters n hn) .arms) (hne : u.val≠1)
    (h : ∀ a : ExtensionField (binaryParameters n hn),
      ⁅short (binaryParameters n hn) rfl 0 a,u.val⁆∈highestRoot (binaryParameters n hn)) :
    IsLongRootInvolution n hn u.val := by
  obtain ⟨z,hz⟩ := fixed_mod_center_conjugate_highest _ rfl u h
  have hz1 : z.val≠1 := by
    intro hh
    obtain ⟨a,ha⟩ := isConj_iff.mp hz
    have he := congrArg (MulAut.conj a⁻¹) (ha.trans hh)
    apply hne
    change a⁻¹*(a*u.val*a⁻¹)*(a⁻¹)⁻¹ = a⁻¹*1*(a⁻¹)⁻¹ at he
    simpa only [inv_inv,inv_mul_cancel_left,mul_assoc,mul_inv_cancel_left,mul_one,inv_mul_cancel] using he
  exact (isLongRootInvolution_of_mem_highestRoot n hn z.property hz1).of_isConj n hn hz.symm

end Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
