module
public import Theory.SpecificGroups.Triality.BinaryTorusInvolutions

/-!
# Two representatives for binary triality reflection pairs

The three torus-fixed long roots have their literal Heisenberg product.
Their two Weyl actions show that the common Borel element with coordinates
(b,p+b,j+p+b) conjugates the pair with arms parameter p+q+b to the original
four-coordinate pair. Idempotence in the field of order two is the only
additional scalar identity. Thus one binary twist remains, and the zero
parameter has the genuine native sixth-power relation.

These are identities in the standard graph-field carrier, not in an auxiliary
matrix model. The completion consumer transports one common conjugation
through both original endpoint maps.
Source: GLS3 §§2.4,2.6 and Aschbacher--Smith F.4.15--17, pp.281--283
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
namespace Triality.Standard.BinaryTorusEndpoints
open Parabolics ConcreteBruhat RadicalCoordinates.LeviCommutators
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "C" => Carrier P

private theorem fixed_sq (a : fixedField P) : a^2=a := by
  let := Fintype.ofFinite (fixedField P)
  have h := FiniteField.pow_card a
  rwa [←Nat.card_eq_fintype_card,card_fixedField] at h

private theorem fixedBorel_zero' : (fixedBorel 0 : C)=1 := by
  simp only [fixedBorel,CentralCovers.TwoPrimary.baseProduct,Pi.zero_apply,
    short_zero P (Eq.refl 2),long_zero P (Eq.refl 2),one_mul]

private theorem fixedBorel_ext {a b : Fin 3 → fixedField P} (h : a=b) :
    (fixedBorel a:C)=(fixedBorel b:C) := congrArg (fun a => (fixedBorel a:C)) h

/-- One common fixed unipotent conjugation at the arms endpoint. -/
theorem arms_fixed_conjugation (a b d k : fixedField P) :
    let u := inclusion (borel_le_parabolic P .arms) (fixedBorel ![a,b,d])
    u * endpointWord .arms ![0,0,k] 0 1 * u⁻¹ =
      endpointWord .arms ![a+b,a+b,k+b] 0 1 := by
  apply Subtype.ext
  change (fixedBorel ![a,b,d]:C)*((fixedBorel ![0,0,k]:C)*simpleRepresentative P (Eq.refl 2) .arms*fixedBorel 0*1)*
    (fixedBorel ![a,b,d]:C)⁻¹=(fixedBorel ![a+b,a+b,k+b]:C)*simpleRepresentative P (Eq.refl 2) .arms*fixedBorel 0*1
  simp only [fixedBorel_zero',mul_one]
  apply mul_inv_eq_iff_eq_mul.mpr
  have hw := mul_inv_eq_iff_eq_mul.mp (arms_reflection_fixed ![a,b,d])
  rw [mul_assoc (fixedBorel ![a+b,a+b,k+b]:C),hw,←mul_assoc,←mul_assoc,
    fixedBorel_mul,fixedBorel_mul]
  apply congrArg (fun x : C => x*simpleRepresentative P (Eq.refl 2) .arms)
  apply fixedBorel_ext
  funext i
  fin_cases i
  · change a+0=(a+b)+b
    rw [add_assoc,CharTwo.add_self_eq_zero b,add_zero]
  · change b+0=(a+b)+a
    rw [add_right_comm,CharTwo.add_self_eq_zero a,zero_add,add_zero]
  · change d+k+b*0=(k+b)+(d+a*b)+(a+b)*b
    have hbb : b*b=b := by simpa only [pow_two] using fixed_sq b
    simp only [mul_zero,add_zero,add_mul,hbb]
    linear_combination (norm := ring_nf) -(CharTwo.add_self_eq_zero b) -
      a*(CharTwo.add_self_eq_zero b)

/-- The same fixed unipotent conjugation at the central endpoint. -/
theorem central_fixed_conjugation (a b d : fixedField P) :
    let u := inclusion (borel_le_parabolic P .central) (fixedBorel ![a,b,d])
    u * simpleEndpoint .central * u⁻¹ =
      endpointWord .central (Pi.single 0 a) ![a,b+d,(1+a)*(b+d)] 1 := by
  apply Subtype.ext
  change (fixedBorel ![a,b,d]:C)*simpleRepresentative P (Eq.refl 2) .central*
    (fixedBorel ![a,b,d]:C)⁻¹=
      (fixedBorel (Pi.single 0 a):C)*simpleRepresentative P (Eq.refl 2) .central*
        (fixedBorel ![a,b+d,(1+a)*(b+d)]:C)*1
  rw [mul_one]
  apply mul_inv_eq_iff_eq_mul.mpr
  have hu : (fixedBorel ![a,b,d]:C)=
      (fixedBorel (Pi.single 0 a):C)*(fixedBorel ![0,b,d]:C) := by
    rw [fixedBorel_mul]
    apply fixedBorel_ext
    funext i
    fin_cases i <;> simp
  have ht : (fixedBorel ![a,b+d,(1+a)*(b+d)]:C)*(fixedBorel ![a,b,d]:C)=
      (fixedBorel ![0,d,b]:C) := by
    rw [fixedBorel_mul]
    apply fixedBorel_ext
    funext i
    fin_cases i
    · exact CharTwo.add_self_eq_zero a
    · change b+d+b=d
      rw [add_right_comm,CharTwo.add_self_eq_zero,zero_add]
    · change (1+a)*(b+d)+d+(b+d)*a=b
      linear_combination (norm := ring_nf) (CharTwo.add_self_eq_zero d) +
        (b+d)*(CharTwo.add_self_eq_zero a)
  have hw := mul_inv_eq_iff_eq_mul.mp (central_reflection_tail d b)
  rw [mul_assoc ((fixedBorel (Pi.single 0 a):C)*simpleRepresentative P (Eq.refl 2) .central),
    ht,mul_assoc,hw,←mul_assoc,←hu]

/-- Every four-coordinate pair is a simultaneous conjugate of one of two
pairs; the conjugating element lies in the same torus-fixed Borel subgroup. -/
theorem four_coordinate_conjugation (p q b j : fixedField P) :
    let u := fixedBorel ![b,p+b,j+p+b]
    let s := endpointWord .arms ![0,0,p+q+b] 0 1
    let t := simpleEndpoint .central
    (inclusion (borel_le_parabolic P .arms) u)*s*
      (inclusion (borel_le_parabolic P .arms) u)⁻¹ = endpointWord .arms ![p,p,q] 0 1 ∧
    (inclusion (borel_le_parabolic P .central) u)*t*
      (inclusion (borel_le_parabolic P .central) u)⁻¹ =
        endpointWord .central (Pi.single 0 b) ![b,j,(1+b)*j] 1 := by
  have ha : b+(p+b)=p := by
    rw [add_left_comm,CharTwo.add_self_eq_zero,add_zero]
  have hb : (p+q+b)+(p+b)=q := by
    linear_combination (norm := ring_nf) (CharTwo.add_self_eq_zero p) +
      (CharTwo.add_self_eq_zero b)
  have hj : (p+b)+(j+p+b)=j := by
    linear_combination (norm := ring_nf) (CharTwo.add_self_eq_zero p) +
      (CharTwo.add_self_eq_zero b)
  constructor
  · simpa only [ha,hb] using arms_fixed_conjugation b (p+b) (j+p+b) (p+q+b)
  · simpa only [hj] using central_fixed_conjugation b (p+b) (j+p+b)

/-- The one remaining scalar is binary. -/
theorem fixed_eq_zero_or_one (a : fixedField P) : a=0 ∨ a=1 :=
  eq_zero_or_one_of_sq_eq_self (fixed_sq a)

/-- The untwisted pair satisfies the native hexagon equation. -/
theorem canonical_product_six :
    ((endpointWord .arms ![0,0,0] 0 1:C)*(simpleEndpoint .central:C))^6=1 := by
  have hz : (![0,0,0] : Fin 3 → fixedField P)=0 := by funext i; fin_cases i <;> rfl
  change ((fixedBorel ![0,0,0]:C)*simpleRepresentative P (Eq.refl 2) .arms*
    fixedBorel 0*1*simpleRepresentative P (Eq.refl 2) .central)^6=1
  simp only [hz,fixedBorel_zero',one_mul,mul_one]
  rw [←orderOf_simpleProduct P (Eq.refl 2)]
  exact pow_orderOf_eq_one _

end Triality.Standard.BinaryTorusEndpoints
