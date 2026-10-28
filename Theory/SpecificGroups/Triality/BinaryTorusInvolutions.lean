module
public import Theory.SpecificGroups.Triality.BinaryTorusEndpoints
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.TorusModel
public import Theory.SpecificGroups.Triality.BinaryThreeFreeSylow
import all Theory.SpecificGroups.Triality.BinaryThreeFreeSylow

/-!
# Binary triality involutions in the torus normalizer

The central local factor has order 12288, coprime to the order-seven torus.
Thus a central endpoint involution has trivial torus parameter. The arms
reflection inverts that torus, so conjugation by the fourth power of its
parameter removes the arms torus factor while fixing the central word.
This is one common Borel conjugation, usable with unchanged endpoint maps.

The three torus-fixed long roots obey the actual radical multiplication law.
Their Weyl actions force equal lower coordinates at the arms endpoint. At the
central endpoint the action on the higher-root plane forces the two lower
coefficients to agree; the involution equation then determines the last one.
Consequently the torus-free pair has only four binary parameters. This does
not assert a sixth-power equation for their product.

Source: GLS3 §§2.4,2.6 for the literal root and torus actions, and the Cartan
comparison of Aschbacher--Smith F.4.15--17, pp.281--283 (`refs/quasithin.pdf`).
The internal import reuses the checked central local-factor order without
changing the shared module's public boundary.
-/

@[expose] public noncomputable section
open Subgroup
namespace Triality.Standard.BinaryTorusEndpoints
open Parabolics ConcreteBruhat RadicalCoordinates.LeviCommutators
open RootPresentationRecognition
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "C" => Carrier P

private theorem fixed_units_one (u : (fixedField P)ˣ) : u = 1 := by
  have hc : Nat.card (fixedField P)ˣ = 1 := by rw [Nat.card_units,card_fixedField]; rfl
  let : Subsingleton (fixedField P)ˣ := (Nat.card_eq_one_iff_unique.mp hc).1
  exact Subsingleton.elim _ _

/-- The central reflection centralizes the whole binary torus. -/
theorem central_reflection_torus (z : torus P) :
    simpleRepresentative P (Eq.refl 2) .central * (z : C) *
      (simpleRepresentative P (Eq.refl 2) .central)⁻¹ = z := by
  obtain ⟨p,rfl⟩ := (TorusCoordinates.torusMulEquiv P (Eq.refl 2)).surjective z
  have h := TorusModel.central 1 Nat.zero_lt_one p
  rw [SignedModel.nB_one,SignedModel.torus_eq,SignedModel.torus_eq] at h
  have hp : (p.1,RootPresentationRecognition.normUnit p.1 / p.2) = p := by
    apply Prod.ext
    · rfl
    change RootPresentationRecognition.normUnit p.1 / p.2 = p.2
    rw [fixed_units_one (RootPresentationRecognition.normUnit p.1),fixed_units_one p.2,div_one]
  simpa only [hp] using h

/-- The arms reflection inverts the same binary torus. -/
theorem arms_reflection_torus (z : torus P) :
    simpleRepresentative P (Eq.refl 2) .arms * (z : C) *
      (simpleRepresentative P (Eq.refl 2) .arms)⁻¹ = (z : C)⁻¹ := by
  obtain ⟨p,rfl⟩ := (TorusCoordinates.torusMulEquiv P (Eq.refl 2)).surjective z
  have h := TorusModel.arms 1 Nat.zero_lt_one p
  rw [SignedModel.nA_one,SignedModel.torus_eq,SignedModel.torus_eq] at h
  have hp : (TorusCoordinates.fixedUnit P p.2 / p.1,p.2) = p⁻¹ := by
    apply Prod.ext
    · simp only [fixed_units_one p.2,map_one,one_div,Prod.fst_inv]
    · simp only [fixed_units_one p.2,Prod.snd_inv,inv_one]
  simpa only [hp,map_inv,Subgroup.coe_inv] using h

private theorem fixedBorel_mem_unipotent (a : Fin 3 → fixedField P) :
    (fixedBorel a : C) ∈ unipotent P :=
  ((BinaryTorusCentralizer.mem_unipotent_torus_centralizer_iff _).mpr ⟨a,rfl⟩).1

/-- Every binary fixed unipotent word commutes with the original torus. -/
theorem torus_commute_fixedBorel (z : torus P) (a : Fin 3 → fixedField P) :
    Commute (z : C) (fixedBorel a : C) :=
  ((BinaryTorusCentralizer.mem_unipotent_torus_centralizer_iff _).mpr ⟨a,rfl⟩).2 z z.property

private theorem fixedBorel_mem_local (a : Fin 3 → fixedField P) :
    (fixedBorel a : C) ∈ localFactor P .central :=
  sylow_le_localFactor P .central (unipotentSylow P (Eq.refl 2))
    ((unipotent_le_borel P).trans (borel_le_parabolic P .central))
      (fixedBorel_mem_unipotent a)

/-- The torus has trivial intersection with the central local factor. -/
theorem disjoint_torus_central_local : Disjoint (torus P) (localFactor P .central) := by
  apply disjoint_def.mpr
  intro z hz hl
  have h7 : orderOf z ∣ 7 := by
    have h := orderOf_dvd_natCard (⟨z,hz⟩ : torus P)
    rw [←orderOf_injective (torus P).subtype (torus P).subtype_injective,
      TorusCoordinates.card_torus P (Eq.refl 2)] at h
    exact h
  have h12 : orderOf z ∣ 12288 := by
    have h := orderOf_dvd_natCard (⟨z,hl⟩ : localFactor P .central)
    rw [←orderOf_injective (localFactor P .central).subtype
      (localFactor P .central).subtype_injective,
      BinaryThreeFreeSylow.central_local_card] at h
    exact h
  have h1 : orderOf z ∣ 1 := Nat.dvd_gcd h7 h12
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)


/-- Involutivity removes the torus factor at the central endpoint. This uses
its actual local factor, of order 12288, disjoint from the seven-torus. -/
theorem central_involution_torus_eq_one
    (a b : Fin 3 → fixedField P) (z : torus P)
    (h : (endpointWord .central a b z)^2 = 1) : z = 1 := by
  let x := endpointWord .central a b z
  have hx : (x : C) ∈ localFactor P .central :=
    mem_localFactor_of_pow P .central x x.property 1 (congrArg Subtype.val h)
  have hw : simpleRepresentative P (Eq.refl 2) .central ∈ localFactor P .central :=
    mem_localFactor_of_pow P .central _ (simpleRepresentative_mem_parabolic P (Eq.refl 2) .central)
      1 (simpleRepresentative_sq P (Eq.refl 2) .central)
  have hp := (localFactor P .central).mul_mem
    ((localFactor P .central).mul_mem (fixedBorel_mem_local a) hw) (fixedBorel_mem_local b)
  have hz : (z : C) ∈ localFactor P .central := by
    have hh := (localFactor P .central).mul_mem ((localFactor P .central).inv_mem hp) hx
    change (((fixedBorel a : C) * simpleRepresentative P (Eq.refl 2) .central * fixedBorel b)⁻¹ *
      ((fixedBorel a : C) * simpleRepresentative P (Eq.refl 2) .central * fixedBorel b * z)) ∈ _ at hh
    simpa only [inv_mul_cancel_left] using hh
  apply Subtype.ext
  exact disjoint_def.mp disjoint_torus_central_local z.property hz

/-- Removing the central torus factor leaves the same native element. -/
theorem central_involution_word
    (a b : Fin 3 → fixedField P) (z : torus P)
    (h : (endpointWord .central a b z)^2 = 1) :
    endpointWord .central a b z = endpointWord .central a b 1 := by
  rw [central_involution_torus_eq_one a b z h]

private theorem fixedBorel_zero : (fixedBorel 0 : C) = 1 := by
  simp only [fixedBorel, CentralCovers.TwoPrimary.baseProduct, Pi.zero_apply,
    short_zero P (Eq.refl 2), long_zero P (Eq.refl 2), one_mul]

/-- Fourth powers are square roots in the original order-seven torus. -/
theorem torus_fourth_sq (z : torus P) : (z^4)^2 = z := by
  have hz : z^7=1 := by
    have h := pow_card_eq_one' (x := z)
    rwa [TorusCoordinates.card_torus P (Eq.refl 2)] at h
  calc
    (z^4)^2 = z^7*z := by group
    _ = z := by rw [hz,one_mul]

/-- One common torus conjugation removes the arms torus parameter. -/
theorem arms_torus_conjugation (a : Fin 3 → fixedField P) (z : torus P) :
    let q := inclusion (borel_le_parabolic P .arms) (torusBorel (z^4))
    q * endpointWord .arms a 0 z * q⁻¹ = endpointWord .arms a 0 1 := by
  apply Subtype.ext
  change ((z^4 : torus P) : C) *
    ((fixedBorel a : C) * simpleRepresentative P (Eq.refl 2) .arms * fixedBorel 0 * z) *
      (((z^4 : torus P) : C))⁻¹ =
    (fixedBorel a : C) * simpleRepresentative P (Eq.refl 2) .arms * fixedBorel 0 * (1 : C)
  simp only [fixedBorel_zero,mul_one]
  let q : C := (z^4 : torus P)
  let w : C := simpleRepresentative P (Eq.refl 2) .arms
  have hq := torus_commute_fixedBorel (z^4) a
  have hw : q*w=w*q⁻¹ := by
    have hh := arms_reflection_torus (z^4)⁻¹
    simpa only [Subgroup.coe_inv,inv_inv] using (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hz : (z : C)=q^2 := (congrArg Subtype.val (torus_fourth_sq z)).symm
  change q*((fixedBorel a : C)*w*(z:C))*q⁻¹=(fixedBorel a:C)*w
  rw [hz]
  calc
    _ = (q*(fixedBorel a:C))*w*(q^2*q⁻¹) := by group
    _ = ((fixedBorel a:C)*q)*w*q := by rw [hq.eq]; dsimp only [q]; group
    _ = (fixedBorel a:C)*(q*w)*q := by group
    _ = (fixedBorel a:C)*(w*q⁻¹)*q := by rw [hw]
    _ = _ := by group

/-- The same common torus conjugation fixes the central torus-free word. -/
theorem central_torus_conjugation (a b : Fin 3 → fixedField P) (z : torus P) :
    let q := inclusion (borel_le_parabolic P .central) (torusBorel z)
    q * endpointWord .central a b 1 * q⁻¹ = endpointWord .central a b 1 := by
  apply Subtype.ext
  have hw : Commute (z : C) (simpleRepresentative P (Eq.refl 2) .central) :=
    (mul_inv_eq_iff_eq_mul.mp (central_reflection_torus z)).symm
  have h := ((torus_commute_fixedBorel z a).mul_right hw).mul_right
    (torus_commute_fixedBorel z b)
  change (z:C)*((fixedBorel a:C)*simpleRepresentative P (Eq.refl 2) .central*fixedBorel b*1)*(z:C)⁻¹ =
    (fixedBorel a:C)*simpleRepresentative P (Eq.refl 2) .central*fixedBorel b*1
  simp only [mul_one]
  rw [h.eq,mul_inv_cancel_right]


open RadicalCoordinates.Centers

private theorem fixedBorel_toSplit (a : Fin 3 → fixedField P) :
    FixedDescent.carrierToSplit P (Eq.refl 2) (fixedBorel a) = armsProduct P (0,a) := by
  rw [show (fixedBorel a : C) = CentralCovers.TwoPrimary.baseProduct 1 Nat.zero_lt_one (0,a) from rfl,
    CentralCovers.TwoPrimary.baseProduct_toSplit]
  rfl

/-- The three torus-fixed long roots have their literal Heisenberg product. -/
theorem fixedBorel_mul (a b : Fin 3 → fixedField P) :
    (fixedBorel a : C)*(fixedBorel b : C) =
      fixedBorel ![a 0+b 0,a 1+b 1,a 2+b 2+a 1*b 0] := by
  apply FixedDescent.carrierToSplit_injective P (Eq.refl 2)
  rw [map_mul,fixedBorel_toSplit,fixedBorel_toSplit,fixedBorel_toSplit,
    ←armsProduct_multiply P (Eq.refl 2)]
  congr 1
  simp only [armsMultiply,armsCocycle,Pi.zero_apply,armsPairing_zero_left,add_zero]

private theorem fixed_product (a : Fin 3 → fixedField P) :
    (fixedBorel a : C) = long P (Eq.refl 2) 0 (a 0)*long P (Eq.refl 2) 1 (a 1)*long P (Eq.refl 2) 2 (a 2) := by
  simp only [fixedBorel,CentralCovers.TwoPrimary.baseProduct,Pi.zero_apply,
    short_zero P (Eq.refl 2),one_mul,mul_one]

private theorem long_as_fixed (i : Fin 3) (a : fixedField P) :
    long P (Eq.refl 2) i a = (fixedBorel (Pi.single i a) : C) := by
  fin_cases i <;> simp [fixed_product,long_zero P (Eq.refl 2)]

/-- The arms Weyl involution swaps the two lower long roots, with the
central correction forced by their noncommuting product order. -/
theorem arms_reflection_fixed (a : Fin 3 → fixedField P) :
    simpleRepresentative P (Eq.refl 2) .arms * (fixedBorel a : C) *
      (simpleRepresentative P (Eq.refl 2) .arms)⁻¹ =
        fixedBorel ![a 1,a 0,a 2+a 0*a 1] := by
  have hm (x y : C) : simpleRepresentative P (Eq.refl 2) .arms*(x*y)*
      (simpleRepresentative P (Eq.refl 2) .arms)⁻¹ =
      (simpleRepresentative P (Eq.refl 2) .arms*x*(simpleRepresentative P (Eq.refl 2) .arms)⁻¹)*
      (simpleRepresentative P (Eq.refl 2) .arms*y*(simpleRepresentative P (Eq.refl 2) .arms)⁻¹) := by group
  rw [fixed_product,hm,hm]
  rw [PositiveWeylModel.arms_long P (Eq.refl 2) 0,
    PositiveWeylModel.arms_long P (Eq.refl 2) 1,
    PositiveWeylModel.arms_long P (Eq.refl 2) 2]
  rw [long_as_fixed,long_as_fixed,long_as_fixed,fixedBorel_mul,fixedBorel_mul]
  apply congrArg (fun a : Fin 3 → fixedField P => (fixedBorel a:C))
  funext i
  fin_cases i <;> simp [add_comm]

/-- An arms involution has equal first two fixed-root coordinates. -/
theorem arms_involution_coordinates (a : Fin 3 → fixedField P)
    (h : (endpointWord .arms a 0 1)^2 = 1) : a 0 = a 1 := by
  have hs := congrArg Subtype.val h
  change ((fixedBorel a:C)*simpleRepresentative P (Eq.refl 2) .arms*fixedBorel 0*1)^2=1 at hs
  simp only [fixedBorel_zero,mul_one] at hs
  have hw : (simpleRepresentative P (Eq.refl 2) .arms)^2=1 := simpleRepresentative_sq P (Eq.refl 2) .arms
  have he : (fixedBorel a:C)*
      (simpleRepresentative P (Eq.refl 2) .arms*(fixedBorel a:C)*(simpleRepresentative P (Eq.refl 2) .arms)⁻¹)=1 := by
    have hi : (simpleRepresentative P (Eq.refl 2) .arms)⁻¹=simpleRepresentative P (Eq.refl 2) .arms :=
      inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hw)
    rw [hi]
    simpa only [pow_two,mul_assoc] using hs
  rw [arms_reflection_fixed,fixedBorel_mul] at he
  have hinj (b d : Fin 3 → fixedField P) (hb : (fixedBorel b:C)=(fixedBorel d:C)) : b=d :=
    congrArg Prod.snd (CentralCovers.TwoPrimary.baseProduct_injective 1 Nat.zero_lt_one hb)
  have hz := congrFun (hinj _ 0 (he.trans fixedBorel_zero.symm)) 0
  have hsum : a 0 + a 1 = 0 := hz
  exact eq_neg_of_add_eq_zero_left hsum |>.trans (CharTwo.neg_eq _)


/-- The fixed long-root group acts on its higher-root plane by the exact shear. -/
theorem fixedBorel_conjugate_tail (a : Fin 3 → fixedField P) (y z : fixedField P) :
    (fixedBorel a:C)*(fixedBorel ![0,y,z]:C)*(fixedBorel a:C)⁻¹ =
      fixedBorel ![0,y,z+a 0*y] := by
  apply mul_inv_eq_iff_eq_mul.mpr
  rw [fixedBorel_mul,fixedBorel_mul]
  apply congrArg (fun a : Fin 3 → fixedField P => (fixedBorel a:C))
  funext i
  fin_cases i
  · change a 0+0=0+a 0
    exact add_comm _ _
  · change a 1+y=y+a 1
    exact add_comm _ _
  · change a 2+z+a 1*0=z+a 0*y+a 2+y*a 0
    rw [mul_zero,add_zero]
    calc
      a 2+z = (a 2+z)+(a 0*y+a 0*y) := by rw [CharTwo.add_self_eq_zero (a 0*y),add_zero]
      _ = _ := by ring

/-- The central reflection swaps the two higher fixed long roots. -/
theorem central_reflection_tail (y z : fixedField P) :
    simpleRepresentative P (Eq.refl 2) .central*(fixedBorel ![0,y,z]:C)*
      (simpleRepresentative P (Eq.refl 2) .central)⁻¹ = fixedBorel ![0,z,y] := by
  have hm (x y : C) : simpleRepresentative P (Eq.refl 2) .central*(x*y)*
      (simpleRepresentative P (Eq.refl 2) .central)⁻¹ =
      (simpleRepresentative P (Eq.refl 2) .central*x*(simpleRepresentative P (Eq.refl 2) .central)⁻¹)*
      (simpleRepresentative P (Eq.refl 2) .central*y*(simpleRepresentative P (Eq.refl 2) .central)⁻¹) := by group
  rw [fixed_product]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,long_zero P (Eq.refl 2),one_mul]
  rw [hm,PositiveWeylModel.central_long P (Eq.refl 2) 1 (by decide),
    PositiveWeylModel.central_long P (Eq.refl 2) 2 (by decide)]
  rw [long_as_fixed,long_as_fixed,fixedBorel_mul]
  apply congrArg (fun a : Fin 3 → fixedField P => (fixedBorel a:C))
  funext i
  fin_cases i <;> simp

/-- The central endpoint induces its literal two-dimensional action on the
higher long-root plane. The remaining tail coordinates act trivially. -/
theorem central_word_conjugate_tail (b : fixedField P) (d : Fin 3 → fixedField P)
    (y z : fixedField P) :
    (endpointWord .central (Pi.single 0 b) d 1:C)*(fixedBorel ![0,y,z]:C)*
      (endpointWord .central (Pi.single 0 b) d 1:C)⁻¹ =
        fixedBorel ![0,z+d 0*y,y+b*(z+d 0*y)] := by
  have hm (x y v : C) : (x*y)*v*(x*y)⁻¹=x*(y*v*y⁻¹)*x⁻¹ := by group
  change ((fixedBorel (Pi.single 0 b):C)*simpleRepresentative P (Eq.refl 2) .central*(fixedBorel d:C)*1)*
    (fixedBorel ![0,y,z]:C)*((fixedBorel (Pi.single 0 b):C)*simpleRepresentative P (Eq.refl 2) .central*(fixedBorel d:C)*1)⁻¹ = _
  simp only [mul_one]
  rw [hm,hm,fixedBorel_conjugate_tail,central_reflection_tail,fixedBorel_conjugate_tail]
  simp only [Pi.single_eq_same]

/-- Involutivity equates the leading and trailing simple long-root coefficients. -/
theorem central_involution_leading (b : fixedField P) (d : Fin 3 → fixedField P)
    (h : (endpointWord .central (Pi.single 0 b) d 1)^2=1) : d 0=b := by
  let t : C := endpointWord .central (Pi.single 0 b) d 1
  let u : C := fixedBorel ![0,0,1]
  have ht : t*t=1 := by simpa only [pow_two,Subgroup.coe_mul,Subgroup.coe_one] using congrArg Subtype.val h
  have he : t*(t*u*t⁻¹)*t⁻¹=u := by
    calc
      _ = (t*t)*u*(t*t)⁻¹ := by group
      _ = u := by rw [ht]; simp
  change (endpointWord .central (Pi.single 0 b) d 1:C)*
    ((endpointWord .central (Pi.single 0 b) d 1:C)*(fixedBorel ![0,0,1]:C)*
      (endpointWord .central (Pi.single 0 b) d 1:C)⁻¹)*
        (endpointWord .central (Pi.single 0 b) d 1:C)⁻¹ = (fixedBorel ![0,0,1]:C) at he
  rw [central_word_conjugate_tail,central_word_conjugate_tail] at he
  have hc := congrArg Prod.snd
    (CentralCovers.TwoPrimary.baseProduct_injective 1 Nat.zero_lt_one he)
  have heq := congrFun hc 1
  have hz : b+d 0=0 := by simpa only [mul_zero,add_zero,mul_one,zero_add,Matrix.cons_val_one,Matrix.cons_val_zero,Matrix.head_cons,Matrix.tail_cons] using heq
  exact (eq_neg_of_add_eq_zero_left (show d 0+b=0 by rwa [add_comm])).trans (CharTwo.neg_eq b)


private theorem fixedBorel_injective : Function.Injective (fun a => (fixedBorel a:C)) := by
  intro a b h
  exact congrArg Prod.snd (CentralCovers.TwoPrimary.baseProduct_injective 1 Nat.zero_lt_one h)

private theorem fixedBorel_single_sq (b : fixedField P) :
    (fixedBorel (Pi.single 0 b):C)^2=1 := by
  rw [←long_as_fixed,pow_two,←long_add P (Eq.refl 2) 0 b b,
    CharTwo.add_self_eq_zero b,long_zero P (Eq.refl 2) 0]

private theorem fixedBorel_tail_sq (y z : fixedField P) :
    (fixedBorel ![0,y,z]:C)^2=1 := by
  rw [pow_two,fixedBorel_mul]
  have he : ![(![0,y,z]:Fin 3 → fixedField P) 0 + ![0,y,z] 0,
      ![0,y,z] 1 + ![0,y,z] 1,
      ![0,y,z] 2 + ![0,y,z] 2 + ![0,y,z] 1*![0,y,z] 0] = 0 := by
    funext i
    fin_cases i
    · simp
    · exact CharTwo.add_self_eq_zero y
    · change z+z+y*0=0
      rw [mul_zero,add_zero,CharTwo.add_self_eq_zero z]
  rw [he,fixedBorel_zero]

/-- Both constraints on a central endpoint involution, in the original
three-coordinate order. Thus this endpoint has only two binary parameters. -/
theorem central_involution_coordinates (b : fixedField P) (d : Fin 3 → fixedField P)
    (h : (endpointWord .central (Pi.single 0 b) d 1)^2=1) :
    d 0=b ∧ d 2=(1+b)*d 1 := by
  have hd := central_involution_leading b d h
  refine ⟨hd,?_⟩
  let x : C := fixedBorel (Pi.single 0 b)
  let w : C := simpleRepresentative P (Eq.refl 2) .central
  let v : C := fixedBorel ![0,d 1,d 2]
  let t : C := endpointWord .central (Pi.single 0 b) d 1
  have hx : x*x=1 := by simpa only [pow_two] using fixedBorel_single_sq b
  have hv : v*v=1 := by simpa only [pow_two] using fixedBorel_tail_sq (d 1) (d 2)
  have hw : w*w=1 := by simpa only [pow_two] using simpleRepresentative_sq P (Eq.refl 2) .central
  have ht : t*t=1 := by simpa only [pow_two,Subgroup.coe_mul,Subgroup.coe_one] using congrArg Subtype.val h
  have he : t=x*w*x*v := by
    change (endpointWord .central (Pi.single 0 b) d 1:C)=_
    simp only [endpointWord_val,Subgroup.coe_one,mul_one]
    have hh : (fixedBorel d:C)=x*v := by
      dsimp only [x,v]
      rw [fixedBorel_mul]
      apply congrArg (fun a : Fin 3 → fixedField P => (fixedBorel a:C))
      funext i
      fin_cases i <;> simp [hd]
    change x*w*(fixedBorel d:C)=x*w*x*v
    rw [hh]
    simp only [mul_assoc]
  have htv : (t*v)*(t*v)=1 := by
    rw [he]
    calc
      _ = x*w*x*(v*v)*x*w*x*(v*v) := by group
      _ = 1 := by rw [hv,mul_one,mul_one]; simp only [mul_assoc,hx,mul_one,hw]
  have hc : Commute t v := by
    have hi := inv_eq_of_mul_eq_one_left htv
    rw [mul_inv_rev,inv_eq_of_mul_eq_one_left hv,inv_eq_of_mul_eq_one_left ht] at hi
    exact hi.symm
  have hconj : t*v*t⁻¹=v := by rw [hc.eq,mul_inv_cancel_right]
  change (endpointWord .central (Pi.single 0 b) d 1:C)*
    (fixedBorel ![0,d 1,d 2]:C)*(endpointWord .central (Pi.single 0 b) d 1:C)⁻¹ =
      (fixedBorel ![0,d 1,d 2]:C) at hconj
  rw [central_word_conjugate_tail] at hconj
  have heq := congrFun (fixedBorel_injective hconj) 1
  have hz : d 2+b*d 1=d 1 := by
    change d 2+d 0*d 1=d 1 at heq
    rwa [hd] at heq
  calc
    d 2 = d 1-b*d 1 := eq_sub_of_add_eq hz
    _ = (1+b)*d 1 := by rw [sub_eq_add_neg,CharTwo.neg_eq (b*d 1)]; ring

/-- Four binary parameters now describe both torus-free involutions. -/
theorem involution_coordinate_words
    (a : Fin 3 → fixedField P) (b : fixedField P) (d : Fin 3 → fixedField P)
    (hs : (endpointWord .arms a 0 1)^2=1)
    (ht : (endpointWord .central (Pi.single 0 b) d 1)^2=1) :
    endpointWord .arms a 0 1 = endpointWord .arms ![a 0,a 0,a 2] 0 1 ∧
      endpointWord .central (Pi.single 0 b) d 1 =
        endpointWord .central (Pi.single 0 b) ![b,d 1,(1+b)*d 1] 1 := by
  have ha := arms_involution_coordinates a hs
  obtain ⟨hd,he⟩ := central_involution_coordinates b d ht
  constructor
  · congr 1
    funext i
    fin_cases i <;> simp [ha]
  · congr 1
    funext i
    fin_cases i <;> simp [hd,he]

/-- Every displayed endpoint word normalizes the same original seven-torus. -/
theorem endpointWord_normalizes (s : Node) (a b : Fin 3 → fixedField P) (z : torus P) :
    (endpointWord s a b z:C) ∈ normalizer (torus P : Set C) := by
  have hu (d : Fin 3 → fixedField P) : (fixedBorel d:C) ∈ normalizer (torus P:Set C) :=
    Subgroup.centralizer_le_normalizer _
      (((BinaryTorusCentralizer.mem_unipotent_torus_centralizer_iff _).mpr ⟨d,rfl⟩).2)
  have hw : simpleRepresentative P (Eq.refl 2) s ∈ normalizer (torus P:Set C) := by
    rw [←weylRepresentative_simple P (Eq.refl 2)]
    exact RelativeNormalizer.weylRepresentative_normalizes_torus P (Eq.refl 2) _
  change (fixedBorel a:C)*simpleRepresentative P (Eq.refl 2) s*(fixedBorel b:C)*(z:C)∈_
  exact mul_mem (mul_mem (mul_mem (hu a) hw) (hu b)) ((torus P).le_normalizer z.property)

end Triality.Standard.BinaryTorusEndpoints
