module
public import Theory.GroupTheory.FixedInvertedFactorization
public import Mathlib.Tactic.Group

/-!
# Uniqueness of four factors for a Klein-four action

For two commuting involutive automorphisms of a finite odd-order group,
multiplication is injective on four factors: points fixed by both, fixed by
the first and inverted by the second, inverted by the first and fixed by
the second, and inverted by both. No faithfulness or solubility is assumed.

The proof follows Gorenstein--Walter, *On finite groups with dihedral Sylow
2-subgroups*, Section 2, Lemma 4(ii). From equality of two products, unique
fixed/inverted splitting normalizes two ratios into a six-factor equation.
Apply the two automorphisms to that equation and compare squares. Unique
square roots in an odd-order group show one ratio is conjugate to its
inverse, hence trivial; the other ratio follows. Three applications of
fixed/inverted uniqueness then identify the original four factors.

This result supplies the injective map for the Klein-four cardinality
inequality. Once the exact Brauer--Wielandt formula is available, the same
map also supplies the three-fixed-subgroup factorization used in ABG.
-/

namespace MulAut

variable {G : Type*} [Group G]

private theorem eq_one_of_conjugate_inverse (odd : Odd (Nat.card G))
    (actor element : G) (inverted : actor * element * actor⁻¹ = element⁻¹) :
    element = 1 := by
  have squareInjective : Function.Injective (fun element : G => element ^ 2) :=
    odd.coprime_two_right.pow_left_bijective.injective
  have inverseImage : actor * element⁻¹ * actor⁻¹ = element := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using congrArg Inv.inv inverted
  have backward : actor⁻¹ * element * actor = element⁻¹ := by
    calc
      actor⁻¹ * element * actor =
          actor⁻¹ * (actor * element⁻¹ * actor⁻¹) * actor := by rw [inverseImage]
      _ = element⁻¹ := by group
  have square : (element * actor * element⁻¹) ^ 2 = actor ^ 2 := by
    calc
      (element * actor * element⁻¹) ^ 2 =
          actor * (actor⁻¹ * element * actor) * actor * element⁻¹ := by simp [pow_two, mul_assoc]
      _ = actor * (actor * element * actor⁻¹) * actor * element⁻¹ := by
        rw [backward, inverted]
      _ = actor ^ 2 := by simp [pow_two, mul_assoc]
  have root : element * actor * element⁻¹ = actor := squareInjective square
  have fixed : actor * element * actor⁻¹ = element := by
    calc
      actor * element * actor⁻¹ =
          (element * actor * element⁻¹) * element * actor⁻¹ := by rw [root]
      _ = element := by group
  have selfInverse : element = element⁻¹ := fixed.symm.trans inverted
  apply squareInjective
  change element ^ 2 = (1 : G) ^ 2
  calc
    element ^ 2 = element * element := pow_two element
    _ = element * element⁻¹ := by rw [← selfInverse]
    _ = (1 : G) ^ 2 := by group

private theorem normalized_ratios_eq_one (odd : Odd (Nat.card G))
    (common first middle other last final : G)
    (original : common * first * middle = other * last * final)
    (second : common * first⁻¹ * middle = other * last⁻¹ * final)
    (firstImage : common * first * middle⁻¹ = other⁻¹ * last⁻¹ * final)
    (bothImage : common * first⁻¹ * middle⁻¹ = other⁻¹ * last * final) :
    first = 1 ∧ last = 1 := by
  have squareInjective : Function.Injective (fun element : G => element ^ 2) :=
    odd.coprime_two_right.pow_left_bijective.injective
  have squareForward : (middle⁻¹ * first * middle) ^ 2 =
      (final⁻¹ * last * final) ^ 2 := by
    calc
      _ = (common * first⁻¹ * middle)⁻¹ * (common * first * middle) := by simp [pow_two, mul_assoc]
      _ = (other * last⁻¹ * final)⁻¹ * (other * last * final) := by
        rw [original, second]
      _ = _ := by simp [pow_two, mul_assoc]
  have forward := squareInjective squareForward
  have squareBackward : (middle * first * middle⁻¹) ^ 2 =
      (final⁻¹ * last⁻¹ * final) ^ 2 := by
    calc
      _ = (common * first⁻¹ * middle⁻¹)⁻¹ * (common * first * middle⁻¹) := by simp [pow_two, mul_assoc]
      _ = (other⁻¹ * last * final)⁻¹ * (other⁻¹ * last⁻¹ * final) := by
        rw [firstImage, bothImage]
      _ = _ := by simp [pow_two, mul_assoc]
  have backward := squareInjective squareBackward
  have inverted : middle ^ 2 * first * (middle ^ 2)⁻¹ = first⁻¹ := by
    calc
      _ = middle * (middle * first * middle⁻¹) * middle⁻¹ := by simp [pow_two, mul_assoc]
      _ = middle * (final⁻¹ * last⁻¹ * final) * middle⁻¹ := by rw [backward]
      _ = middle * (final⁻¹ * last * final)⁻¹ * middle⁻¹ := by group
      _ = middle * (middle⁻¹ * first * middle)⁻¹ * middle⁻¹ := by rw [forward]
      _ = first⁻¹ := by group
  have firstOne := eq_one_of_conjugate_inverse odd (middle ^ 2) first inverted
  refine ⟨firstOne, ?_⟩
  have lastConjugate : final⁻¹ * last * final = 1 := by
    simpa only [firstOne, mul_one, inv_mul_cancel] using forward.symm
  calc
    last = final * (final⁻¹ * last * final) * final⁻¹ := by group
    _ = 1 := by rw [lastConjugate]; group

private theorem normalized_fixed_inverted_ratios_eq_one (odd : Odd (Nat.card G))
    (firstActor secondActor : MulAut G)
    (common first middle other last final : G)
    (commonFirst : firstActor common = common)
    (commonSecond : secondActor common = common)
    (firstFixed : firstActor first = first)
    (firstInverted : secondActor first = first⁻¹)
    (middleFixed : secondActor middle = middle)
    (middleInverted : firstActor middle = middle⁻¹)
    (otherFixed : secondActor other = other)
    (otherInverted : firstActor other = other⁻¹)
    (lastFirst : firstActor last = last⁻¹)
    (lastSecond : secondActor last = last⁻¹)
    (finalFirst : firstActor final = final)
    (finalSecond : secondActor final = final)
    (product : common * first * middle = other * last * final) :
    first = 1 ∧ last = 1 := by
  have secondImage := congrArg secondActor product
  simp only [map_mul, commonSecond, firstInverted, middleFixed,
    otherFixed, lastSecond, finalSecond] at secondImage
  have firstImage := congrArg firstActor product
  simp only [map_mul, commonFirst, firstFixed, middleInverted,
    otherInverted, lastFirst, finalFirst] at firstImage
  have bothImage := congrArg firstActor secondImage
  simp only [map_mul, map_inv, commonFirst, firstFixed, middleInverted,
    otherInverted, lastFirst, finalFirst, inv_inv] at bothImage
  exact normalized_ratios_eq_one odd common first middle other last final
    product secondImage firstImage bothImage


private theorem split_fixed [Finite G] (odd : Odd (Nat.card G))
    (a b : MulAut G) (hb : Function.Involutive b) (hab : Commute a b)
    (x : G) (hx : a x = x) :
    ∃ u v : G, a u = u ∧ b u = u ∧ a v = v ∧ b v = v⁻¹ ∧ u * v = x := by
  obtain ⟨⟨u,v⟩, ⟨hu,hv,huv⟩, huniq⟩ :=
    Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card odd b hb x
  have hba (z : G) : b (a z) = a (b z) :=
    (congrArg (fun f : MulAut G => f z) hab.eq).symm
  have heq := huniq (a u, a v)
    ⟨by rw [hba,hu], by rw [hba,hv,map_inv], by rw [← map_mul,huv,hx]⟩
  exact ⟨u,v,congrArg Prod.fst heq,hu,congrArg Prod.snd heq,hv,huv⟩

private theorem four_factors_eq [Finite G] (odd : Odd (Nat.card G))
    (a b : MulAut G) (ha : Function.Involutive a) (hb : Function.Involutive b)
    (hab : Commute a b)
    (h x y z h' x' y' z' : G)
    (hh : a h = h ∧ b h = h) (hx : a x = x ∧ b x = x⁻¹)
    (hy : a y = y⁻¹ ∧ b y = y) (hz : a z = z⁻¹ ∧ b z = z⁻¹)
    (hh' : a h' = h' ∧ b h' = h') (hx' : a x' = x' ∧ b x' = x'⁻¹)
    (hy' : a y' = y'⁻¹ ∧ b y' = y') (hz' : a z' = z'⁻¹ ∧ b z' = z'⁻¹)
    (heq : h*x*y*z = h'*x'*y'*z') : h=h' ∧ x=x' ∧ y=y' ∧ z=z' := by
  let U := x'⁻¹ * h'⁻¹ * h * x
  let V := z' * z⁻¹
  have hU : a U = U := by simp [U,hh.1,hx.1,hh'.1,hx'.1]
  obtain ⟨k,u,hka,hkb,hua,hub,hku⟩ := split_fixed odd a b hb hab U hU
  have hV : (a*b) V⁻¹ = V⁻¹ := by
    simp [V, MulAut.mul_apply, hz.1,hz.2,hz'.1,hz'.2]
  have hca : Commute (a*b) a := by
    apply DFunLike.ext
    intro t
    change a (b (a t)) = a (a (b t))
    exact congrArg a ((congrArg (fun f : MulAut G => f t) hab.eq).symm)
  obtain ⟨j,v,hjc,hja,hvc,hva,hjv⟩ := split_fixed odd (a*b) a ha hca V⁻¹ hV
  have hjb : b j = j := by
    have he := congrArg a hjc
    change a (a (b j)) = a j at he
    exact (ha _).symm.trans (he.trans hja)
  have hvb : b v = v⁻¹ := by
    have he := congrArg a hvc
    change a (a (b v)) = a v at he
    exact (ha _).symm.trans (he.trans hva)
  have hVsplit : V = v⁻¹ * j⁻¹ := by
    simpa using (congrArg Inv.inv hjv).symm
  have hnorm : k * u * y = y' * v⁻¹ * j⁻¹ := by
    rw [hku, mul_assoc y', ← hVsplit]
    change (x'⁻¹ * h'⁻¹ * h * x) * y = y' * (z' * z⁻¹)
    calc
      _ = x'⁻¹ * h'⁻¹ * (h*x*y*z) * z⁻¹ := by group
      _ = _ := by rw [heq]; group
  obtain ⟨hu,hv⟩ := normalized_fixed_inverted_ratios_eq_one odd a b
    k u y y' v⁻¹ j⁻¹ hka hkb hua hub hy.2 hy.1 hy'.2 hy'.1
    (by rw [map_inv,hva]) (by rw [map_inv,hvb])
    (by rw [map_inv,hja]) (by rw [map_inv,hjb]) hnorm
  have hzsplit : j⁻¹ * z = z' := by
    have hvone : v = 1 := inv_eq_one.mp hv
    rw [hvone, inv_one, one_mul] at hVsplit
    change z' * z⁻¹ = j⁻¹ at hVsplit
    rw [← hVsplit]
    group
  obtain ⟨p,hp,huniq⟩ :=
    Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card odd a ha z'
  have he1 := huniq (j⁻¹,z) ⟨by rw [map_inv,hja], hz.1, hzsplit⟩
  have he2 := huniq (1,z') ⟨by simp, hz'.1, by simp⟩
  have hjone : j⁻¹ = 1 := congrArg Prod.fst (he1.trans he2.symm)
  have hzz : z = z' := congrArg Prod.snd (he1.trans he2.symm)
  have hkysplit : k*y = y' := by simpa [hu,hv,hjone] using hnorm
  obtain ⟨p,hp,huniq⟩ :=
    Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card odd a ha y'
  have he1 := huniq (k,y) ⟨hka,hy.1,hkysplit⟩
  have he2 := huniq (1,y') ⟨by simp,hy'.1,by simp⟩
  have hyy : y = y' := congrArg Prod.snd (he1.trans he2.symm)
  have hhx : h*x = h'*x' := by
    simpa [hyy,hzz] using heq
  obtain ⟨p,hp,huniq⟩ :=
    Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card odd b hb (h'*x')
  have he1 := huniq (h,x) ⟨hh.2,hx.2,hhx⟩
  have he2 := huniq (h',x') ⟨hh'.2,hx'.2,rfl⟩
  exact ⟨congrArg Prod.fst (he1.trans he2.symm),
    congrArg Prod.snd (he1.trans he2.symm),hyy,hzz⟩

/-- Multiplication of the common-fixed and three fixed/inverted factors is injective. -/
public theorem fixed_inverted_four_factor_injective [Finite G] (odd : Odd (Nat.card G))
    (a b : MulAut G) (ha : Function.Involutive a) (hb : Function.Involutive b)
    (hab : Commute a b) :
    Function.Injective (fun p :
      {h : G // a h = h ∧ b h = h} ×
      {x : G // a x = x ∧ b x = x⁻¹} ×
      {y : G // a y = y⁻¹ ∧ b y = y} ×
      {z : G // a z = z⁻¹ ∧ b z = z⁻¹} =>
      p.1.val * p.2.1.val * p.2.2.1.val * p.2.2.2.val) := by
  rintro ⟨h,x,y,z⟩ ⟨h',x',y',z'⟩ heq
  obtain ⟨eh,ex,ey,ez⟩ := four_factors_eq odd a b ha hb hab
    h x y z h' x' y' z' h.property x.property y.property z.property
    h'.property x'.property y'.property z'.property heq
  exact Prod.ext (Subtype.ext eh)
    (Prod.ext (Subtype.ext ex) (Prod.ext (Subtype.ext ey) (Subtype.ext ez)))
end MulAut
