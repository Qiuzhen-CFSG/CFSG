module

public import Theory.GroupTheory.PGroup.CentralQuotientQuadratic
public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter
public import Theory.ElementaryAbelian.QuadraticPolarImageBound

/-!
# A nonelementary center bounds the elementary central quotient

A finite two-group with elementary binary central quotient, three involutions,
and all involutions central has central quotient of order at most eight when
its center is not elementary abelian.

The center has four elements killed by squaring, hence four square classes.
Since it is not elementary abelian, its square subgroup is nontrivial; Cauchy's
theorem supplies a nonidentity involution in that subgroup. Consequently the
image of the central involutions in the square classes has order at most two.
The anisotropic square map on the central quotient has its polar map in this
image, because commutators are involutions. The restricted-polar-image bound
therefore gives `|P/Z(P)| ≤ 4 · 2`.

Source motivation: MacWilliams, *On 2-groups with no normal abelian subgroups
of rank 3, and their occurrence as Sylow 2-subgroups of finite simple groups*,
Trans. Amer. Math. Soc. 150 (1970), §3, pp. 366–374. The argument here is an
independent square-class argument and uses neither classification nor odd
order automorphisms.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace IsPGroup
private theorem card_involution_square_class_image_le_two
    {A : Type*} [CommGroup A] [Finite A]
    (hA : IsPGroup 2 A)
    (hfour : Nat.card (omega₁ A (p := 2)) = 4)
    (hbad : ¬ IsElementaryAbelian 2 A) :
    let S := (powMonoidHom 2 : A →* A).range
    let K := (powMonoidHom 2 : A →* A).ker
    Nat.card (K.map (QuotientGroup.mk' S)) ≤ 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let square : A →* A := powMonoidHom 2
  let S := square.range
  let K := square.ker
  let r := QuotientGroup.mk' S
  let f := r.comp K.subtype
  have hS : S ≠ ⊥ := by
    intro hbot
    apply hbad
    refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro z
    have hm : z ^ 2 ∈ S := ⟨z, rfl⟩
    rwa [hbot, mem_bot] at hm
  have hdiv : 2 ∣ Nat.card S :=
    (hA.to_subgroup S).card_eq_or_dvd.resolve_left
      (fun h => hS (card_eq_one.mp h))
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 hdiv
  have ht2 : (t : A)^2 = 1 := congrArg Subtype.val (orderOf_eq_prime_iff.mp ht).1
  let u : K := ⟨t, ht2⟩
  have hu : u ∈ f.ker := (QuotientGroup.eq_one_iff _).mpr t.property
  have hne : (⟨u, hu⟩ : f.ker) ≠ 1 := by
    intro he
    apply (orderOf_eq_prime_iff.mp ht).2
    apply Subtype.ext
    exact congrArg (fun v : f.ker => ((v : K) : A)) he
  have hker : 2 ≤ Nat.card f.ker := by
    have : Nontrivial f.ker := nontrivial_iff.mpr ⟨⟨u, hu⟩, 1, hne⟩
    exact Finite.one_lt_card_iff_nontrivial.mpr this
  have hcard : Nat.card f.ker * Nat.card f.range = 4 := by
    rw [← index_ker, card_mul_index]
    change Nat.card (powMonoidHom 2 : A →* A).ker = 4
    rwa [square_ker_eq_omega_one]
  have hrange : f.range = K.map r := by rw [MonoidHom.range_comp, range_subtype]
  change Nat.card (K.map r) ≤ 2
  rw [← hrange]
  nlinarith

/-- With exactly three central involutions, an elementary binary central
quotient has order at most eight if the center is not elementary abelian. -/
public theorem card_center_quotient_le_eight_of_nonelementary_center
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (hquot : IsElementaryAbelian 2 (P ⧸ center P))
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (hbad : ¬ IsElementaryAbelian 2 (center P)) :
    Nat.card (P ⧸ center P) ≤ 8 := by
  let _ := hquot
  let Z := center P
  let S := (powMonoidHom 2 : Z →* Z).range
  let K := (powMonoidHom 2 : Z →* Z).ker
  let W := Z ⧸ S
  let r : Z →* W := QuotientGroup.mk' S
  let R := K.map r
  let : IsElementaryAbelian 2 W := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective S x
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩) }
  have hfour := card_omega_center_eq_four_of_three_central_involutions hcentral hthree
  have hR : Nat.card R ≤ 2 :=
    card_involution_square_class_image_le_two (hP.to_subgroup Z) hfour hbad
  have hW : Nat.card W = 4 := by
    rw [← index_eq_card, index_range, square_ker_eq_omega_one]
    exact hfour
  obtain ⟨square, polar, hsquare, hone, hquadratic, hbilinear, hanisotropic⟩ :=
    exists_anisotropic_center_quotient_square_class_map hcentral
  have hpolar (a b : P ⧸ center P) : polar a b ∈ R := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center P) a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center P) b
    have hsq := hquot.sq_mem_center_of_central_quotient
    have hc : ⁅x,y⁆ ∈ center P := hquot.commutator_le_center_of_central_quotient
      (commutator_mem_commutator (mem_top x) (mem_top y))
    let c : Z := ⟨⁅x,y⁆, hc⟩
    have hcK : c ∈ K :=
      Subtype.ext (hquot.commutatorElement_sq_eq_one_of_central_quotient x y)
    have hmul : (x * y) ^ 2 = x ^ 2 * y ^ 2 * ⁅x,y⁆ := by
      symm
      calc
        x ^ 2 * y ^ 2 * ⁅x,y⁆ = ⁅x,y⁆ * (x ^ 2 * y ^ 2) := mem_center_iff.mp hc _
        _ = x * y * x⁻¹ * (y⁻¹ * x ^ 2) * y ^ 2 := by
          simp only [commutatorElement_def, mul_assoc]
        _ = x * y * x⁻¹ * (x ^ 2 * y⁻¹) * y ^ 2 := by rw [mem_center_iff.mp (hsq x)]
        _ = (x * y) ^ 2 := by simp only [pow_two]; group
    have hprod : (⟨(x*y)^2, hsq (x*y)⟩ : Z) =
        ⟨x^2, hsq x⟩ * ⟨y^2, hsq y⟩ * c := Subtype.ext hmul
    have he : square (QuotientGroup.mk' Z x * QuotientGroup.mk' Z y) =
        square (QuotientGroup.mk' Z x) * square (QuotientGroup.mk' Z y) * r c := by
      rw [← map_mul, hsquare (x*y) (hsq (x*y)), hsquare x (hsq x), hsquare y (hsq y)]
      change r ⟨(x*y)^2, hsq (x*y)⟩ = _
      rw [hprod, map_mul, map_mul]
    have heq : polar (QuotientGroup.mk' Z x) (QuotientGroup.mk' Z y) = r c :=
      mul_left_cancel ((hquadratic _ _).symm.trans he)
    rw [heq]
    exact mem_map_of_mem r hcK
  have hb := IsElementaryAbelian.card_le_card_mul_card_of_polar_mem R square polar
    hone hquadratic hbilinear hanisotropic hpolar
  rw [hW] at hb
  omega
end IsPGroup
