module

public import Theory.Alternating.proposition_5_2_4
public import Theory.Mathieu.SchurMultipliers.Models
public import Theory.Mathieu.M12.Properties.InvolutionClasses
public import Theory.GroupTheory.PerfectCentralCoverSquareObstruction

/-!
# A perfect central double cover of the native M₁₂

Take the inverse image of the twelve-point Witt-design automorphism group in
Schur's double cover of A₁₂. Perfectness of M₁₂ makes its action even. The
kernel is the original central group of order two. The native involution of
support twelve is conjugate in A₁₂ to the product of three disjoint double
transpositions, whose Schur lift squares to the nonidentity kernel element.
The square obstruction then proves that the inverse image is perfect.

This constructs the lower bound in Aschbacher–Smith, Lemma I.1.3(1), printed
p.407. It does not assert the upper bound or universality of this cover.
-/

open Subgroup GLS3.Chapter5.SchurPresentation

namespace Sporadic.Mathieu.SchurMultipliers.M12DoubleCover

noncomputable section

/-- The native twelve-point M₁₂ action consists of even permutations. -/
public theorem action_even (g : M12) : (g : Equiv.Perm (Fin 12)) ∈
    alternatingGroup (Fin 12) := by
  apply Equiv.Perm.mem_alternatingGroup.mpr
  exact Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp M12.subtype)
    Group.IsPerfect.mem_commutator

/-- The Schur projection followed by the natural twelve-point action. -/
@[expose] public def permutationProjection :
    SchurAlternatingGroup 7 →* Equiv.Perm (Fin 12) :=
  (alternatingGroup (Fin 12)).subtype.comp (schurAlternatingProjection 7)

/-- The inverse image of the actual Witt-design automorphism group M₁₂. -/
@[expose] public def preimage : Subgroup (SchurAlternatingGroup 7) :=
  M12.comap permutationProjection

/-- The concrete central double cover, as a subgroup of Schur's cover of A₁₂. -/
public abbrev Carrier := ↥preimage

/-- The projection onto native M₁₂. -/
@[expose] public def projection : Carrier →* M12 where
  toFun x := ⟨permutationProjection x.1, x.2⟩
  map_one' := Subtype.ext (map_one permutationProjection)
  map_mul' x y := Subtype.ext (map_mul permutationProjection x.1 y.1)

public theorem projection_surjective : Function.Surjective projection := by
  intro g
  obtain ⟨x, hx⟩ := schurAlternatingProjection_surjective 7 ⟨g.1, action_even g⟩
  have heq : permutationProjection x = g.1 := congrArg Subtype.val hx
  exact ⟨⟨x, show permutationProjection x ∈ M12 from heq ▸ g.2⟩, Subtype.ext heq⟩

/-- The marked central involution inherited from the Schur cover. -/
@[expose] public def central : Carrier :=
  ⟨schurAlternatingCentral 7, by
    change permutationProjection (schurAlternatingCentral 7) ∈ M12
    have h := schurAlternatingCentral_mem_ker 7
    have heq := congrArg Subtype.val (MonoidHom.mem_ker.mp h)
    change permutationProjection (schurAlternatingCentral 7) = 1 at heq
    rw [heq]
    exact M12.one_mem⟩

public theorem central_ne_one : central ≠ 1 := by
  intro h
  exact schurAlternatingCentral_ne_one 7 (congrArg Subtype.val h)

public theorem central_sq : central ^ 2 = 1 :=
  Subtype.ext (schurAlternatingCentral_sq 7)

public theorem central_mem_ker : central ∈ projection.ker := by
  apply MonoidHom.mem_ker.mpr
  apply Subtype.ext
  exact congrArg (fun g : alternatingGroup (Fin 12) => g.1)
    (MonoidHom.mem_ker.mp (schurAlternatingCentral_mem_ker 7))

public theorem ker_mem_cases {x : Carrier} (hx : x ∈ projection.ker) :
    x = 1 ∨ x = central := by
  have h : x.1 ∈ (schurAlternatingProjection 7).ker := by
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact congrArg (fun g : M12 => g.1) (MonoidHom.mem_ker.mp hx)
  exact (InvolutionPreimage.ker_mem_cases 7 h).imp Subtype.ext Subtype.ext

public theorem ker_le_center : projection.ker ≤ center Carrier := by
  intro x hx
  rcases ker_mem_cases hx with rfl | rfl
  · exact (center Carrier).one_mem
  · apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact mem_center_iff.mp (schurAlternatingCentral_mem_center 7) y.1

/-- The pullback kernel has exactly two elements. -/
public theorem card_ker : Nat.card projection.ker = 2 := by
  apply (Nat.card_eq_two_iff' (1 : projection.ker)).mpr
  refine ⟨⟨central, central_mem_ker⟩, ?_, ?_⟩
  · intro h
    exact central_ne_one (congrArg Subtype.val h)
  · intro y hy
    rcases ker_mem_cases y.2 with h | h
    · exact (hy (Subtype.ext h)).elim
    · exact Subtype.ext h

private theorem schur_lift_sq_of_support (n m : ℕ) (hdeg : 4 * m ≤ n + 5)
    (hm : 1 ≤ m) (x : SchurAlternatingGroup n)
    (hx2 : schurAlternatingProjection n x ^ 2 = 1)
    (hxne : schurAlternatingProjection n x ≠ 1)
    (hsupport : (schurAlternatingProjection n x).1.support.card = 4 * m) :
    x ^ 2 = schurAlternatingCentral n ^ m := by
  let y := canonicalLift n m hdeg
  have hy2 : (schurAlternatingProjection n y).1 ^ 2 = 1 := by
    have ho := canonicalLift_proj_order_two n m hdeg hm
    have hp := pow_orderOf_eq_one (schurAlternatingProjection n y)
    rw [ho] at hp
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using
      congrArg (fun g : alternatingGroup (Fin (n + 5)) => g.1) hp
  have hcard : (schurAlternatingProjection n x).1.support.card =
      (schurAlternatingProjection n y).1.support.card := by
    rw [canonicalLift_proj, canonicalPerm_support_card]
    exact hsupport
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (alternating_involution_isConj_of_card_support_eq
      (congrArg (fun g : alternatingGroup (Fin (n + 5)) => g.1) hx2)
      hy2 hxne hcard)
  have hsq : x ^ 2 = y ^ 2 :=
    DoubleCoverUniqueness.sq_eq_sq_of_conjugate_images
      (schurAlternatingCovering n) (natCard_ker_schurAlternatingCovering n) hx2 hc
  exact hsq.trans (canonicalLift_sq n m hdeg)

/-- Every lift of the native support-twelve involution has nontrivial square. -/
public theorem lift_involution_sq (x : Carrier) (hx : projection x = m12Involution2A) :
    x ^ 2 = central := by
  let a := schurAlternatingProjection 7 x.1
  have ha : a.1 = (m12Involution2A : Equiv.Perm (Fin 12)) :=
    congrArg Subtype.val hx
  have hi : m12Involution2A ^ 2 = 1 := by
    simpa only [m12Involution2A_order] using pow_orderOf_eq_one m12Involution2A
  have ha2 : a ^ 2 = 1 := by
    apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, ha] using congrArg Subtype.val hi
  have hane : a ≠ 1 := by
    intro h
    have hperm : (m12Involution2A : Equiv.Perm (Fin 12)) = 1 := by
      rw [← ha, h]
      rfl
    have he : m12Involution2A = 1 := Subtype.ext hperm
    have ho := m12Involution2A_order
    rw [he, orderOf_one] at ho
    norm_num at ho
  have hsupport : a.1.support.card = 4 * 3 := by
    rw [ha, m12Involution2A_support_card]
  apply Subtype.ext
  exact (schur_lift_sq_of_support 7 3 (by decide) (by decide) x.1 ha2 hane hsupport).trans
    (central_pow_of_odd 7 (by decide : Odd 3))

/-- The square obstruction makes the full inverse image perfect. -/
public instance carrier_isPerfect : Group.IsPerfect Carrier := by
  obtain ⟨x, hx⟩ := projection_surjective m12Involution2A
  exact PerfectCentralCovering.isPerfect_of_central_binary_kernel_of_square
    projection projection_surjective ker_le_center central central_sq
    (fun _ h => ker_mem_cases h) x (lift_involution_sq x hx)

/-- A finite perfect central double cover of the actual M₁₂. -/
@[expose] public def cover : PerfectCentralCovering.Cover Carrier M12 where
  toMonoidHom := projection
  surjective := projection_surjective
  ker_le_center := ker_le_center
  isPerfect := inferInstance

public theorem cover_card_ker : Nat.card cover.toMonoidHom.ker = 2 := card_ker

/-- The marked square also rules out a homomorphic section of this projection. -/
public theorem not_split : ¬ ∃ s : M12 →* Carrier,
    projection.comp s = MonoidHom.id M12 := by
  rintro ⟨s, hs⟩
  have hx : projection (s m12Involution2A) = m12Involution2A :=
    DFunLike.congr_fun hs m12Involution2A
  have hi : m12Involution2A ^ 2 = 1 := by
    simpa only [m12Involution2A_order] using pow_orderOf_eq_one m12Involution2A
  apply central_ne_one
  rw [← lift_involution_sq _ hx, ← map_pow, hi, map_one]

end

end Sporadic.Mathieu.SchurMultipliers.M12DoubleCover
