module
public import Theory.SpecificGroups.SL2.CentralTwoExtensions

/-!
# Small stabilizers in central quotients of SL₂

The center of odd-characteristic SL₂ has order two. Thus the full preimage
of a subgroup in a center-kernel quotient has twice its order. In particular,
a projective four-group lifts to the actual quaternion group of order eight:
its lift has exponent at most four and a unique involution, so the cyclic
alternative in the two-group classification is impossible.

The maps and preimage subgroups are retained literally. This supplies the
S₃ order bound and the quaternion lifts in Aschbacher--Smith 13.1.12(1),
printed pp.872--873; its original-action applications are in Chapter13's
`ModuleOrbits.RadicalStabilizers.Models`.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup

/-- The center of odd-characteristic SL₂ has exactly two elements. -/
theorem center_rank_two_card {F : Type*} [Field F] (hF : (2 : F) ≠ 0) :
    Nat.card (center SL(2,F)) = 2 := by
  have hn : (-1 : SL(2,F)) ≠ 1 := by
    intro h
    have he := congrArg (fun x : SL(2,F) => x.val 0 0) h
    have he' : (-1 : F) = 1 := by simpa using he
    exact hF (by linear_combination -he')
  have hs : (center SL(2,F) : Set SL(2,F)) = {1, -1} := by
    ext x
    constructor
    · intro hx
      obtain ⟨a,ha,he⟩ := mem_center_iff.mp hx
      simp only [Fintype.card_fin] at ha
      rcases sq_eq_one_iff.mp ha with rfl | rfl
      · exact Or.inl (Subtype.ext (by simpa using he.symm))
      · exact Or.inr (Subtype.ext (by simpa [← Matrix.diagonal_neg] using he.symm))
    · rintro (rfl | rfl)
      · exact one_mem _
      · apply Subgroup.mem_center_iff.mpr
        intro y
        simp
  change Nat.card ↥(center SL(2,F) : Set SL(2,F)) = 2
  rw [Nat.card_coe_set_eq,hs,Set.ncard_pair hn.symm]

private theorem pow_four_of_square_central {F : Type*} [Field F] {x : SL(2,F)}
    (hx : x ^ 2 ∈ center SL(2,F)) : x ^ 4 = 1 := by
  obtain ⟨a,ha,he⟩ := mem_center_iff.mp hx
  simp only [Fintype.card_fin] at ha
  have hs : x ^ 2 = 1 ∨ x ^ 2 = -1 := by
    rcases sq_eq_one_iff.mp ha with rfl | rfl
    · exact Or.inl (Subtype.ext (by simpa using he.symm))
    · exact Or.inr (Subtype.ext (by simpa [← Matrix.diagonal_neg] using he.symm))
  rcases hs with hs | hs <;> rw [show 4 = 2 * 2 from rfl,pow_mul,hs] <;> simp

private theorem quaternion_of_card_eight {F : Type*} [Field F]
    (hF : (2 : F) ≠ 0) (K : Subgroup SL(2,F)) [Finite K]
    (hc : Nat.card K = 8) (hexp : ∀ x : K, x ^ 4 = 1) :
    Nonempty (K ≃* QuaternionGroup 2) := by
  have hp : IsPGroup 2 K := IsPGroup.of_card (n := 3) hc
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (by rw [hc]; decide)
  have hi (x : K) (hx : orderOf x = 2) : (x : SL(2,F)) = -1 := by
    have hs : (x : SL(2,F)) ^ 2 = 1 := congrArg Subtype.val
      (show x ^ 2 = 1 by simpa only [hx] using pow_orderOf_eq_one x)
    have hd : (toGL (x : SL(2,F))).det = 1 := by apply Units.ext; exact x.val.property
    rcases GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one hF
      (toGL (x : SL(2,F))) (by rw [← map_pow,hs,map_one]) hd with he | he
    · have hx1 : x = 1 := Subtype.ext (toGL_injective (by simpa using he))
      simp [hx1] at hx
    · exact Subtype.ext (congrArg Units.val he)
  rcases hp.isCyclic_or_quaternion_of_unique_involution
      ⟨z,hz,fun x hx => Subtype.ext ((hi x hx).trans (hi z hz).symm)⟩ with hcyc | ⟨n,hn,⟨e⟩⟩
  · let := hcyc
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hexp
    rw [IsCyclic.exponent_eq_card,hc] at h
    norm_num at h
  · have hh := Nat.card_congr e.toEquiv
    rw [hc,Nat.card_eq_fintype_card,QuaternionGroup.card] at hh
    have hn2 : 2 ^ (n - 2) = 2 := by omega
    rw [hn2] at e
    exact ⟨e⟩

end Matrix.SpecialLinearGroup

namespace MonoidHom
open Matrix.SpecialLinearGroup
variable {E B : Type*} [Group E] [Finite E] [Group B] [Finite B]

omit [Finite E] in
/-- The order of the full preimage under a surjection. -/
theorem card_comap_of_surjective (f : E →* B) (hf : Function.Surjective f)
    (A : Subgroup B) : Nat.card (A.comap f) = Nat.card A * Nat.card f.ker := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero A.index_ne_zero_of_finite)
  calc
    Nat.card (A.comap f) * A.index = Nat.card E := by
      rw [← A.index_comap_of_surjective hf]
      exact (A.comap f).card_mul_index
    _ = Nat.card B * Nat.card f.ker := by
      have hh := f.ker.index_mul_card
      rw [index_ker, f.range_eq_top.mpr hf, Nat.card_congr Subgroup.topEquiv.toEquiv] at hh
      exact hh.symm
    _ = (Nat.card A * Nat.card f.ker) * A.index := by
      rw [← A.card_mul_index]
      ac_rfl

/-- Every projective four-group has a literal quaternion preimage. -/
theorem quaternion_comap_of_four {F : Type*} [Field F]
    (hF : (2 : F) ≠ 0) (e : E ≃* SL(2,F))
    (f : E →* B) (hf : Function.Surjective f) (hk : f.ker = center E)
    (A : Subgroup B) (hc : Nat.card A = 4) (hs : ∀ a : A, a ^ 2 = 1) :
    Nonempty (A.comap f ≃* QuaternionGroup 2) := by
  have hz : Nat.card f.ker = 2 := by
    rw [hk,Nat.card_congr (centerCongr e).toEquiv]
    exact center_rank_two_card hF
  have hcard : Nat.card (A.comap f) = 8 := by
    rw [f.card_comap_of_surjective hf A,hc,hz]
  let K := (A.comap f).map e.toMonoidHom
  let ek : A.comap f ≃* K := e.subgroupMap _
  let : Finite K := Finite.of_equiv (A.comap f) ek.toEquiv
  have hK : Nat.card K = 8 := (Nat.card_congr ek.toEquiv).symm.trans hcard
  have hpow (x : K) : x ^ 4 = 1 := by
    obtain ⟨y,rfl⟩ := ek.surjective x
    apply Subtype.ext
    apply pow_four_of_square_central
    change e y ^ 2 ∈ center SL(2,F)
    rw [← map_pow]
    apply (centerCongr e) ⟨(y : E)^2,?_⟩ |>.property
    rw [← hk,MonoidHom.mem_ker,map_pow]
    exact congrArg Subtype.val (hs ⟨f y,y.property⟩)
  obtain ⟨w⟩ := quaternion_of_card_eight hF K hK hpow
  exact ⟨ek.trans w⟩

end MonoidHom
