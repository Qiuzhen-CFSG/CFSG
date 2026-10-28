module
public import Theory.SpecificGroups.PSL3.RadicalParabolicTwoSignalizers.AutomorphismSignalizers.Inner
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Inner
public import Theory.SpecificGroups.GL2.PrimeCardinality
public import Theory.GroupTheory.CentralCoprimePrimeLift

public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Graph.Equivalence
public import Theory.SpecificGroups.SU3.TernaryOrthogonalThreeRank.Components
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Defining-prime two-signalizers in odd projective degree three

A subgroup of order p² cannot centralize an involution: an inner involution
has a GL₂(p) centralizer quotient, and an outer involution has an orthogonal
fixed group of order p(p²−1). For a normalized two-subgroup, lift its center
through the scalar kernel to SL₃(p). The degree-three abelian automizer
embeds in S₃, so the defining-prime subgroup centralizes that center.
This kills the inner two-subgroup. The remaining automorphisms fix the
order-p² subgroup pointwise and are killed by the same involution bound.

The argument keeps nontrivial scalar kernels and includes all automorphisms.
It supplies the signalizer step of Aschbacher--Smith 1.3.8, printed p.513,
without assuming marked-parabolic recognition or restricting to p = 5.
-/

public noncomputable section
open scoped MatrixGroups IsMulCommutative
open Subgroup
namespace CFSG.Quasithin.Chapter3.RadicalCentralization.ChosenStars.Signalizers
variable {p : ℕ} [Fact p.Prime]
local notation "F" => ZMod p
local notation "A" => PSL(3,F)

private theorem prime_action_perm_three (hp : 3 < p) {B : Type*} [Group B]
    (hB : IsPGroup p B) (f : B →* Equiv.Perm (Fin 3)) (b : B) : f b = 1 := by
  have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hr := hB.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hb : f.range = ⊥ := by
    apply card_eq_one.mp
    rcases hr.card_eq_or_dvd with h | h
    · exact h
    · have hd := h.trans f.range.card_subgroup_dvd_card
      rw [hc] at hd
      have : p ∣ 2 ∨ p ∣ 3 := (Fact.out : p.Prime).dvd_mul.mp hd
      rcases this with hd | hd <;> have := Nat.le_of_dvd (by decide) hd <;> omega
  exact mem_bot.mp (hb ▸ (show f b ∈ f.range from ⟨b,rfl⟩))

private theorem prime_normalizes_abelian_two_centralizes
    (hp : 3 < p) (B Q : Subgroup (GL (Fin 3) F))
    (hB : IsPGroup p B) (hQ : IsPGroup 2 Q) [IsMulCommutative Q]
    (hn : B ≤ normalizer (Q : Set (GL (Fin 3) F))) :
    B ≤ centralizer (Q : Set (GL (Fin 3) F)) := by
  obtain ⟨j, hj⟩ := Representation.rankThree_abelian_automizer_embeds_perm
    p 2 (by omega) Q hQ
  let i : B →* normalizer (Q : Set (GL (Fin 3) F)) := inclusion hn
  let f := (j.comp Q.normalizerMonoidHom.rangeRestrict).comp i
  intro b hb
  have he : Q.normalizerMonoidHom (i ⟨b,hb⟩) = 1 := by
    have hh : Q.normalizerMonoidHom.rangeRestrict (i ⟨b,hb⟩) = 1 := by
      apply hj
      change f ⟨b,hb⟩ = j 1
      rw [map_one]
      exact prime_action_perm_three hp hB f ⟨b,hb⟩
    exact congrArg Subtype.val hh
  have hk : i ⟨b,hb⟩ ∈ Q.normalizerMonoidHom.ker := he
  rw [normalizerMonoidHom_ker] at hk
  exact hk

/-- No projective involution centralizes a defining-prime subgroup of order p². -/
theorem involution_not_centralized (hp : 3 < p)
    (P : Subgroup A) (hcard : Nat.card P = p ^ 2)
    (t : A) (ht : orderOf t = 2) : ¬ P ≤ centralizer ({t} : Set A) := by
  intro hP
  have h2 : (2 : F) ≠ 0 := by
    change ¬ ((2 : ℕ) : F) = 0
    rw [CharP.cast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  obtain ⟨f,hf⟩ := Matrix.PSL3.OddInvolutionFixed.exists_gl2_surjective_centralizer t ht h2
  have hd := (card_dvd_of_le hP).trans (card_dvd_of_surjective f hf)
  rw [hcard] at hd
  exact Matrix.GeneralLinearGroup.prime_sq_not_dvd_card hd

/-- A defining-prime subgroup of order p² normalizes no nontrivial two-subgroup
of PSL₃(p). The proof includes the nontrivial scalar center of SL₃(p). -/
theorem projective_normalized_two_eq_bot (hp : 3 < p)
    (P S : Subgroup A) (hP : IsPGroup p P) (hc : Nat.card P = p ^ 2)
    (hS : IsPGroup 2 S) (hn : P ≤ normalizer (S : Set A)) : S = ⊥ := by
  let π := Matrix.PSL3.projection F
  have hcentral : π.ker ≤ center SL(3,F) := (Matrix.PSL3.projection_ker F).le
  have hk : Nat.card π.ker ∣ 3 := by
    rw [Matrix.PSL3.projection_ker]
    exact Matrix.SL3.card_center_dvd_three F
  obtain ⟨B,hB,hBP,_,_,_⟩ := exists_prime_lift_of_central_coprime π
    (Matrix.PSL3.projection_surjective F) hcentral
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) hp) |>.of_dvd_right hk) P hP
  obtain ⟨U,hU,hUS,hnU,_,hiU⟩ := exists_prime_lift_of_central_coprime π
    (Matrix.PSL3.projection_surjective F) hcentral
    ((show Nat.Coprime 2 3 from by decide).of_dvd_right hk) S hS
  have hBU : B ≤ normalizer (U : Set SL(3,F)) := by
    rw [← hnU, ← map_le_iff_le_comap, hBP]
    exact hn
  let Z := (center U).map U.subtype
  have hZ : IsPGroup 2 Z := (hU.to_subgroup _).map U.subtype
  let f : SL(3,F) →* GL (Fin 3) F := Matrix.SpecialLinearGroup.toGL
  have hf : Function.Injective f := Matrix.SpecialLinearGroup.toGL_injective
  let : IsMulCommutative Z := Subgroup.map_isMulCommutative (center U) U.subtype
  let : IsMulCommutative (Z.map f) := Subgroup.map_isMulCommutative Z f
  have hBZ := hBU.trans (normalizer_le_normalizer_characteristic_image U (center U))
  have hcen := prime_normalizes_abelian_two_centralizes hp (B.map f) (Z.map f)
    (hB.map f) (hZ.map f) ((map_mono hBZ).trans (Z.le_normalizer_map f))
  have hZB : Z ≤ centralizer (B : Set SL(3,F)) := by
    intro z hz b hb
    apply hf
    simpa only [map_mul] using ((hcen (mem_map_of_mem f hb)) _ (mem_map_of_mem f hz)).symm
  by_contra hne
  have hUne : U ≠ ⊥ := by intro he; rw [he,Subgroup.map_bot] at hUS; exact hne hUS.symm
  let : Nontrivial U := (nontrivial_iff_ne_bot U).mpr hUne
  let : Nontrivial (center U) := hU.center_nontrivial
  have hd : 2 ∣ Nat.card (center U) := by
    rcases (hU.to_subgroup (center U)).card_eq_or_dvd with h | h
    · exact ((nontrivial_iff_ne_bot (center U)).mp inferInstance (card_eq_one.mp h)).elim
    · exact h
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' 2 hd
  let tU : U := t.val
  have htU : orderOf tU = 2 := (orderOf_injective (center U).subtype (center U).subtype_injective t).trans ht
  have htπ : orderOf (π (tU : SL(3,F))) = 2 :=
    (orderOf_injective (π.comp U.subtype) hiU tU).trans htU
  apply involution_not_centralized hp P hc _ htπ
  rw [← hBP]
  rintro _ ⟨b,hb,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have htb := hZB (mem_map_of_mem U.subtype t.property) b hb
  exact (map_mul π b (tU : SL(3,F))).symm.trans ((congrArg π htb).trans (map_mul π (tU : SL(3,F)) b))


/-- Every involution in the full projective automorphism group has fixed-point
order indivisible by the square of the defining prime. -/
theorem involution_fixed_not_square (hp : 3 < p) (a : MulAut A)
    (ha : orderOf a = 2) : ¬ p ^ 2 ∣ Nat.card a.fixedSubgroup := by
  let : IsSimpleGroup A := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect A := Atlas.psl_perfect 3 (by decide)
  have hns : ¬ Group.IsSolvable A := Group.IsPerfect.not_isSolvable A
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  have hz : center A = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)
  have h2 : (2 : F) ≠ 0 := by
    change ¬ ((2 : ℕ) : F) = 0
    rw [CharP.cast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  by_cases hi : ∃ t : A, a = MulAut.conj t
  · obtain ⟨t,rfl⟩ := hi
    have ht : orderOf t = 2 :=
      (orderOf_injective MulAut.conj (MulAut.conj_injective_of_center_eq_bot hz) t).symm.trans ha
    obtain ⟨f,hf⟩ := Matrix.PSL3.OddInvolutionFixed.exists_gl2_surjective_centralizer t ht h2
    rw [MulAut.fixedSubgroup_conj]
    exact fun hd => Matrix.GeneralLinearGroup.prime_sq_not_dvd_card
      (hd.trans (card_dvd_of_surjective f hf))
  · obtain ⟨J,hJ,⟨e⟩⟩ := Matrix.PSL3.OddInvolutionFixed.outer_fixed_equiv_orthogonal
      hns Fact.out ((Fact.out : p.Prime).odd_of_ne_two (by omega)) (Nat.card_zmod p)
      a (ha ▸ pow_orderOf_eq_one a) hi
    obtain ⟨e'⟩ := BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.orthogonal_equiv_split J hJ h2
    rw [Nat.card_congr (e.trans e').toEquiv,
      BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.card_splitOrthogonal_specialSubgroup h2,
      Nat.card_zmod]
    intro hd
    have hp' := (Fact.out : p.Prime)
    rw [pow_two, Nat.mul_dvd_mul_iff_left hp'.pos] at hd
    have hsum : p ∣ (p * p - 1) + 1 := by
      rw [Nat.sub_add_cancel (by nlinarith [hp'.two_le] : 1 ≤ p*p)]
      exact dvd_mul_right p p
    exact hp'.not_dvd_one ((Nat.dvd_add_iff_right hd).mpr hsum)

/-- The full automorphism group admits no nontrivial two-signalizer for an
order-p² defining subgroup. No marked-parabolic recognition is required. -/
theorem automorphism_normalized_two_eq_bot (hp : 3 < p)
    (P : Subgroup A) (hP : IsPGroup p P) (hc : Nat.card P = p ^ 2)
    (U : Subgroup (MulAut A)) (hU : IsPGroup 2 U)
    (hn : P.map (MulAut.conj : A →* MulAut A) ≤ normalizer (U : Set (MulAut A))) :
    U = ⊥ := by
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  have hz : center A = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)
  have hi := MulAut.conj_injective_of_center_eq_bot hz
  let S := U.comap (MulAut.conj : A →* MulAut A)
  have hS : IsPGroup 2 S := hU.comap_of_injective _ hi
  have hnS : P ≤ normalizer (S : Set A) := by
    rw [le_normalizer_iff]
    intro a ha x hx
    change MulAut.conj (a*x*a⁻¹) ∈ U
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hn (mem_map_of_mem _ ha)) _).mp hx
  have hbot := projective_normalized_two_eq_bot hp P S hP hc hS hnS
  have hfix (a : MulAut A) (ha : a ∈ U) : P ≤ a.fixedSubgroup := by
    intro x hx
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    have hm : MulAut.conj (x * (a x)⁻¹) =
        MulAut.conj x * a * (MulAut.conj x)⁻¹ * a⁻¹ := by
      ext y
      simp [MulAut.conj_apply,mul_assoc]
    have he : x * (a x)⁻¹ ∈ S := by
      change MulAut.conj (x * (a x)⁻¹) ∈ U
      rw [hm]
      exact U.mul_mem
        ((mem_normalizer_iff.mp (hn (mem_map_of_mem _ hx)) _).mp ha) (U.inv_mem ha)
    exact (mul_inv_eq_one.mp (mem_bot.mp (hbot ▸ he))).symm
  by_contra hne
  have hd : 2 ∣ Nat.card U := by
    rcases hU.card_eq_or_dvd with h | h
    · exact (hne (card_eq_one.mp h)).elim
    · exact h
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 2 hd
  have ha' : orderOf (a : MulAut A) = 2 :=
    (orderOf_injective U.subtype U.subtype_injective a).trans ha
  exact involution_fixed_not_square hp a ha' (hc ▸ card_dvd_of_le (hfix a a.property))

end CFSG.Quasithin.Chapter3.RadicalCentralization.ChosenStars.Signalizers
