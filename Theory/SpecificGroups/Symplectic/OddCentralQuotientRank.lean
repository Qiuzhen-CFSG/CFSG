module
public import Theory.Quasithin.CentralExtensionRankBound
public import Theory.SpecificGroups.Symplectic.FundamentalPlane
public import Theory.SpecificGroups.SymplecticFour.DefiningRank
public import Theory.SpecificGroups.SL2.CommutingUnipotents

/-!
# Rank-four witnesses in odd symplectic central quotients

A root group in the first hyperbolic plane commutes with the symmetric
shears of a complementary four-space. Their product embeds: any overlap
would make a nonidentity SL₂ transvection central. Iterating the actual tail
embedding gives this rank-four witness in every symplectic rank at least
three. Two hyperbolic planes give twice the field degree in rank two.

The marked scalar involution centralizes these elementary groups. Applying
the odd central-quotient rank bound excludes higher rank and forces a prime
field in rank two for any original quasithin group with odd center. Neither
argument assumes quasithinness of the central quotient.

Source: Aschbacher–Smith A.2.15(2) and A.2.17, printed pp.37–39.
-/

noncomputable section
open Subgroup Matrix Matrix.PSp4Three
open scoped MatrixGroups
namespace Theory.SpecificGroups.Symplectic.OddCentralQuotientRank
open FundamentalPlane
variable {F : Type*} [Field F]

private def extendTwo : (k : ℕ) → Matrix.symplecticGroup (Fin 2) F →*
    Matrix.symplecticGroup (Fin (k+2)) F
  | 0 => MonoidHom.id _
  | k+1 => (tailHom (k+2)).comp (extendTwo k)

private theorem extendTwo_injective (k : ℕ) : Function.Injective (extendTwo (F := F) k) := by
  induction k with
  | zero => exact Function.injective_id
  | succ k ih => exact (tailHom_injective (k+2)).comp ih

private theorem symShear_injective :
    Function.Injective (SymplecticFour.DefiningRank.symShearHom F) := by
  intro a b h
  apply SymplecticFour.DefiningRank.projectiveSymShear_injective F
  exact congrArg (QuotientGroup.mk' _) h

private def complementShear (k : ℕ) : Multiplicative (Fin 3 → F) →* PSp (k+3) F :=
  (projectTail (k+2)).comp ((extendTwo k).comp (SymplecticFour.DefiningRank.symShearHom F))

private theorem complementShear_injective (k : ℕ) :
    Function.Injective (complementShear (F := F) k) :=
  (projectTail_injective (k+2)).comp ((extendTwo_injective k).comp symShear_injective)

private theorem fundamental_shear_commute (k : ℕ)
    (a : SL(2,F)) (v : Multiplicative (Fin 3 → F)) :
    Commute (fundamental (k+2) a) (complementShear k v) :=
  project_factors_commute (k+2)
    (Theory.SpecificGroups.SymplecticRoot.rankOneEquivSL.symm a) _

private def fourShear (k : ℕ) : Multiplicative F × Multiplicative (Fin 3 → F) →*
    PSp (k+3) F :=
  ((fundamental (k+2)).comp (SpecialLinearGroup.upperUnipotentHom F)).noncommCoprod
    (complementShear k) (fun _ _ => fundamental_shear_commute k _ _)

private theorem fourShear_injective (k : ℕ) :
    Function.Injective (fourShear (F := F) k) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨a,b⟩ hab
  change fundamental (k+2) (SpecialLinearGroup.upperUnipotentHom F a) *
    complementShear k b = 1 at hab
  have he : fundamental (k+2) (SpecialLinearGroup.upperUnipotentHom F a) =
      (complementShear k b)⁻¹ := eq_inv_of_mul_eq_one_left hab
  have haZ : SpecialLinearGroup.upperUnipotentHom F a ∈ center SL(2,F) := by
    apply mem_center_iff.mpr
    intro x
    apply fundamental_injective (k+2) (by omega)
    rw [map_mul, map_mul, he]
    exact (fundamental_shear_commute k x b).inv_right.eq
  have ha : a = 1 :=
    (SpecialLinearGroup.transvection_mem_center_iff zero_ne_one a.toAdd).mp haZ
  have hb : b = 1 := by
    rw [ha, map_one, map_one, one_mul] at hab
    apply complementShear_injective k
    simpa only [map_one] using hab
  exact Prod.ext ha hb

private def fourShearCentralizer (k : ℕ) :
    Multiplicative F × Multiplicative (Fin 3 → F) →*
      centralizer ({fundamental (k+2) (-1)} : Set (PSp (k+3) F)) :=
  (fourShear k).codRestrict _ (fun a => by
    apply mem_centralizer_singleton_iff.mpr
    change Commute (fundamental (k+2) (SpecialLinearGroup.upperUnipotentHom F a.1) *
      complementShear k a.2) (fundamental (k+2) (-1))
    apply Commute.mul_left _ ((fundamental_shear_commute k (-1) a.2).symm)
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul]
    congr 1
    simp)

/-- Every symplectic rank at least three has a defining elementary rank-four
subgroup in the centralizer of its fundamental scalar involution. -/
public theorem exists_involution_four_mul_rank [Finite F]
    {r e : ℕ} [Fact r.Prime] [CharP F r] (hr : r ≠ 2)
    (hcard : Nat.card F = r^e) (k : ℕ) :
    ∃ z : PSp (k+3) F, orderOf z = 2 ∧
      4*e ≤ primeRank r (centralizer ({z} : Set (PSp (k+3) F))) := by
  obtain ⟨hz,hz2⟩ := SpecialLinearGroup.map_neg_one_isInvolution hr
    (fundamental (F := F) (k+2)) (fundamental_injective (k+2) (by omega))
  refine ⟨_, orderOf_eq_prime hz2 hz, ?_⟩
  apply primeRank_ge_of_elementary_embedding (A := Multiplicative F × Multiplicative (Fin 3 → F))
    (f := fourShearCentralizer k)
  · intro a
    apply Prod.ext
    · change r • a.1.toAdd = 0
      simp [nsmul_eq_mul]
    · change r • a.2.toAdd = 0
      ext i
      simp [nsmul_eq_mul]
  · change Nat.card (F × (Fin 3 → F)) = _
    rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, hcard, ← pow_mul, ← pow_add]
    congr 1
    omega
  · intro a b h
    exact fourShear_injective k (congrArg Subtype.val h)

/-- Quasithinness of an original odd central cover excludes every symplectic
rank at least three, without any quotient quasithinness assertion. -/
public theorem not_quasithin_of_odd_center_higher_model
    {G : Type*} [Group G] [Finite G] [Finite F]
    {r e : ℕ} [Fact r.Prime] [CharP F r] (hr : r ≠ 2) (he : 1 ≤ e)
    (hcard : Nat.card F = r^e) (k : ℕ)
    (iso : G ⧸ center G ≃* PSp (k+3) F) (ho : Odd (Nat.card (center G))) :
    ¬ IsQuasithin G := by
  intro hqt
  obtain ⟨z,hz,hl⟩ := exists_involution_four_mul_rank hr hcard k
  have hu := CentralExtension.primeRank_involutionCentralizer_le_three_of_odd_center
    hr iso ho hqt hz
  omega

private def secondRankOne : SL(2,F) →* PSp 2 F :=
  (projectTail 1).comp Theory.SpecificGroups.SymplecticRoot.rankOneEquivSL.symm.toMonoidHom

private theorem secondRankOne_injective : Function.Injective (secondRankOne (F := F)) :=
  (projectTail_injective 1).comp Theory.SpecificGroups.SymplecticRoot.rankOneEquivSL.symm.injective

private theorem pairRankOne_commute (a b : SL(2,F)) :
    Commute (fundamental 1 a) (secondRankOne b) :=
  project_factors_commute 1 _ _

/-- The actual two rank-one factors in PSp₄ give twice the field degree in
an involution centralizer. -/
public theorem exists_involution_two_mul_rank [Finite F]
    {r e : ℕ} [Fact r.Prime] [CharP F r] (hr : r ≠ 2)
    (hcard : Nat.card F = r^e) :
    ∃ z : PSp 2 F, orderOf z = 2 ∧
      2*e ≤ primeRank r (centralizer ({z} : Set (PSp 2 F))) := by
  obtain ⟨hz,hz2⟩ := SpecialLinearGroup.map_neg_one_isInvolution hr
    (fundamental (F := F) 1) (fundamental_injective 1 (by decide))
  refine ⟨_, orderOf_eq_prime hz2 hz, ?_⟩
  apply primeRank_ge_of_elementary_embedding
    (SpecialLinearGroup.CommutingUnipotents.pair_exponent r) _
    (SpecialLinearGroup.CommutingUnipotents.centralizerPair
      (fundamental 1) secondRankOne pairRankOne_commute)
    (SpecialLinearGroup.CommutingUnipotents.centralizerPair_injective
      (fundamental 1) secondRankOne pairRankOne_commute
      (fundamental_injective 1 (by decide)) secondRankOne_injective)
  change Nat.card (F × F) = _
  rw [Nat.card_prod, hcard, ← pow_add]
  congr 1
  omega

/-- A quasithin odd central cover of PSp₄ is over a prime field. -/
public theorem fieldExponent_eq_one_of_odd_center
    {G : Type*} [Group G] [Finite G] [Finite F]
    {r e : ℕ} [Fact r.Prime] [CharP F r] (hr : r ≠ 2) (he : 1 ≤ e)
    (hcard : Nat.card F = r^e)
    (iso : G ⧸ center G ≃* PSp 2 F) (ho : Odd (Nat.card (center G)))
    (hqt : IsQuasithin G) : e = 1 := by
  obtain ⟨z,hz,hl⟩ := exists_involution_two_mul_rank hr hcard
  have hu := CentralExtension.primeRank_involutionCentralizer_le_three_of_odd_center
    hr iso ho hqt hz
  omega
end Theory.SpecificGroups.Symplectic.OddCentralQuotientRank
