module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.AmbientExtensions.Orders
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import GorensteinWalter.PGL2InnerAction
public import Theory.Mathieu.M12.Properties.AutCover
public import Theory.Mathieu.M12.Properties.Order

/-!
# Permutation rows and arithmetic exclusions in the ambient comparison

The small offender actor excludes the solvable row by order, the
large-prime rank-one rows by odd divisibility, and both Mathieu rows by
their actual embedded M₁₂. The literal triple-seven coverings have odd
part 945, impossible for any small actor with two-group quotient.
Thus rows (7) and (9) give their specified A₇ and S₇ equivalences.

Only the rank-one rows (6),(8) and degree-three rows (10),(11) remain.
Their complete source records, including extension actions, are retained.
This is a reduction; it does not assert recognition in those four rows.
Source: Aschbacher–Smith, F.6.18, pp.309–310; 15.4.18, p.1163.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace QuasisimpleComparison.AmbientExtensions
open GoldschmidtAlternatives
universe u v
variable {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D} {K : GroupClass.{u}}

/-- Both alternatives in row (2) are smaller than the actor itself. -/
theorem not_case2 (s : SmallActorModel (offenderSubgroup ρ)) : ¬ Case2 D := by
  have hl := (actor_card_lower s).trans
    (Nat.card_le_card_of_injective (offenderSubgroup ρ).subtype
      (offenderSubgroup ρ).subtype_injective)
  intro hr
  rcases hr with he | he
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv] at hl
    norm_num [S3, Nat.card_prod, Nat.card_eq_fintype_card,
      Fintype.card_perm, Nat.factorial] at hl
  · rw [he.card, HeisenbergPrime.card] at hl
    norm_num [E4, C, Nat.card_prod] at hl

private theorem psl_prime_dvd {A : Type*} [Group A] {p : ℕ} (hp : p.Prime)
    (ho : Odd p) (hm : ClassicalGroup.IsPSL A 2 p) : p ∣ Nat.card A := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  rw [Nat.card_congr e.toEquiv]
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hF ▸ ho)
  have hd : p ∣ Nat.card PSL(2,F) * 2 := by
    rw [hc, hF]
    exact dvd_mul_right _ _
  rcases hp.dvd_mul.mp hd with hd | hd
  · exact hd
  · have he := (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one
    have hh := Nat.odd_iff.mp ho
    omega

/-- The PSL₂(p) factor in row (3) supplies its forbidden defining prime. -/
theorem not_case3 (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ)) : ¬ Case3 G₁ G₂ := by
  rintro ⟨p, A, _, hp, hp24, hm, _⟩
  exact no_large_prime h s hp (by omega)
    ((psl_prime_dvd hp (Nat.odd_iff.mpr (by omega)) hm).trans A.card_subgroup_dvd_card)

/-- The prime parameters in row (4) cannot occur in an ambient small actor extension. -/
theorem not_case4 (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ)) : ¬ Case4 G₁ G₂ := by
  rintro ⟨p, hp, hp24, hm, _⟩
  exact no_large_prime h s hp (by omega)
    (psl_prime_dvd hp (Nat.odd_iff.mpr (by omega)) hm)

/-- The literal PSL₂ inclusion into PGL₂ excludes row (5). -/
theorem not_case5 (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ)) : ¬ Case5 G₁ G₂ := by
  rintro ⟨p, hp, hp24, ⟨F, _, _, hF, ⟨e⟩⟩, _⟩
  have hd := psl_prime_dvd hp (Nat.odd_iff.mpr (by omega))
    (show ClassicalGroup.IsPSL PSL(2,F) 2 p from ⟨F, inferInstance, inferInstance,
      hF, ⟨MulEquiv.refl _⟩⟩)
  have hi : Nat.card PSL(2,F) ∣ Nat.card PGL(2,F) :=
    card_dvd_of_injective Matrix.ProjectiveSpecialLinearGroup.toPGL
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  exact no_large_prime h s hp (by omega)
    (by simpa only [Nat.card_congr e.toEquiv] using hd.trans hi)

/-- The actual triple-seven central quotient has forbidden odd part 945. -/
theorem not_tripleSeven (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ)) : ¬ TripleAlternating D 7 := by
  intro hc
  apply ambient_not_945 h s
  rw [tripleAlternating_card hc]
  norm_num [Nat.factorial]

/-- The same obstruction applies to the genuine symmetric triple-seven cover. -/
theorem not_tripleSymmetricSeven (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ)) : ¬ TripleSymmetric D 7 := by
  intro hc
  apply ambient_not_945 h s
  rw [tripleSymmetric_card hc]
  norm_num [Nat.factorial]

/-- Row (7) now supplies its actual A₇ model. -/
theorem case7_model (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ)) (hr : Case7 G₁ G₂) :
    SmallAmbientModel D := by
  rcases hr.1 with he | hc
  · obtain ⟨e⟩ := he
    exact Or.inl (.alternatingSeven e)
  · exact (not_tripleSeven h s hc).elim

/-- Row (9) supplies its actual S₇ model. -/
theorem case9_model (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ)) (hr : Case9 G₁ G₂) :
    SmallAmbientModel D := by
  rcases hr.1 with he | hc
  · obtain ⟨e⟩ := he
    exact Or.inl (.symmetricSeven e)
  · exact (not_tripleSymmetricSeven h s hc).elim

/-- M₁₂ has an odd prime divisor absent from the offender actor. -/
theorem not_case12 (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ)) : ¬ Case12 G₁ G₂ := by
  rintro ⟨⟨e⟩, _⟩
  apply no_large_prime h s (by decide : Nat.Prime 11) (by decide)
  rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m12_order]
  decide

/-- The faithful inner-automorphism map retains this divisor in Aut(M₁₂). -/
theorem not_case13 (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ)) : ¬ Case13 G₁ G₂ := by
  rintro ⟨⟨e⟩, _⟩
  have hd : 11 ∣ Nat.card Sporadic.Mathieu.M12 := by
    rw [Sporadic.Mathieu.m12_order]
    decide
  have hi := card_dvd_of_injective Sporadic.Mathieu.m12InnerAut
    Sporadic.Mathieu.m12InnerAut_injective
  apply no_large_prime h s (by decide : Nat.Prime 11) (by decide)
  rw [Nat.card_congr e.toEquiv]
  exact hd.trans hi

/-- The remaining rank-one rows retain all local markings and the prescribed
quadratic-field action. -/
def RankOneRows (G₁ G₂ : Subgroup D) : Prop := Case6 G₁ G₂ ∨ Case8 G₁ G₂

/-- The degree-three rows retain both signs, special/projective alternatives,
and the actual graph action. -/
def DegreeThreeRows (G₁ G₂ : Subgroup D) : Prop := Case10 G₁ G₂ ∨ Case11 G₁ G₂

private theorem ordered_reduction (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ)) (hr : RemainingOrdered G₁ G₂) :
    SmallAmbientModel D ∨ RankOneRows G₁ G₂ ∨ DegreeThreeRows G₁ G₂ := by
  rcases hr with h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · exact (not_case2 s h2).elim
  · exact (not_case3 h s h3).elim
  · exact (not_case4 h s h4).elim
  · exact (not_case5 h s h5).elim
  · rcases h6.1 with hc | _
    · exact Or.inl (Or.inl (.tripleSix hc))
    · exact Or.inr (Or.inl (Or.inl h6))
  · exact Or.inl (case7_model h s h7)
  · rcases h8.1 with hc | _
    · exact Or.inl (Or.inr hc)
    · exact Or.inr (Or.inl (Or.inr h8))
  · exact Or.inl (case9_model h s h9)
  · exact Or.inr (Or.inr (Or.inl h10))
  · exact Or.inr (Or.inr (Or.inr h11))
  · exact (not_case12 h s h12).elim
  · exact (not_case13 h s h13).elim

private theorem swap (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂) :
    ProjectiveLine.ClassifiedAction K ρ G₂ G₁ :=
  ⟨h.faithful, h.twoCore, h.threePrimeCore, h.triple.symm, h.goldschmidt.symm,
    h.ffHypothesis, h.ffWitness, h.ffAlternatives, h.quotient_twoGroup, h.sylow_fixedSpace⟩

/-- Exhaust all twelve source rows and both generator orientations. Only the
four genuine classical rows remain to be recognized. -/
theorem comparison_reduction (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (s : SmallActorModel (offenderSubgroup ρ)) :
    SmallAmbientModel D ∨ (RankOneRows G₁ G₂ ∨ RankOneRows G₂ G₁) ∨
      (DegreeThreeRows G₁ G₂ ∨ DegreeThreeRows G₂ G₁) := by
  rcases h.goldschmidt with hr | hr
  · rcases ordered_reduction h s hr with hs | hr | hr
    · exact Or.inl hs
    · exact Or.inr (Or.inl (Or.inl hr))
    · exact Or.inr (Or.inr (Or.inl hr))
  · rcases ordered_reduction (swap h) s hr with hs | hr | hr
    · exact Or.inl hs
    · exact Or.inr (Or.inl (Or.inr hr))
    · exact Or.inr (Or.inr (Or.inr hr))

end QuasisimpleComparison.AmbientExtensions
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
