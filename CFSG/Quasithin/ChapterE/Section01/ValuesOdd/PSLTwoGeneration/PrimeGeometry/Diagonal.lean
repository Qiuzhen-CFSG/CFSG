module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LocalModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.Actors
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.OuterPlacement
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.NormalTransfer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# The prime-field PGL₂ placement calculation

The outer four-group branch is discharged by the low-torus construction and
the explicit maximal-overgroup models. If every actor in the Sylow lies in
PSL₂, transfer the already required PSL₂ geometry through the normal
index-two subgroup, retaining the actual weak closure and Sylow intersections.

The final theorem discharges both inputs of the conditional assembly using
the prime-field PSL₂ geometry and maximal-overgroup calculation, and transports
the resulting witnesses through an actual isomorphism to the ambient group.
It proves the concrete PGL₂ placement needed in E.1.14(6); the intrinsic E1
verification and final E-generation assembly remain with its consumers.

Source: Aschbacher--Smith E.1.2 and E.1.14(6), printed pp.210 and 214;
Aschbacher (1982), Lemma 4.10.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal

open Subgroup GorensteinWalter

/-- Assemble the outer torus calculation with geometry in the actual normal
PSL₂ subgroup. Both independent classification inputs remain explicit. -/
theorem concreteGeometry_of_psl_geometry_and_overgroups
    (F : Type*) [Field F] [Finite F] [Finite (PGL2 F)] [Finite (PSL2 F)]
    (hF : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (hinner : ∀ Q : Sylow 2 (PSL2 F), ConcreteLocalGeometryAt Q)
    (hover : ∀ (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F)),
      IsCoatom M → (T : Subgroup (PGL2 F)) ≤ M → SylowOvergroupModel F M) :
    ∀ T : Sylow 2 (PGL2 F), ConcreteLocalGeometryAt T := by
  intro T Ω hΩ hlarge M hM hTM hNM
  classical
  by_cases houter : ∃ A ∈ Ω, A ≤ (T : Subgroup (PGL2 F)) ∧ IsKleinFour A ∧
      ¬ A ≤ commutator (PGL2 F)
  · obtain ⟨A, hA, hAT, hAF, hAJ⟩ := houter
    exact ⟨A, hA, hAT, hAF,
      outer_kleinFour_escape_of_overgroup_model F hF hcard T A M hAF hAT hAJ
        hTM (hover T M hM hTM)⟩
  · let J := commutator (PGL2 F)
    have hJ : J.index = 2 := by
      change (commutator (PGL2 F)).index = 2
      rw [pgl2_commutator_eq_psl2_range_of_card_gt_three F hF hcard]
      exact pgl2_psl2Range_index_eq_two F hF
    have hquot : IsPGroup 2 (PGL2 F ⧸ J) :=
      IsPGroup.of_card (n := 1) (by
        change J.index = 2 ^ 1
        simpa using hJ)
    have hgen : (T : Subgroup (PGL2 F)) ⊔ J = ⊤ :=
      T.sup_eq_top_of_quotient_isPGroup J hquot
    have eJ : Nonempty (J ≃* PSL2 F) :=
      commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three F hF hcard
        (MulEquiv.refl (PGL2 F))
    have hgeometryJ : ∀ Q : Sylow 2 J, ConcreteLocalGeometryAt Q :=
      concreteGeometry_of_equiv eJ.some.symm hinner
    apply inner_escape_of_normal_geometry J T hgen hgeometryJ Ω hΩ hlarge
      ?_ M hTM hM.ne_top hNM
    intro A hA hAT
    by_cases hAb : A = ⊥
    · exact hAb ▸ bot_le
    · have hAF := actor_isKleinFour_of_rank (pgl_twoRank_le_two F hF)
        A (hΩ.1 A hA) hAb (hlarge A hA hAT hAb)
      by_contra hAJ
      exact houter ⟨A, hA, hAT, hAF, hAJ⟩

/-- Every Sylow two-subgroup of an actual PGL₂ model over a prime field of
odd order greater than five has the concrete local geometry required in the
large-family branch of E.1.14(6). Outer actors use prime dihedral tori, and
families entirely inside PSL₂ use its normal-subgroup geometry. -/
theorem concreteLocalGeometryAt_of_prime_field
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (hpo : Odd p) (hp5 : 5 < p)
    (hF : Nat.card F = p) (e : G ≃* PGL2 F) (T : Sylow 2 G) :
    ConcreteLocalGeometryAt T := by
  let : Fact p.Prime := ⟨hp⟩
  let : Finite (PGL2 F) := Finite.of_equiv G e.toEquiv
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, hp, hpo, le_rfl, by simpa using hF⟩
  apply concreteGeometry_of_equiv e.symm ?_ T
  exact concreteGeometry_of_psl_geometry_and_overgroups F hodd (by omega)
    (Inner.concreteLocalGeometryAt_of_prime_field hp hpo hp5 hF (MulEquiv.refl _))
    (fun Q M hM hQM => sylowOvergroupModel_of_prime_card hpo hp5 hF Q M hM hQM)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal
