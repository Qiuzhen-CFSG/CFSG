module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover
public import Theory.SpecificGroups.SymplecticFour.CentralRootLifts
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.SimpleQuotients
public import Theory.GroupTheory.CoveringKernelBound
public import Theory.GroupTheory.CoveringKernelEquiv

/-!
# Symplectic inputs to I.1.3–I.1.4

The universal kernels of Sp₄(F) and PSp₄(F) in characteristic two, |F| > 3,
and of PSL₅(2) are multiplicatively isomorphic to PUnit. The universal kernels
of PSp₄(p), p odd prime, and Sp₆(2) are multiplicatively isomorphic to C₂.
These are the literal matrix groups and their central quotients.

The even symplectic result combines the proved two-primary root-section
calculation with the independent odd-primary transfer calculations. The other
families use their proved matrix presentations and central-extension
calculations. The identity covers, odd symplectic central quotient cover,
and binary six-space free-central cover are explicitly certified universal.
The earlier conditional assembly and root-lifting interfaces are preserved.

Source: Aschbacher–Smith, A.2.2–A.2.4, printed p.33 (PDF p.44), and
I.1.3–I.1.4, printed pp.407–408 (PDF pp.418–419). The printed I.1.4 list
requires qualification: A.2.2 includes Sp₆(2), whose multiplier is C₂,
and PSp₄(p) for odd primes; PSp₄(3) is covered by its U₄(2) alias but
the ordinary odd-prime symplectic family also has a nontrivial multiplier.
The ATLAS S62, S44 and S45 pages respectively give multipliers 2, 1 and 2:
https://brauer.maths.qmul.ac.uk/Atlas/v3/clas/S62/
https://brauer.maths.qmul.ac.uk/Atlas/v3/clas/S44/
https://brauer.maths.qmul.ac.uk/Atlas/v3/clas/S45/
These source observations are not used as Lean proof inputs. The exceptional
Sp₄(2)' endpoint belongs to the A₆ branch, not to the full Sp₄(2) group.

All four family calculations below have their central-extension premises
discharged. They supply the symplectic and PSL₅(2) rows to the independent
full-table assembly; they do not assert the printed table's exhaustiveness.
-/

namespace CFSG.Quasithin.ChapterI.LieMultipliers.Symplectic

open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open PerfectCentralCovering

universe u w
variable (F : Type u) [Field F] [Finite F] [CharP F 2]

/-- The matrix model supplies the perfectness and simple central quotient
needed by the quasisimple covering API. -/
public theorem even_isQuasisimple (hF : 3 < Nat.card F) : IsQuasisimple (Sp F) where
  toIsPerfect := CentralRootLifts.perfect (by omega)
  simple := SimpleQuotients.isSimpleGroup hF

/-- Actual additive root sections generating the constructed universal cover.
This applies the local lifting result to the precise projection used by the
component-cover consumers. It leaves relations between different roots open. -/
public theorem even_universal_root_lifts (hF : 4 < Nat.card F) :
    ∃ x : Fin 8 → Multiplicative F →* UniversalGroup (Sp F),
      (∀ r, (universalProjection (Sp F)).comp (x r) = RootSubgroup.parameter r) ∧
      Subgroup.closure
        (Set.range (fun p : Fin 8 × Multiplicative F => x p.1 p.2)) = ⊤ := by
  let : Group.IsPerfect (Sp F) := CentralRootLifts.perfect (by omega)
  exact CentralRootLifts.exists_generating_root_lifts hF (universalCover (Sp F))

omit [Finite F] [CharP F 2] in
/-- Assembly of the exact kernel equality needed by component-cover rigidity.
Both primary exclusions remain explicit independent proof obligations. -/
public theorem even_universalProjection_ker_eq_bot_of_prime_exclusions
    (h₂ : ¬ 2 ∣ Nat.card (universalProjection (Sp F)).ker)
    (hodd : ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (universalProjection (Sp F)).ker) :
    (universalProjection (Sp F)).ker = ⊥ := by
  apply Subgroup.card_eq_one.mp
  by_contra h
  obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd h
  by_cases hp2 : p = 2
  · exact h₂ (hp2 ▸ hdiv)
  · exact hodd p hp hp2 hdiv

/-- Conditional identity-cover calculation, including its kernel as a group.
This becomes the even symplectic multiplier theorem only after both prime
exclusions have been proved, including at field order four. -/
public theorem even_universalCover_of_prime_exclusions (hF : 3 < Nat.card F)
    (h₂ : ¬ 2 ∣ Nat.card (universalProjection (Sp F)).ker)
    (hodd : ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (universalProjection (Sp F)).ker) :
    letI : IsQuasisimple (Sp F) := even_isQuasisimple F hF
    Covering.IsUniversal.{u, u, w} (Covering.id : Covering (Sp F) (Sp F)) ∧
      Nonempty ((universalProjection (Sp F)).ker ≃* PUnit) := by
  let : IsQuasisimple (Sp F) := even_isQuasisimple F hF
  have hk := even_universalProjection_ker_eq_bot_of_prime_exclusions F h₂ hodd
  have hcard := Subgroup.card_eq_one.mpr hk
  refine ⟨Covering.isUniversal_of_kernel_card_le _ ?_, ?_⟩
  · rw [hcard]
    exact Nat.card_pos
  · let : Subsingleton (universalProjection (Sp F)).ker := by
      rw [hk]
      infer_instance
    let : Unique (universalProjection (Sp F)).ker := uniqueOfSubsingleton 1
    exact ⟨MulEquiv.ofUnique⟩

end CFSG.Quasithin.ChapterI.LieMultipliers.Symplectic

public section
noncomputable section

namespace CFSG.Quasithin.ChapterI.LieMultipliers.Symplectic

open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open PerfectCentralCovering

universe u w

section Even
variable (F : Type u) [Field F] [Finite F] [CharP F 2]

/-- The unconditional multiplier input to the component-model step in 13.6.6. -/
theorem even_universalProjection_ker_eq_bot (hF : 3 < Nat.card F) :
    (universalProjection (Sp F)).ker = ⊥ :=
  CentralCovers.Even.universalProjection_ker_eq_bot hF

omit [CharP F 2] in
/-- The exact field-degree convention used by the source component consumers. -/
theorem even_universalProjection_ker_eq_bot_of_card_pow
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    (universalProjection (Sp F)).ker = ⊥ :=
  CentralCovers.Even.universalProjection_ker_eq_bot_of_card_pow hF hn

/-- The actual Sp₄ multiplier equivalence, including F₄. -/
def evenUniversalKernelEquivPUnit (hF : 3 < Nat.card F) :
    (universalProjection (Sp F)).ker ≃* PUnit :=
  CentralCovers.Even.universalKernelEquivPUnit hF

/-- The identity cover and its canonical multiplier, without extra prime exclusions. -/
theorem even_universalCover (hF : 3 < Nat.card F) :
    letI : IsQuasisimple (Sp F) := even_isQuasisimple F hF
    Covering.IsUniversal.{u, u, w} (Covering.id : Covering (Sp F) (Sp F)) ∧
      Nonempty ((universalProjection (Sp F)).ker ≃* PUnit) := by
  let : IsQuasisimple (Sp F) := even_isQuasisimple F hF
  exact ⟨CentralCovers.Even.identity_isUniversal hF,
    ⟨evenUniversalKernelEquivPUnit F hF⟩⟩

/-- Transport through the actual central quotient Sp₄(F) ≃ PSp₄(F). -/
def evenProjectiveUniversalKernelEquivPUnit (hF : 3 < Nat.card F) :
    (universalProjection (ClassicalGroup.PSp 2 F)).ker ≃* PUnit := by
  let : Fact (2 < Nat.card F) := ⟨by omega⟩
  let e := (universalQuasisimpleCover_isUniversal (ClassicalGroup.PSp 2 F)).kerMulEquiv
    (universalQuasisimpleCover_isUniversal (Sp F)) EvenProjective.equiv.symm
  exact e.trans (evenUniversalKernelEquivPUnit F hF)

/-- The literal Sp₄ → PSp₄ quotient is universal, with both its own kernel
and the canonical universal kernel explicitly trivial. -/
theorem even_projective_universalCover (hF : 3 < Nat.card F) :
    letI : Fact (2 < Nat.card F) := ⟨by omega⟩
    Covering.IsUniversal.{u, u, w} (CentralCovers.OddPrime.quotientCover F) ∧
      Nonempty ((CentralCovers.OddPrime.quotientCover F).toMonoidHom.ker ≃* PUnit) ∧
      Nonempty ((universalProjection (ClassicalGroup.PSp 2 F)).ker ≃* PUnit) := by
  let : Fact (2 < Nat.card F) := ⟨by omega⟩
  refine ⟨?_, ?_, ⟨evenProjectiveUniversalKernelEquivPUnit F hF⟩⟩
  · apply Covering.isUniversal_of_kernel_card_le
    rw [Nat.card_congr (evenProjectiveUniversalKernelEquivPUnit.{u, 0} F hF).toEquiv]
    calc
      Nat.card (PUnit : Type) = 1 := by simp
      _ ≤ Nat.card (CentralCovers.OddPrime.quotientCover F).toMonoidHom.ker := Nat.card_pos
  · have hk : (CentralCovers.OddPrime.quotientCover F).toMonoidHom.ker = ⊥ := by
      rw [CentralCovers.OddPrime.quotientCover_ker, EvenProjective.center_eq_bot]
    let : Subsingleton (CentralCovers.OddPrime.quotientCover F).toMonoidHom.ker := by
      rw [hk]
      infer_instance
    let : Unique (CentralCovers.OddPrime.quotientCover F).toMonoidHom.ker :=
      uniqueOfSubsingleton 1
    exact ⟨MulEquiv.ofUnique⟩
end Even

section LinearFive
variable (F : Type u) [Field F] [Finite F]

/-- The PSL₅(2) row over every finite field of cardinality two. -/
def psl5TwoUniversalKernelEquivPUnit (hF : Nat.card F = 2) :
    (universalProjection (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F)).ker ≃* PUnit :=
  Theory.SpecificGroups.PSL5Two.UniversalCover.fieldUniversalKernelEquivPUnit F hF

/-- The actual identity cover of PSL₅(2) is universal. Field transport is
entrywise on matrices and descends through the scalar center. -/
theorem psl5_two_universalCover (hF : Nat.card F = 2) :
    letI := Theory.SpecificGroups.PSL5Two.UniversalCover.isQuasisimple F
    Covering.IsUniversal.{u, u, w} (Covering.id :
      Covering (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F)
        (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F)) ∧
      Nonempty ((universalProjection
        (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F)).ker ≃* PUnit) := by
  let := Theory.SpecificGroups.PSL5Two.UniversalCover.isQuasisimple F
  exact ⟨Theory.SpecificGroups.PSL5Two.UniversalCover.field_identity_isUniversal F hF,
    ⟨psl5TwoUniversalKernelEquivPUnit F hF⟩⟩
end LinearFive

section OddPrime
variable (F : Type u) [Field F] [Finite F] {p : ℕ} [Fact p.Prime]

/-- The ordinary odd-prime symplectic multiplier, including p = 3. No extra
central-closure or U₄(2) model-comparison hypothesis remains. -/
def oddPrimeUniversalKernelEquivC2 (hp2 : p ≠ 2) (hF : Nat.card F = p) :
    (universalProjection (ClassicalGroup.PSp 2 F)).ker ≃* Multiplicative (ZMod 2) := by
  let : Fact (2 < Nat.card F) :=
    ⟨CentralCovers.OddPrime.card_gt_two (Fact.out : p.Prime) hp2 hF⟩
  exact CentralCovers.OddPrime.primeUniversalKernelEquivC2 hp2 hF

/-- The explicit universal double cover is the literal quotient of Sp₄(F)
by its center, not a group-family label or a group-order recognition. -/
theorem odd_prime_universalCover (hp2 : p ≠ 2) (hF : Nat.card F = p) :
    letI : Fact (2 < Nat.card F) :=
      ⟨CentralCovers.OddPrime.card_gt_two (Fact.out : p.Prime) hp2 hF⟩
    Covering.IsUniversal.{u, u, w} (CentralCovers.OddPrime.quotientCover F) ∧
      Nonempty ((CentralCovers.OddPrime.quotientCover F).toMonoidHom.ker ≃*
        Multiplicative (ZMod 2)) ∧
      Nonempty ((universalProjection (ClassicalGroup.PSp 2 F)).ker ≃*
        Multiplicative (ZMod 2)) :=
  CentralCovers.OddPrime.universal_double_cover hp2 hF

/-- The odd-prime symplectic family cannot be classified as having trivial
multiplier on the basis of its omitted I.1.4 table row. -/
theorem odd_prime_universalProjection_ker_ne_bot (hp2 : p ≠ 2) (hF : Nat.card F = p) :
    (universalProjection (ClassicalGroup.PSp 2 F)).ker ≠ ⊥ := by
  intro hk
  have hc := Nat.card_congr (oddPrimeUniversalKernelEquivC2 F hp2 hF).toEquiv
  rw [hk, Subgroup.card_bot] at hc
  norm_num at hc
end OddPrime

/-- The omitted Sp₆(2) row has multiplier C₂. The carrier is the literal
six-dimensional binary symplectic matrix group. -/
def sp6TwoUniversalKernelEquivC2 :
    (universalProjection (Matrix.symplecticGroup (Fin 3) (ZMod 2))).ker ≃*
      Multiplicative (ZMod 2) :=
  Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.kernelEquiv

/-- The free-central construction is a finite quasisimple universal double
cover; its upper bound and concrete Co₃ lower bound have both been proved. -/
theorem sp6_two_universalCover :
    Covering.IsUniversal.{0, 0, w}
      Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.cover ∧
      Nonempty ((universalProjection (Matrix.symplecticGroup (Fin 3) (ZMod 2))).ker ≃*
        Multiplicative (ZMod 2)) :=
  Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.universalDoubleCover

/-- In particular, the omission of Sp₆(2) in I.1.4 cannot imply triviality. -/
theorem sp6_two_universalProjection_ker_ne_bot :
    (universalProjection (Matrix.symplecticGroup (Fin 3) (ZMod 2))).ker ≠ ⊥ := by
  intro hk
  have hc := Nat.card_congr sp6TwoUniversalKernelEquivC2.toEquiv
  rw [hk, Subgroup.card_bot] at hc
  norm_num at hc

end CFSG.Quasithin.ChapterI.LieMultipliers.Symplectic
