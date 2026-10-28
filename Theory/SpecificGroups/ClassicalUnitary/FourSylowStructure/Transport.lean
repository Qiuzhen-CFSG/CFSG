module

public import Theory.SpecificGroups.ClassicalUnitary.FourSylowStructure.Action
public import Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport

/-!
# Solvable automorphism groups of binary unitary-four Sylow subgroups

The characteristic elementary subgroup identifies restriction of Sylow
automorphisms with a subgroup of the additive norm-plane root normalizer.
The restriction kernel is a two-group and the root normalizer is solvable
when the fixed field has more than two elements.

Conjugacy of Sylow subgroups and change of Hermitian form transport this
conclusion to every Sylow two-subgroup of the actual projective unitary
matrix group. In characteristic two the SU₄ projection is injective, so
this transport preserves the entire Sylow group.

Source: Aschbacher--Smith F.1.11--12, printed pp.262--264, and the
solvable-action step of 4.4.10--11, printed p.621.
-/

open Matrix BenderSuzuki.MatrixGroups Subgroup
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow

public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.FourSylowStructure
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)

/-- The coordinate result transports to every Sylow subgroup of standard SU₄. -/
theorem sylow_mulAut_isSolvable_of_rootNormalizer
    (hnt : ∃ u, σ u ≠ u)
    (hn : Group.IsSolvable (FourSylowNormalizer.rootNormalizer F σ hσ))
    (P : Sylow 2 (SU F (form F σ hσ))) :
    Group.IsSolvable (MulAut P) := by
  let e : localUpper F σ hσ ≃* upper F σ hσ :=
    (localUpper F σ hσ).equivMapOfInjective (localSU F (form F σ hσ)).subtype
      (localSU F (form F σ hσ)).subtype_injective
  let j : localUpper F σ hσ ≃* P := e.trans (Sylow.equiv (sylow F σ hσ) P)
  let : Group.IsSolvable (MulAut (localUpper F σ hσ)) :=
    mulAut_isSolvable_of_rootNormalizer F σ hσ hnt hn
  exact Group.isSolvable_of_surjective (f := (MulAut.congr j).toMonoidHom)
    (MulAut.congr j).surjective

/-- The concrete additive normalizer discharges the full Sylow automorphism
solvability premise whenever the fixed field has order greater than two. -/
theorem sylow_mulAut_isSolvable
    (hnt : ∃ u, σ u ≠ u) (hK : 2 < Nat.card (FixedBy.subfield F σ))
    (P : Sylow 2 (SU F (form F σ hσ))) :
    Group.IsSolvable (MulAut P) :=
  sylow_mulAut_isSolvable_of_rootNormalizer F σ hσ hnt
    (FourSylowNormalizer.rootNormalizer_isSolvable F σ hσ hnt hK) P

omit [CharP F 2] in
/-- Every Sylow two-subgroup of PSU₄(2ⁿ), n greater than one, has solvable
full automorphism group, for the original arbitrary Hermitian form. -/
theorem projective_sylow_mulAut_isSolvable
    (J : HermitianForm 4 F) {n : ℕ} (hn : 1 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Group.IsSolvable (MulAut P) := by
  have hn0 : 0 < n := by omega
  let : CharP F 2 := UnitaryFourFormTransport.charP_two n hn0 hcard
  have hfixed : Nat.card (FixedBy.subfield F J.conj) = 2 ^ n :=
    UnitaryFourFormTransport.fixed_card J n hn0 hcard hconj
  have hnt : ∃ u, J.conj u ≠ u := by
    by_contra! h
    let j : FixedBy.subfield F J.conj ≃ F := Equiv.ofBijective Subtype.val
      ⟨Subtype.val_injective, fun x => ⟨⟨x,h x⟩,rfl⟩⟩
    have he := Nat.card_congr j
    rw [hfixed,hcard] at he
    have hp : 1 < 2 ^ n := one_lt_pow₀ (by decide) hn0.ne'
    nlinarith
  have hK : 2 < Nat.card (FixedBy.subfield F J.conj) := by
    rw [hfixed]
    simpa only [pow_one] using Nat.pow_lt_pow_right (by decide : 1 < 2) hn
  obtain ⟨j⟩ := UnitaryFourFormTransport.nonempty_projectiveEquiv_standardSU
    J n hn0 hcard hconj
  let Q := P.mapSurjective (f := j.toMonoidHom) j.surjective
  let e : P ≃* Q := P.equivMapOfInjective j.toMonoidHom j.injective
  let : Group.IsSolvable (MulAut Q) :=
    sylow_mulAut_isSolvable F J.conj J.conj_involutive hnt hK Q
  exact Group.isSolvable_of_surjective (f := (MulAut.congr e.symm).toMonoidHom)
    (MulAut.congr e.symm).surjective

end Theory.SpecificGroups.ClassicalUnitary.FourSylowStructure
