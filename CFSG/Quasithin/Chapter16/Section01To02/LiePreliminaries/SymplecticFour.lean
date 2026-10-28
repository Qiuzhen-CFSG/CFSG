module

public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import Theory.SpecificGroups.SymplecticFour.Binary.DerivedSylowAction
public import Theory.SpecificGroups.SymplecticFour.InvolutionTypes

/-!
# The derived binary symplectic exception in Chapter 16

An actual isomorphism to Sp₄(2)′ transports a Sylow subgroup and its
pointwise stabilizer. The marked Aut(A₆) Sylow calculation places every
two-power actor in the faithful S₆ action on Sp₄(2)′. Both the equivalence
and its elementwise action are retained; the full Sp₄(2) is not substituted
for its derived subgroup.

This completes the binary alternative of Lemma 16.1.6 for the intrinsic
derived model. The nonbinary involution table, its fixed two-residuals,
and nonbinary Sylow-pointwise innerness are separate remaining obligations.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Notation 16.1.3 and Lemmas 16.1.4, 16.1.6,
printed pp.1171–1172; Suzuki types are defined in E.2.6, printed p.218.
-/

public section

namespace CFSG.Quasithin.Chapter16.LiePreliminaries
open Subgroup Theory.SpecificGroups.SymplecticFour

variable {L F : Type*} [Group L] [Finite L] [Field F] [Finite F]

/-- Source 16.1.6's S₆ alternative on a group actually identified with
Sp₄(2)′. The output is equality with a faithful permutation-induced action. -/
theorem binaryDerived_sylow_fixed_permutation (hF : Nat.card F = 2)
    (e : L ≃* commutator (Sp F)) (P : Sylow 2 L) (r : MulAut L)
    {k : ℕ} (hr : r ^ (2 ^ k) = 1)
    (hfix : ∀ x ∈ (P : Subgroup L), r x = x) :
    ∃ σ : Equiv.Perm (Fin 6),
      MulAut.congr e r = Binary.derivedPermutationAction hF σ := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hpow : (MulAut.congr e r) ^ (2 ^ k) = 1 := by
    rw [← map_pow, hr, map_one]
  have hQ : ∀ x ∈ (Q : Subgroup (commutator (Sp F))), MulAut.congr e r x = x := by
    rintro _ ⟨x, hx, rfl⟩
    change e (r (e.symm (e x))) = e x
    rw [e.symm_apply_apply, hfix x hx]
  obtain ⟨σ, hσ⟩ := Binary.derived_twoPower_fixes_sylow hF Q _ hpow hQ
  exact ⟨σ, hσ.symm⟩

/-- The small exception retains the actual action on every element of A₆,
as needed when comparing centralizers in a chosen Sylow subgroup. -/
theorem binaryDerived_sylow_fixed_action (hF : Nat.card F = 2)
    (e : L ≃* commutator (Sp F)) (P : Sylow 2 L) (r : MulAut L)
    {k : ℕ} (hr : r ^ (2 ^ k) = 1)
    (hfix : ∀ x ∈ (P : Subgroup L), r x = x) :
    ∃ σ : Equiv.Perm (Fin 6), ∀ x : L,
      (Binary.derivedEquivAlternatingSix hF (e (r x)) : Equiv.Perm (Fin 6)) =
        σ * (Binary.derivedEquivAlternatingSix hF (e x) : Equiv.Perm (Fin 6)) * σ⁻¹ := by
  obtain ⟨σ, hσ⟩ := binaryDerived_sylow_fixed_permutation hF e P r hr hfix
  refine ⟨σ, fun x => ?_⟩
  have he : e (r x) = Binary.derivedPermutationAction hF σ (e x) := by
    have h := congrArg (fun a : MulAut (commutator (Sp F)) => a (e x)) hσ
    change e (r (e.symm (e x))) = _ at h
    simpa only [e.symm_apply_apply] using h
  rw [he]
  exact Binary.derivedPermutationAction_apply hF σ (e x)

end CFSG.Quasithin.Chapter16.LiePreliminaries
