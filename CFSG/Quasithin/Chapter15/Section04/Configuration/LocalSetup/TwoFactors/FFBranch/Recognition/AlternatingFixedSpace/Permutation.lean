module

public import Theory.Representation.BinaryPermutation.CubicFixedSpace

/-!
# The permutation-module alternatives in the mixed FF comparison

The same explicit cubic element handles the full permutation module, its
augmentation core, its quotient by constants and its natural section.
Containment of the regular Klein four in a Sylow group, followed by Sylow
conjugacy, gives the assertion for every Sylow two-subgroup.

The final theorem treats the honest extension configuration from B.5.1:
an invariant submodule has a central kernel and the prescribed natural
section, while the quotient of the whole module is trivial. Neither
extension is assumed split. An arbitrary embedding of the alternating
actor allows both A₆ and S₆, and actual automorphism twists, without
identifying different actions by name. Trivial summands are allowed.

Source: Aschbacher–Smith B.3.3, p.84; B.4.2 and B.5.1, pp.86,99;
the B.5.6/F.6.18 comparison in Lemma 15.4.18, p.1163.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.AlternatingFixedSpace
open Representation Representation.BinaryOffender BinaryPermutation
open BinaryPermutation.CubicFixedSpace

variable (n : ℕ) (hn : n = 6 ∨ n = 7)
include hn

theorem alternating_full_enlargement (S : Sylow 2 (alternatingGroup (Fin n))) :
    ∃ d : alternatingGroup (Fin n), d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ((representation (Fin n)).comp (alternatingGroup (Fin n)).subtype)
        (S : Subgroup (alternatingGroup (Fin n))),
        representation (Fin n) d.val v = v :=
  sylow_fixedSpace_enlargement_of_cubic _ _ (klein_isPGroup n hn) _
    (cycle_pow n hn) (cycle_ne_one n hn) (cycle_fixes_full n hn) S

theorem alternating_core_enlargement (S : Sylow 2 (alternatingGroup (Fin n))) :
    ∃ d : alternatingGroup (Fin n), d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ((coreRepresentation (Fin n)).comp (alternatingGroup (Fin n)).subtype)
        (S : Subgroup (alternatingGroup (Fin n))),
        coreRepresentation (Fin n) d.val v = v :=
  sylow_fixedSpace_enlargement_of_cubic _ _ (klein_isPGroup n hn) _
    (cycle_pow n hn) (cycle_ne_one n hn) (cycle_fixes_core n hn) S

theorem alternating_deleted_enlargement (S : Sylow 2 (alternatingGroup (Fin n))) :
    ∃ d : alternatingGroup (Fin n), d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ((deletedRepresentation (Fin n)).comp (alternatingGroup (Fin n)).subtype)
        (S : Subgroup (alternatingGroup (Fin n))),
        deletedRepresentation (Fin n) d.val v = v :=
  sylow_fixedSpace_enlargement_of_cubic _ _ (klein_isPGroup n hn) _
    (cycle_pow n hn) (cycle_ne_one n hn) (cycle_fixes_deleted n hn) S

theorem alternating_natural_enlargement (S : Sylow 2 (alternatingGroup (Fin n))) :
    ∃ d : alternatingGroup (Fin n), d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace (alternatingNaturalRepresentation (Ω := Fin n))
        (S : Subgroup (alternatingGroup (Fin n))),
        naturalRepresentation (Fin n) d.val v = v :=
  sylow_fixedSpace_enlargement_of_cubic _ _ (klein_isPGroup n hn) _
    (cycle_pow n hn) (cycle_ne_one n hn) (cycle_fixes_natural n hn) S

theorem symmetric_full_enlargement (S : Sylow 2 (Equiv.Perm (Fin n))) :
    ∃ d : Equiv.Perm (Fin n), d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace (representation (Fin n)) (S : Subgroup (Equiv.Perm (Fin n))),
        representation (Fin n) d v = v :=
  sylow_fixedSpace_enlargement_of_embedded_cubic _ (alternatingGroup (Fin n)).subtype
    Subtype.val_injective _ (klein_isPGroup n hn) _
    (cycle_pow n hn) (cycle_ne_one n hn) (cycle_fixes_full n hn) S

theorem symmetric_core_enlargement (S : Sylow 2 (Equiv.Perm (Fin n))) :
    ∃ d : Equiv.Perm (Fin n), d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace (coreRepresentation (Fin n)) (S : Subgroup (Equiv.Perm (Fin n))),
        coreRepresentation (Fin n) d v = v :=
  sylow_fixedSpace_enlargement_of_embedded_cubic _ (alternatingGroup (Fin n)).subtype
    Subtype.val_injective _ (klein_isPGroup n hn) _
    (cycle_pow n hn) (cycle_ne_one n hn) (cycle_fixes_core n hn) S

theorem symmetric_deleted_enlargement (S : Sylow 2 (Equiv.Perm (Fin n))) :
    ∃ d : Equiv.Perm (Fin n), d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace (deletedRepresentation (Fin n)) (S : Subgroup (Equiv.Perm (Fin n))),
        deletedRepresentation (Fin n) d v = v :=
  sylow_fixedSpace_enlargement_of_embedded_cubic _ (alternatingGroup (Fin n)).subtype
    Subtype.val_injective _ (klein_isPGroup n hn) _
    (cycle_pow n hn) (cycle_ne_one n hn) (cycle_fixes_deleted n hn) S

theorem symmetric_natural_enlargement (S : Sylow 2 (Equiv.Perm (Fin n))) :
    ∃ d : Equiv.Perm (Fin n), d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace (naturalRepresentation (Fin n)) (S : Subgroup (Equiv.Perm (Fin n))),
        naturalRepresentation (Fin n) d v = v :=
  sylow_fixedSpace_enlargement_of_embedded_cubic _ (alternatingGroup (Fin n)).subtype
    Subtype.val_injective _ (klein_isPGroup n hn) _
    (cycle_pow n hn) (cycle_ne_one n hn) (cycle_fixes_natural n hn) S

/-- The natural-section case of B.5.1, retaining central extensions on both
sides and an arbitrary actual embedding of the alternating actor. -/
theorem permutation_centralSection_enlargement
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
    (f : alternatingGroup (Fin n) →* D) (hf : Function.Injective f)
    (U : Subrepresentation (ρ.comp f))
    (q : U.toSubmodule →ₗ[ZMod 2] natural (Fin n))
    (hq : ∀ g u, q (U.toRepresentation g u) = naturalRepresentation (Fin n) g.val (q u))
    (hker : ∀ g u, q u = 0 → U.toRepresentation g u = u)
    (hquot : ∀ g v, ρ (f g) v - v ∈ U) (S : Sylow 2 D) :
    ∃ d : D, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ d v = v := by
  apply sylow_fixedSpace_enlargement_of_embedded_cubic ρ f hf _
    (klein_isPGroup n hn) _ (cycle_pow n hn) (cycle_ne_one n hn) _ S
  exact cubic_fixedSpace_of_central_section (ρ.comp f)
    (alternatingNaturalRepresentation (Ω := Fin n)) _ _ (cycle_pow n hn)
    (cycle_normalizes n hn) U q hq hker hquot (cycle_fixes_natural n hn)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.AlternatingFixedSpace
