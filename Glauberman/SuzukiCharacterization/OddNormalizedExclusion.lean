module

public import Glauberman.SuzukiCharacterization.Hypotheses
public import Glauberman.SuzukiCharacterization.NormalStructure
public import Glauberman.SuzukiCharacterization.PrincipalCosetValues
public import Glauberman.SuzukiCharacterization.ZeroFixedCharacter
public import Theory.Character.CosetKernel
public import Theory.Character.ModularBlock.Congruence
public import Theory.Representation.SubrepresentationLattice

/-!
# Exclusion of odd subgroups normalized by the Sylow two-subgroup

This is the final reduction in Glauberman, *A Characterization of the Suzuki
Groups* (1968), Theorem 4.1(i), p. 90. A principal-block character with no
P-fixed vectors has a kernel not containing P. The normal-subgroup dichotomy
and the trivial odd core make that kernel trivial. Constancy of its values
on nonidentity P-cosets of H then puts H in the kernel by Lemma 3.1.

The conditional kernel argument retains the normal-subgroup dichotomy,
existence of the character, and coset-value identity as explicit inputs.
The unconditional theorem discharges them using `NormalStructure`,
`ZeroFixedCharacter`, and `PrincipalCosetValues`, respectively: Proposition 2.1,
the column argument through (4.7), and Lemma 3.8 with (4.8).
The source is stored at
`refs/original/n-group-global/odd-core-rank-two-source/glauberman-suzuki-1968-euclid-wayback.pdf`.
-/

open scoped BigOperators
open ModularBlock.PrincipalBlockConstruction
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace Glauberman.SuzukiCharacterization

/-- The final kernel argument, with the three preceding source results explicit. -/
public theorem Hypotheses.odd_normalized_eq_bot_of_principal_block_data {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (h : Hypotheses P)
    (d : PrincipalCongruenceBlockData G)
    (hnormal : ∀ N : Subgroup G, N.Normal →
      Nat.Coprime 2 (Nat.card N) ∨ (P : Subgroup G) ≤ N)
    (hselect : ∃ i ∈ d.block, ∑ x : P, d.chi i (ConjClasses.mk (x : G)) = 0)
    (hcoset : ∀ i ∈ d.block, ∀ H : Subgroup G,
      Nat.Coprime 2 (Nat.card H) → (P : Subgroup G) ≤ Subgroup.normalizer (H : Set G) →
      ∀ x : P, x ≠ 1 → ∀ y : H,
        d.chi i (ConjClasses.mk ((x : G) * y)) = d.chi i (ConjClasses.mk (x : G)))
    (H : Subgroup G) (hodd : Nat.Coprime 2 (Nat.card H))
    (hnorm : (P : Subgroup G) ≤ Subgroup.normalizer (H : Set G)) : H = ⊥ := by
  obtain ⟨i, hi, hsum⟩ := hselect
  obtain ⟨n, ρ, hρ⟩ := (d.complete.1 i).1
  have hval (g : G) : d.chi i (ConjClasses.mk g) = ρ.character g := by
    rw [hρ]
    exact congrFun (ofConjClassFunction_characterClassFunction ρ) g
  let : Representation.IsIrreducible ρ :=
    (irreducible_iff_character_norm_one (ρ := ρ)).2 (by
      rw [← hρ]
      exact (d.complete.1 i).2)
  let : Nontrivial (Fin n → ℂ) := Subrepresentation.irreducible_module_nontrivial ρ
  have hfix : Representation.invariants (ρ.comp (P : Subgroup G).subtype) = ⊥ := by
    apply Representation.invariants_eq_bot_of_sum_character_eq_zero
    simpa only [hval] using hsum
  have hPnot : ¬ (P : Subgroup G) ≤ ρ.ker := by
    intro hP
    have htop : Representation.invariants (ρ.comp (P : Subgroup G).subtype) = ⊤ := by
      apply top_unique
      intro v _ x
      change ρ (x : G) v = v
      rw [MonoidHom.mem_ker.mp (hP x.property)]
      rfl
    exact bot_ne_top (hfix.symm.trans htop)
  have hkerodd := (hnormal ρ.ker (MonoidHom.normal_ker ρ)).resolve_right hPnot
  have hker : ρ.ker = ⊥ := by
    apply eq_bot_iff.mpr
    rw [← h.oddCore_eq_bot]
    exact le_sSup ⟨MonoidHom.normal_ker ρ, hkerodd⟩
  apply eq_bot_iff.mpr
  rw [← hker]
  apply Representation.le_ker_of_invariants_eq_bot_of_character_mul ρ
    (P : Subgroup G) H hfix
  intro x hx y
  have hv := hcoset i hi H hodd hnorm x hx y
  simpa only [hval] using hv

/-- Glauberman's Theorem 4.1(i): under the Suzuki characterization hypotheses,
every odd-order subgroup normalized by the Sylow two-subgroup is trivial. -/
public theorem Hypotheses.odd_normalized_eq_bot {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (h : Hypotheses P)
    (H : Subgroup G) (hodd : Nat.Coprime 2 (Nat.card H))
    (hnorm : (P : Subgroup G) ≤ Subgroup.normalizer (H : Set G)) : H = ⊥ := by
  obtain ⟨d⟩ := exists_principalCongruenceBlockData G
  exact h.odd_normalized_eq_bot_of_principal_block_data P d
    (h.normal_dichotomy P) (h.exists_principalBlock_zero_sylow_sum P d)
    (fun _ hi => h.principal_coset_values P d hi) H hodd hnorm

end Glauberman.SuzukiCharacterization
