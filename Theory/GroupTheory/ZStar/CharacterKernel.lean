module

public import Theory.Character.KernelEquality
public import Theory.Character.Divisibility
public import Theory.Character.SimpleCriteria
public import Theory.Character.ModularBlock.Congruence
public import Theory.GroupTheory.ZStar.LocalReduction

/-!
# The ordinary-character kernel step in the Z-star argument

A nonprincipal irreducible character has a proper representation kernel:
if the kernel were the whole group, its constant character would have
norm one only in dimension one, making it the principal character. Suzuki VI.1.8(ii)
places an involution in that kernel whenever its character value equals
the degree.

Suppose induction centralizes the involution in every proper normal subgroup
containing it. Its conjugates then commute with it inside the kernel.
Their products have square one and, by the odd-commutator hypothesis, odd
order, so they are the identity. Consequently the involution would be
central in the whole group, contradicting the counterexample hypothesis.

This is the kernel reduction in Glauberman step (VI), ported from
`Submission/ZStar/CharacterArgument.lean` at historical commit `c3503435`.
It uses the shared ordinary principal character and the production
involution definition.
-/

public section
noncomputable section
open scoped BigOperators
namespace Glauberman.ZStar.CharacterArgument
open ModularBlock.PrincipalBlockConstruction
universe u v
attribute [local instance] Fintype.ofFinite

/-- An irreducible ordinary character has nonzero degree. -/
theorem irreducibleCharacter_degree_ne_zero
    {G : Type u} [Group G] [Finite G]
    (chi : ConjClassFunction G)
    (hchi : IsIrreducibleConjCharacter chi) :
    chi (ConjClasses.mk (1 : G)) ≠ 0 := by
  rcases hchi.1 with ⟨n, rho, rfl⟩
  have hirr : Representation.IsIrreducible rho :=
    (irreducible_iff_character_norm_one (ρ := rho)).2 hchi.2
  let : Representation.IsIrreducible rho := hirr
  let : Nontrivial (Fin n → ℂ) :=
    irreducible_nontrivial (ρ := rho)
  have hdim_pos : 0 < Module.finrank ℂ (Fin n → ℂ) :=
    (Module.finrank_pos_iff (R := ℂ) (M := Fin n → ℂ)).2 inferInstance
  have hdim_ne : (Module.finrank ℂ (Fin n → ℂ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hdim_pos)
  change rho.character 1 ≠ 0
  simpa [Representation.character] using hdim_ne

/-- The representation affording a nonprincipal irreducible character has
proper kernel.

A constant irreducible character has norm one, hence degree one, and is
the principal character. -/
theorem representationKernel_ne_top_of_irreducibleCharacter_ne_principal
    {G : Type u} [Group G] [Finite G]
    (chi : ConjClassFunction G)
    (hchi : IsIrreducibleConjCharacter chi)
    (hne : chi ≠ ordinaryPrincipalCharacter G)
    {n : ℕ} (rho : Representation ℂ G (Fin n → ℂ))
    (hchar : chi = characterClassFunction rho) :
    rho.ker ≠ ⊤ := by
  intro hker
  have hconst (g : G) : rho.character g = (n : ℂ) := by
    have hg : g ∈ rho.ker := by rw [hker]; trivial
    have heq : rho g = 1 := MonoidHom.mem_ker.mp hg
    simp [Representation.character, heq]
  have hn : (n : ℂ) * (n : ℂ) = 1 := by
    have hnorm := hchi.2
    rw [hchar] at hnorm
    change (Nat.card G : ℂ)⁻¹ *
      ∑ g : G, rho.character g * star (rho.character g) = 1 at hnorm
    simpa [hconst] using hnorm
  have hnNat : n * n = 1 := by exact_mod_cast hn
  have hnOne : n = 1 := by nlinarith [hnNat]
  apply hne
  ext C
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  rw [hchar]
  change rho.character g = 1
  simp [hconst, hnOne]

/-- An element whose square is one and whose order is odd is the identity. -/
theorem eq_one_of_sq_eq_one_of_orderOf_odd
    {G : Type*} [Group G] {x : G}
    (hsq : x * x = 1) (hodd : Odd (orderOf x)) : x = 1 := by
  have hdvd : orderOf x ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    simpa [pow_two] using hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hone | htwo
  · exact orderOf_eq_one_iff.mp hone
  · rw [htwo] at hodd
    exact False.elim ((Nat.not_even_iff_odd.mpr hodd) (by decide))

/-- Kernel step in Glauberman Step (VI).

If `t` is central in a normal subgroup containing it, and all commutators with
`t` have odd order, then `t` is already central in the whole group.  Applied
to the kernel of an irreducible representation, this excludes
`chi(t) = chi(1)` once induction has made `t` central in that kernel. -/
theorem mem_center_of_normal_central_and_odd_commutators
    {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) (hN : N.Normal) (t : G)
    (htI : BenderSuzuki.PFAppendixIII.IsInvolution t) (htN : t ∈ N)
    (htCentralN : ∀ n : G, n ∈ N → n * t = t * n)
    (hodd : ∀ g : G, Odd (orderOf (g * t * g⁻¹ * t⁻¹))) :
    t ∈ Subgroup.center G := by
  have ht_inv : t⁻¹ = t :=
    inv_eq_self_of_sq_eq_one (by simpa [pow_two] using htI.2)
  rw [Subgroup.mem_center_iff]
  intro g
  let u : G := g * t * g⁻¹
  have huN : u ∈ N := by
    exact hN.conj_mem t htN g
  have huI : BenderSuzuki.PFAppendixIII.IsInvolution u := by
    simpa [u, BenderSuzuki.PFAppendixIII.rightConjugateElem, mul_assoc] using
      (BenderSuzuki.PFAppendixIII.isInvolution_rightConjugateElem (g := g⁻¹) htI)
  have hut_comm : u * t = t * u := htCentralN u huN
  have hut_sq : (u * t) * (u * t) = 1 := by
    calc
      (u * t) * (u * t) = (u * u) * (t * t) := by
        rw [mul_assoc, ← mul_assoc t u t, ← hut_comm]
        simp only [mul_assoc]
      _ = 1 := by
        have hu_sq : u * u = 1 := by simpa [pow_two] using huI.2
        have ht_sq : t * t = 1 := by simpa [pow_two] using htI.2
        rw [hu_sq, ht_sq, mul_one]
  have hut_odd : Odd (orderOf (u * t)) := by
    simpa [u, ht_inv, mul_assoc] using hodd g
  have hut_one : u * t = 1 :=
    eq_one_of_sq_eq_one_of_orderOf_odd hut_sq hut_odd
  have hu_eq_t : u = t := by
    calc
      u = (u * t) * t⁻¹ := by simp [mul_assoc]
      _ = t := by rw [hut_one, one_mul, ht_inv]
  calc
    g * t = (g * t * g⁻¹) * g := by group
    _ = u * g := by rfl
    _ = t * g := by rw [hu_eq_t]

/-- The induction/kernel adapter in Glauberman Step (VI).

For a nonprincipal irreducible character, equality `chi(t) = chi(1)` puts
`t` in the proper representation kernel by Suzuki VI.1.8(ii).  If the
induction hypothesis centralizes `t` in every proper normal subgroup, the
odd-commutator calculation then centralizes `t` in all of `G`, contradicting
the chosen counterexample. -/
theorem irreducibleCharacter_value_ne_degree_of_properNormal_centrality
    {G : Type u} [Group G] [Finite G]
    (chi : ConjClassFunction G)
    (hchi : IsIrreducibleConjCharacter chi)
    (hne : chi ≠ ordinaryPrincipalCharacter G)
    (t : G) (htI : BenderSuzuki.PFAppendixIII.IsInvolution t)
    (htNotCentral : t ∉ Subgroup.center G)
    (hodd : ∀ g : G, Odd (orderOf (g * t * g⁻¹ * t⁻¹)))
    (hproperCentral : ∀ (N : Subgroup G), N.Normal → N ≠ ⊤ → t ∈ N →
      ∀ n : G, n ∈ N → n * t = t * n) :
    chi (ConjClasses.mk t) ≠ chi (ConjClasses.mk (1 : G)) := by
  rcases hchi.1 with ⟨n, rho, hchar⟩
  have hirr : Representation.IsIrreducible rho :=
    (irreducible_iff_character_norm_one (ρ := rho)).2 (by
      simpa [hchar] using hchi.2)
  let : Representation.IsIrreducible rho := hirr
  have hker_ne : rho.ker ≠ ⊤ :=
    representationKernel_ne_top_of_irreducibleCharacter_ne_principal
      chi hchi hne rho hchar
  intro hvalue
  have hrho_value : rho.character t = rho.character 1 := by
    rw [hchar] at hvalue
    change rho.character t = rho.character 1 at hvalue
    exact hvalue
  have htker : t ∈ rho.ker :=
    (BenderSuzuki.External.Suzuki.VI.suzuki_ch6_theorem_1_8_ii rho t).1
      hrho_value
  have hker_normal : rho.ker.Normal := inferInstance
  have htCentralKer : ∀ n : G, n ∈ rho.ker → n * t = t * n :=
    hproperCentral rho.ker hker_normal hker_ne htker
  exact htNotCentral (mem_center_of_normal_central_and_odd_commutators
    rho.ker hker_normal t htI htker htCentralKer hodd)

end Glauberman.ZStar.CharacterArgument

