module

public import Theory.GroupTheory.PResidual.PrimeTo
public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.Sylow

/-!
# Finite-group transfers for parabolic realization

Every p-subgroup lies in the prime-to-p residual. Thus a Sylow subgroup
restricts to that residual without losing any elements. A Levi projection
with p-group kernel and p-reduced target identifies its kernel with the
p-core, including the embedding into the original ambient group.

These are the finite-group steps used in GLS3, Theorems 2.3.4 and 2.6.5.
They do not assume that an arbitrary finite group is of Lie type.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem le_primeToResidual_of_isPGroup {U : Subgroup G}
    (hU : IsPGroup p U) : U ≤ primeToResidual p G := by
  intro x hx
  obtain ⟨n, hn⟩ := hU ⟨x, hx⟩
  apply mem_primeToResidual_of_pow (n := n)
  exact congrArg Subtype.val hn

/-- A Sylow subgroup retains all its elements in the prime-to-p residual. -/
@[expose] def sylowInPrimeToResidual (S : Sylow p G) :
    Sylow p (primeToResidual p G) :=
  S.subtype (le_primeToResidual_of_isPGroup S.isPGroup')

theorem map_sylowInPrimeToResidual (S : Sylow p G) :
    (sylowInPrimeToResidual S : Subgroup (primeToResidual p G)).map
      (primeToResidual p G).subtype = (S : Subgroup G) :=
  map_subgroupOf_eq_of_le (le_primeToResidual_of_isPGroup S.isPGroup')

/-- Use an actual Levi projection, with relative kernel, to identify the
radical with the embedded p-core. Ambient normality of `U` is not required. -/
theorem embedded_pCore_eq_of_leviProjection
    [Finite G] [Fact p.Prime] {L : Type*} [Group L] [Finite L]
    (P U : Subgroup G) (hUP : U ≤ P)
    (f : P →* L) (hf : Function.Surjective f)
    (hker : f.ker = U.subgroupOf P) (hU : IsPGroup p U)
    (hL : pCore p L = ⊥) : (pCore p P).map P.subtype = U := by
  have hkerP : IsPGroup p f.ker := by
    rw [hker]
    exact hU.of_equiv (subgroupOfEquivOfLe hUP).symm
  have heq := f.comap_pCore_of_ker_isPGroup hf hkerP
  rw [hL, MonoidHom.comap_bot, hker] at heq
  rw [← heq, map_subgroupOf_eq_of_le hUP]

/-- Every overgroup of a conjugate of a subgroup containing a Sylow also
contains an ambient Sylow. The Lie-type input is the Sylow in the Borel. -/
theorem contains_sylow_of_conjugate_le
    [Finite G] [Fact p.Prime] {B P : Subgroup G}
    (S : Sylow p G) (hSB : (S : Subgroup G) ≤ B)
    (g : G) (hg : B.map (MulAut.conj g).toMonoidHom ≤ P) :
    ∃ R : Sylow p G, (R : Subgroup G) ≤ P := by
  exact ⟨S.mapSurjective (MulAut.conj g).surjective, (map_mono hSB).trans hg⟩

end Subgroup

end
