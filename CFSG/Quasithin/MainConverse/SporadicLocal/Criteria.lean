module

public import CFSG.Quasithin.MainConverse.Transport
public import Theory.GroupTheory.PrimeRankNonabelianCube

/-!
# Local reductions for the six remaining sporadic converse cases

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Theorem
0.1.2(5), printed p.4, repeated on p.482. The intended carriers are exactly
those of `ClassificationModels.SporadicName`: J₂ and HS use the ATLAS
permutation groups, J₃ and Ru their permutation models, J₄ its matrix model,
and He its permutation model.

The rank reduction uses nonabelian odd Sylow subgroups of prime-cube order
where the cube-free order bound alone is insufficient. A separate exhaustive
local-cover reduction handles J₃, whose ordinary three-rank is three.
For E, only maximal 2-locals containing a fixed Sylow subgroup are covered;
normality and centralization are intrinsic to each actual local group.

These are conditional reductions. They do not assert the six model cases:
the concrete Sylow calculations and exhaustive local covers must still be
constructed. Proper-section and full-catalogue assertions are separate.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal

open Subgroup

/-- Small odd Sylow groups imply the global odd-rank bound. All Sylow
orders and noncommutativity witnesses remain explicit model obligations. -/
public theorem stronglyQuasithin_of_odd_sylow_cases
    {G : Type*} [Group G] [Finite G]
    (h : ∀ p : ℕ, p.Prime → Odd p →
      (¬ p ^ 3 ∣ Nat.card G) ∨
        ∃ P : Sylow p G, Nat.card P = p ^ 3 ∧ ¬ IsMulCommutative P) :
    IsStronglyQuasithin G := by
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  rcases h p hp ho with hc | ⟨P, hc, hna⟩
  · exact primeRank_le_two_of_cube_not_dvd hc
  · exact primeRank_le_two_of_nonabelian_sylow_cube P hc hna

/-- Conjugates of groups with odd-cube-free orders bound every maximal
2-local, provided their coverage has actually been proved. -/
public theorem quasithin_of_maximal_local_cube_free_cover
    {G : Type*} [Group G] [Finite G] {ι : Type*} (L : ι → Subgroup G)
    (hcover : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      ∃ (i : ι) (g : G), M ≤ (L i).map (MulAut.conj g).toMonoidHom)
    (hcard : ∀ (i : ι) (p : ℕ), p.Prime → Odd p → ¬ p ^ 3 ∣ Nat.card (L i)) :
    IsQuasithin G := by
  apply Theory.GroupTheory.isQuasithin_iff_maximalTwoLocal.mpr
  intro M hM p hp ho
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨i, g, hle⟩ := hcover M hM
  have hr := primeRank_le_two_of_cube_not_dvd (hcard i p hp ho)
  have he := Theory.GroupTheory.primeRank_equiv p
    (Subgroup.equivMapOfInjective (L i) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)
  exact (Theory.GroupTheory.primeRank_le_of_injective p
    (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)).trans (he ▸ hr)

/-- Actual normal self-centralizing two-subgroups in an exhaustive family
of Sylow-containing local groups establish condition E. -/
public theorem evenCharacteristic_of_local_normal_cover
    {G : Type*} [Group G] [Finite G] {ι : Type*} (T : Sylow 2 G)
    (L : ι → Subgroup G) (Q : ∀ i, Subgroup (L i))
    (hn : ∀ i, (Q i).Normal) (hp : ∀ i, IsPGroup 2 (Q i))
    (hc : ∀ i, centralizer (Q i : Set (L i)) ≤ Q i)
    (hcover : ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      ∃ i, Nonempty (M ≃* L i)) :
    IsEvenCharacteristic G := by
  apply IsEvenCharacteristicAt.all (T := T)
  intro M hM hTM
  obtain ⟨i, ⟨e⟩⟩ := hcover M hM hTM
  have hQ : Q i ≤ pCore 2 (L i) := le_sSup ⟨hn i, hp i⟩
  have hL : HasCharacteristicTwo (L i) := by
    intro x hx
    exact hQ (hc i ((centralizer_le hQ) hx))
  exact hL.of_equiv e.symm

end CFSG.Quasithin.MainConverse.SporadicLocal
