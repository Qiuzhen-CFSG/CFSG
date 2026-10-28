module
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.UniqueMaximal
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Flags
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Pairs
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
public import Theory.Quasithin.CoprimeRank

/-!
# Nonsolvable Sylow overgroups of cubic rank one in GL₅(2)

Every overgroup of a full Sylow two-subgroup is a stabilizer of a partial
flag in the same basis. Deleting two nonadjacent cuts supplies an actual
S₃ × S₃ quotient, hence three-rank at least two. Thus a flag of three-rank
at most one deletes at most two adjacent cuts. Any proper Sylow overgroup
below it deletes at most one cut and is solvable, since its Sylow index
is at most three. A nonsolvable overgroup therefore cannot be enlarged
while keeping three-rank one. The second theorem lifts this statement
through any specified surjection with two-group kernel.

The source consumer is the literal L₂T ≤ Y in degree five of 12.9.7.
Source: Aschbacher--Smith, refs/quasithin.pdf, printed p.862.
-/

public section
open Subgroup Theory.GroupTheory
namespace BinaryLinear.SylowFlagOvergroups
open OuterCyclic InvariantNodeActions SmallParabolicLevi SmallParabolicLevi.TwoNodes

private instance (d : ℕ) : Finite (LinearGroup d) :=
  Finite.of_injective (fun g : LinearGroup d => (g : Space d → Space d)) DFunLike.coe_injective

private theorem nonadjacent_rank (b : Basis 4) (i j : Fin 4)
    (hij : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    2 ≤ primeRank 3 (cutStabilizer b ({i,j} : Set (Fin 4))ᶜ) := by
  change 2 ≤ primeRank 3 (FiveFlagGeometry.flagStabilizer b ({i,j} : Set (Fin 4))ᶜ)
  let e := (flagDiagonalQuotientEquiv b ({i,j} : Set (Fin 4))ᶜ).trans
    (pairFactorsEquiv i j hij)
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
    (pCore 2 (FiveFlagGeometry.flagStabilizer b ({i,j} : Set (Fin 4))ᶜ)) pCore_isPGroup,
    primeRank_equiv 3 e, primeRank_prod_eq_add]
  have hn : primeRank 3 (Equiv.Perm (Fin 3)) ≠ 0 := by
    intro hz
    have hh := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    rw [Nat.card_perm,Nat.card_fin] at hh
    exact hh (by decide)
  omega

private theorem smaller_cuts (s t : Set (Fin 4)) (hts : t ⊆ s) (hne : s ≠ t)
    (hnear : ∀ i j : Fin 4, i ∉ t → j ∉ t →
      ¬ (i.val + 1 < j.val ∨ j.val + 1 < i.val)) :
    ∃ i : Fin 4, ({i} : Set (Fin 4))ᶜ ⊆ s := by
  classical
  have finite_check : ∀ s t : Finset (Fin 4), t ⊆ s → s ≠ t →
      (∀ i j : Fin 4, i ∉ t → j ∉ t →
        ¬ (i.val + 1 < j.val ∨ j.val + 1 < i.val)) →
      ∃ i : Fin 4, ∀ j : Fin 4, j ≠ i → j ∈ s := by decide +kernel
  obtain ⟨i,hi⟩ := finite_check s.toFinset t.toFinset
    (by simpa using hts) (by simpa using hne) (by simpa using hnear)
  exact ⟨i,fun j hj => Set.mem_toFinset.mp (hi j hj)⟩

/-- A nonsolvable Sylow overgroup cannot be enlarged while retaining cubic rank one. -/
theorem five_eq_of_nonsolvable_and_three_rank
    (S : Sylow 2 (LinearGroup 5)) (P Q : Subgroup (LinearGroup 5))
    (hSP : (S : Subgroup _) ≤ P) (hPQ : P ≤ Q)
    (hP : ¬ Group.IsSolvable P) (hQ : primeRank 3 Q ≤ 1) : P = Q := by
  classical
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer S
  obtain ⟨s,rfl⟩ := overgroup_eq_cutStabilizer S b hb P hSP
  obtain ⟨t,rfl⟩ := overgroup_eq_cutStabilizer S b hb Q (hSP.trans hPQ)
  by_contra hne
  have hst : s ≠ t := fun he => hne (congrArg (cutStabilizer b) he)
  have hnear (i j : Fin 4) (hi : i ∉ t) (hj : j ∉ t) :
      ¬ (i.val + 1 < j.val ∨ j.val + 1 < i.val) := by
    intro h
    have hle : cutStabilizer b ({i,j} : Set (Fin 4))ᶜ ≤ cutStabilizer b t := by
      apply (cutStabilizer_le_iff b _ _).mpr
      intro k hk
      simp only [Set.mem_compl_iff,Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
      exact ⟨fun he => hi (he ▸ hk),fun he => hj (he ▸ hk)⟩
    have hh := (nonadjacent_rank b i j h).trans ((primeRank_mono 3 hle).trans hQ)
    omega
  obtain ⟨i,hi⟩ := smaller_cuts s t ((cutStabilizer_le_iff b _ _).mp hPQ) hst hnear
  have hnode : Group.IsSolvable (minimalParabolic b i) := by
    let : Group.IsNilpotent S := S.isPGroup'.isNilpotent
    apply (S : Subgroup _).isSolvable_of_relIndex_le_four (minimalParabolic b i)
    rw [hb,CubicSylowGeneration.minimalParabolic_index]
    decide
  let : Group.IsSolvable (cutStabilizer b {i}ᶜ) := hnode
  exact hP (Group.isSolvable_of_isSolvable_injective
    (f := inclusion ((cutStabilizer_le_iff b _ _).mpr hi)) (inclusion_injective _))
/-- The same maximality statement through the actual two-group action kernel. -/
theorem five_eq_of_two_kernel_nonsolvable_and_three_rank
    {H : Type*} [Group H] [Finite H]
    (f : H →* LinearGroup 5) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Sylow 2 H) (P Q : Subgroup H) (hSP : (S : Subgroup H) ≤ P) (hPQ : P ≤ Q)
    (hP : ¬ Group.IsSolvable P) (hQ : primeRank 3 Q ≤ 1) : P = Q := by
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  have hPm : ¬ Group.IsSolvable (P.map f) := fun hs =>
    hP ((Group.isSolvable_map_iff_of_solvable_ker f P).mp hs)
  let g := f.subgroupMap Q
  have hg : IsPGroup 2 g.ker := by
    change IsPGroup 2 (f.subgroupMap Q).ker
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  have hr : primeRank 3 (Q.map f) = primeRank 3 Q := by
    symm
    apply primeRank_eq_of_surjective_of_coprime 3 g (f.subgroupMap_surjective Q)
    obtain ⟨k,hk⟩ := hg.exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have he := five_eq_of_nonsolvable_and_three_rank (S.mapSurjective hf)
    (P.map f) (Q.map f) (map_mono hSP) (map_mono hPQ) hPm (hr ▸ hQ)
  have hker := (hk.le_sylow_of_normal S).trans hSP
  exact map_injective_of_ker_le f hker (hker.trans hPQ) he
end BinaryLinear.SylowFlagOvergroups
