module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.ConjugateFactors
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.Complete
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.GlobalEndpoint
public import Theory.GroupTheory.PCoreActionSplitting
public import Theory.GroupTheory.GeneralizedFitting.Solvable

/-!
# Source classification of the literal ratio factors

Each embedded actor is normal in the decomposed subgroup, so the trivial
two-core descends to it. Pulling the original SQTK cover back along the
composite actor inclusion supplies the genuine cover for D.2.17 and D.2.22.
The cyclic source theorem gives an odd normal subgroup and an involution
supplement; cardinalities make every starred actor Sylow. The noncyclic
source theorem gives the same conclusion, and Sylow conjugacy proves the
converse. The resulting equality discharges the classification premise of
the ambient starred-block permutation on the original action.

Source: Aschbacher--Smith D.2.16--17, D.2.22, printed pp.187--189,
and the first paragraph of 15.1.2, printed p.1084. The Fitting-moved input
is retained on each factor; it is supplied by the preceding seed reduction.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
universe u

private theorem normal_core_bot {D : Type*} [Group D] (p : ℕ)
    (h : pCore p D = ⊥) (A : Subgroup D) [A.Normal] : pCore p A = ⊥ := by
  have hh := pCore_eq_map_of_normal_of_le p A (by rw [h]; exact bot_le)
  change pCore p D = (pCore p A).map A.subtype at hh
  exact (map_eq_bot_iff_of_injective _ A.subtype_injective).mp (hh.symm.trans h)

private theorem cyclic_local_starred_sylow
    {D Y : Type u} [Group D] [Finite D] [AddCommGroup Y] [Module (ZMod 2) Y]
    [FiniteDimensional (ZMod 2) Y] {σ : Representation (ZMod 2) D Y}
    (l : CyclicSource.LocalGeneration σ)
    (hc : ∀ A ∈ QhatStar σ, IsCyclic A) {A : Subgroup D} (hA : A ∈ QhatStar σ) :
    ∃ S : Sylow 2 D, (S : Subgroup D) = A := by
  let : l.kernel.Normal := l.normal
  let : Fact l.prime.Prime := ⟨l.prime_prime⟩
  have hAc : Nat.card A = 2 := by
    rw [hA.1.2.1.card_eq_two_pow_rank,CyclicSource.rank_one_of_cyclic σ hA (hc A hA)]
    norm_num
  have ht : Nat.card (zpowers l.involution) = 2 := by rw [Nat.card_zpowers,l.order_two]
  have hdis : Disjoint l.kernel (zpowers l.involution) := IsPGroup.disjoint_of_coprime
    l.pgroup (IsPGroup.of_card (n := 1) (by simpa using ht)) l.prime_odd.coprime_two_right
  have hcard := card_sup_eq_mul_of_normalizes_of_disjoint l.kernel (zpowers l.involution)
    le_normalizer_of_normal hdis
  rw [l.generated,card_top,ht] at hcard
  have hindex : A.index = Nat.card l.kernel := by
    have hh := A.card_mul_index
    rw [hAc,hcard] at hh
    omega
  have hcop : Nat.Coprime 2 (Nat.card l.kernel) := by
    obtain ⟨n,hn⟩ := l.pgroup.exists_card_eq
    rw [hn]
    exact l.prime_odd.coprime_two_left.pow_right n
  have hnot : ¬ 2 ∣ A.index := by
    rw [hindex]
    exact Nat.prime_two.coprime_iff_not_dvd.mp hcop
  exact ⟨(IsPGroup.of_card (n := 1) (by simpa using hAc)).toSylow hnot,rfl⟩

private theorem starred_iff_sylow_of_all_starred_sylow
    {D Y : Type*} [Group D] [Finite D] [AddCommGroup Y] [Module (ZMod 2) Y]
    [FiniteDimensional (ZMod 2) Y] (σ : Representation (ZMod 2) D Y)
    (hq : cubicRatio σ ≤ 2)
    (hs : ∀ A ∈ QhatStar σ, ∃ S : Sylow 2 D, (S : Subgroup D) = A)
    (A : Subgroup D) : A ∈ QhatStar σ ↔ ∃ S : Sylow 2 D, (S : Subgroup D) = A := by
  constructor
  · exact hs A
  · rintro ⟨T,rfl⟩
    obtain ⟨B,hB⟩ := (QhatStar_nonempty_iff σ).mpr hq
    obtain ⟨S,rfl⟩ := hs B hB
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq D S T
    have he : (S : Subgroup D).map (MulAut.conj g).toMonoidHom = T :=
      congrArg Sylow.toSubgroup hg
    exact he ▸ QhatStar.map_conj σ hB g

namespace FactorData
variable {G V : Type u} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V}
    {K : Subgroup G} {U : Submodule (ZMod 2) V} (c : FactorData ρ K U)
    (d : Decomposition c.representation)

/-- The two-core remains trivial on each embedded normal factor actor. -/
theorem factor_twoCore [K.Normal] (hcore : pCore 2 G = ⊥) (i : d.Index) :
    pCore 2 (d.factor i).Carrier = ⊥ := by
  let F := d.factor i
  have hK : pCore 2 K = ⊥ := normal_core_bot 2 hcore K
  let : F.actor.Normal := d.actor_normal c.representation c.faithful i
  have hA : pCore 2 F.actor = ⊥ := normal_core_bot 2 hK F.actor
  have hh := pCoreIn_range_of_injective 2 F.embedding.groupMap F.embedding.group_injective
  have hz : F.actor.pCoreIn 2 = ⊥ := by
    change (pCore 2 F.actor).map F.actor.subtype = ⊥
    rw [hA,Subgroup.map_bot]
  exact (map_eq_bot_iff_of_injective _ F.embedding.group_injective).mp (hh.symm.trans hz)

/-- The actual ambient cover pulls back along the composite factor inclusion. -/
theorem factor_cover {H : Type*} [Group H] [Finite H] {C : GroupClass}
    (hH : IsSQTK C H) (f : H →* G) (honto : Function.Surjective f) (i : d.Index) :
    ∃ (B : Subgroup H) (q : B →* (d.factor i).Carrier),
      IsSQTK C B ∧ Function.Surjective q := by
  let F := d.factor i
  let j := K.subtype.comp F.embedding.groupMap
  have hi : Function.Injective j := K.subtype_injective.comp F.embedding.group_injective
  let B := j.range.comap f
  let q := (MonoidHom.ofInjective hi).symm.toMonoidHom.comp (f.subgroupComap j.range)
  exact ⟨B,q,hH.subgroup B,(MonoidHom.ofInjective hi).symm.surjective.comp
    (f.subgroupComap_surjective_of_surjective _ honto)⟩

/-- D.2.17 applies to the literal cyclic factor with its pulled-back SQTK cover. -/
theorem factor_cyclic_localGeneration [Group.IsSolvable G] [K.Normal]
    (hcore : pCore 2 G = ⊥) (hq : cubicRatio ρ ≤ 2) (hd : d.FittingFull)
    {H : Type*} [Group H] [Finite H] {C : GroupClass}
    (hH : IsSQTK C H) (f : H →* G) (honto : Function.Surjective f)
    (i : d.Index) (hc : ∀ A ∈ QhatStar (d.factor i).action, IsCyclic A) :
    Nonempty (CyclicSource.LocalGeneration (d.factor i).action) := by
  let F := d.factor i
  let j := K.subtype.comp F.embedding.groupMap
  let : Group.IsSolvable F.Carrier := Group.isSolvable_of_isSolvable_injective
    (f := j) (K.subtype_injective.comp F.embedding.group_injective)
  have hqF : cubicRatio F.action ≤ 2 := by rw [F.embedding.ratio,c.ratio]; exact hq
  obtain ⟨B,q,hB,hontoB⟩ := c.factor_cover d hH f honto i
  exact CyclicSource.source_theorem_D_2_17_cyclic F.faithful hqF F.generated
    F.indecomposable (generalizedFitting_eq_fitting_of_solvable F.Carrier)
    (c.factor_twoCore d hcore i) (hd i) hc hB q hontoB

/-- On every literal indecomposable factor, the original starred family is
exactly its Sylow two-subgroups. The cyclic and noncyclic source branches
both apply with the same action and subgroup embedding. -/
theorem factor_starred_sylow_iff [Group.IsSolvable G] [K.Normal]
    (hcore : pCore 2 G = ⊥) (hq : cubicRatio ρ ≤ 2) (hd : d.FittingFull)
    {H : Type*} [Group H] [Finite H] {C : GroupClass}
    (hH : IsSQTK C H) (f : H →* G) (honto : Function.Surjective f)
    (i : d.Index) (A : Subgroup (d.factor i).Carrier) :
    A ∈ QhatStar (d.factor i).action ↔
      ∃ S : Sylow 2 (d.factor i).Carrier, (S : Subgroup _) = A := by
  classical
  let F := d.factor i
  let j := K.subtype.comp F.embedding.groupMap
  let : Group.IsSolvable F.Carrier := Group.isSolvable_of_isSolvable_injective
    (f := j) (K.subtype_injective.comp F.embedding.group_injective)
  have hqF : cubicRatio F.action ≤ 2 := by rw [F.embedding.ratio,c.ratio]; exact hq
  apply starred_iff_sylow_of_all_starred_sylow F.action hqF _ A
  intro B hB
  by_cases hc : ∀ X ∈ QhatStar F.action, IsCyclic X
  · obtain ⟨l⟩ := c.factor_cyclic_localGeneration d hcore hq hd hH f honto i hc
    exact cyclic_local_starred_sylow l hc hB
  · push Not at hc
    obtain ⟨X,hX,hXnoncyclic⟩ := hc
    have hrX : 1 < rank X := by
      have hp := hX.1.2.1.rank_pos
      by_contra hn
      have hr : rank X = 1 := by omega
      have hcard : Nat.card X = 2 := by rw [hX.1.2.1.card_eq_two_pow_rank,hr]; norm_num
      exact hXnoncyclic (isCyclic_of_prime_card hcard)
    obtain ⟨C,q,hC,hontoC⟩ := c.factor_cover d hH f honto i
    have hrB := (SourceReduction.solvable_source_ratio_and_noncyclic F.action
      hC q hontoC F.faithful hX hrX (c.factor_twoCore d hcore i) (hd i)).2.2 B hB
    exact (SourceReduction.source_lemma_D_2_22 F.action hC q hontoC F.faithful hB hrB
      (generalizedFitting_eq_fitting_of_solvable F.Carrier) (c.factor_twoCore d hcore i)
      (hd i) F.generated).1

/-- The completed D.2 classification discharges the Sylow input of the
ambient starred-block action in original 15.1.2 and 14.6.12. -/
theorem classified_Jhat_partition_action [FiniteDimensional (ZMod 2) V] [Group.IsSolvable G]
    (hcore : pCore 2 G = ⊥) (hq : cubicRatio ρ ≤ 2) (hd : d.FittingFull)
    {H : Type*} [Group H] [Finite H] {C : GroupClass}
    (hH : IsSQTK C H) (f : H →* G) (honto : Function.Surjective f)
    (hK : K = Jhat ρ) :
    ∃ π : G →* Equiv.Perm d.Index,
      (⋃ i, c.ambientBlock d i) = QhatStar ρ ∧ K ≤ π.ker ∧ ∀ g i,
      Subgroup.map (MulAut.conj g).toMonoidHom '' c.ambientBlock d i = c.ambientBlock d (π g i) ∧
      (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor ∧
      (c.ambientFactor d i).space.map (ρ g) = (c.ambientFactor d (π g i)).space := by
  let : K.Normal := by rw [hK]; exact Jhat_normal ρ
  exact c.source_Jhat_partition_action hK d
    (c.factor_starred_sylow_iff d hcore hq hd hH f honto)
end FactorData
end CFSG.Quasithin.ChapterD.RatioDecomposition
