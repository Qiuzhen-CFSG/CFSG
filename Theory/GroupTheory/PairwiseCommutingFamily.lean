module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Order.Preorder.Finite

/-!
# Pairwise commuting families in nilpotent groups

Here commuting is required only for distinct members of a family of subgroups;
the members themselves need not be abelian. Each member is normal in the join
of such a family, since it normalizes itself and the other members centralize it.

For a conjugation-invariant family `Δ` inside a finite nilpotent subgroup `S`,
assume that distinct members commute whenever one normalizes the other, and
that a member permuting a pairwise commuting subfamily centralizes its distinct
members. Choose a maximal pairwise commuting subfamily `Γ` with join `W`.
The two assumptions identify `Γ` with the `Δ`-members in `W` and in `N_S(W)`.
Thus `N_S(W)` is self-normalizing in `S`, so the nilpotent normalizer condition
gives `N_S(W) = S` and `Γ = Δ`.

This isolates the maximal-family argument in Aschbacher--Smith,
*The Classification of Quasithin Groups*, I.7.5, printed p.426
(`refs/quasithin.pdf`, PDF p.437). The source's tightly embedded subgroup and
Frattini arguments supply the two explicit local assumptions; they are not
part of this generic result. Conjugation is `x ↦ s * x * s⁻¹`, and all uses of
the nilpotent normalizer condition take place inside `S`.
-/

namespace Subgroup
variable {G : Type*} [Group G]

namespace PairwiseCommutingFamily

/-- A finite group admits a maximal subfamily whose distinct members commute. -/
public theorem exists_maximal [Finite G] (Δ : Set (Subgroup G)) :
    ∃ Γ, Maximal (fun Γ => Γ ⊆ Δ ∧
      Γ.Pairwise (fun A B => A ≤ centralizer (B : Set G))) Γ := by
  apply Set.Finite.exists_maximal (Set.toFinite _)
  exact ⟨∅, Set.empty_subset Δ, by intro A hA; exact False.elim hA⟩

/-- Maximality absorbs a member centralizing every distinct chosen member.
No self-centralization hypothesis is needed. -/
public theorem mem_of_centralizes {Δ Γ : Set (Subgroup G)}
    (hmax : Maximal (fun Γ => Γ ⊆ Δ ∧
      Γ.Pairwise (fun A B => A ≤ centralizer (B : Set G))) Γ)
    {T : Subgroup G} (hT : T ∈ Δ)
    (hcomm : ∀ A ∈ Γ, T ≠ A → T ≤ centralizer (A : Set G)) : T ∈ Γ := by
  have hi : insert T Γ ⊆ Δ ∧
      (insert T Γ).Pairwise (fun A B => A ≤ centralizer (B : Set G)) := by
    refine ⟨Set.insert_subset hT hmax.1.1, ?_⟩
    intro A hA B hB hne
    rcases hA with rfl | hA <;> rcases hB with rfl | hB
    · exact (hne rfl).elim
    · exact hcomm B hB hne
    · exact le_centralizer_iff.mp (hcomm A hA hne.symm)
    · exact hmax.1.2 hA hB hne
  exact hmax.2 hi (Set.subset_insert T Γ) (Set.mem_insert T Γ)

/-- Each member of a pairwise commuting family is normalized by the join. -/
public theorem join_le_normalizer {Γ : Set (Subgroup G)}
    (hΓ : Γ.Pairwise (fun A B => A ≤ centralizer (B : Set G)))
    {A : Subgroup G} (hA : A ∈ Γ) : sSup Γ ≤ normalizer (A : Set G) := by
  apply sSup_le
  intro B hB
  by_cases hBA : B = A
  · subst B; exact A.le_normalizer
  · exact (hΓ hB hA hBA).trans (centralizer_le_normalizer _)

/-- When normalization forces distinct members to commute, the original
members contained in the join are exactly the maximal subfamily. -/
public theorem mem_iff_le_join {Δ Γ : Set (Subgroup G)}
    (hnorm : ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B →
      B ≤ normalizer (A : Set G) → A ≤ centralizer (B : Set G))
    (hmax : Maximal (fun Γ => Γ ⊆ Δ ∧
      Γ.Pairwise (fun A B => A ≤ centralizer (B : Set G))) Γ)
    {T : Subgroup G} (hT : T ∈ Δ) : T ∈ Γ ↔ T ≤ sSup Γ := by
  refine ⟨le_sSup, fun hTW => ?_⟩
  apply mem_of_centralizes hmax hT
  intro A hA hne
  exact le_centralizer_iff.mp (hnorm A (hmax.1.1 hA) T hT hne.symm
    (hTW.trans (join_le_normalizer hmax.1.2 hA)))

/-- An element of `S` normalizing the join preserves the maximal subfamily. -/
public theorem conj_mem {Δ Γ : Set (Subgroup G)} {S : Subgroup G}
    (hconj : ∀ A ∈ Δ, ∀ s ∈ S, A.map (MulAut.conj s).toMonoidHom ∈ Δ)
    (hnorm : ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B →
      B ≤ normalizer (A : Set G) → A ≤ centralizer (B : Set G))
    (hmax : Maximal (fun Γ => Γ ⊆ Δ ∧
      Γ.Pairwise (fun A B => A ≤ centralizer (B : Set G))) Γ)
    {A : Subgroup G} (hA : A ∈ Γ) {s : G} (hs : s ∈ S)
    (hsW : s ∈ normalizer ((sSup Γ : Subgroup G) : Set G)) :
    A.map (MulAut.conj s).toMonoidHom ∈ Γ := by
  apply (mem_iff_le_join hnorm hmax (hconj A (hmax.1.1 hA) s hs)).mpr
  rintro x ⟨y, hy, rfl⟩
  exact (mem_normalizer_iff.mp hsW y).mp (le_sSup hA hy)

/-- If normalization of the join forces centralization of the distinct chosen
members, its normalizer contains exactly the same original family members. -/
public theorem mem_iff_le_normalizer {Δ Γ : Set (Subgroup G)}
    (hmax : Maximal (fun Γ => Γ ⊆ Δ ∧
      Γ.Pairwise (fun A B => A ≤ centralizer (B : Set G))) Γ)
    (hstep : ∀ T ∈ Δ, T ≤ normalizer ((sSup Γ : Subgroup G) : Set G) →
      ∀ A ∈ Γ, T ≠ A → T ≤ centralizer (A : Set G))
    {T : Subgroup G} (hT : T ∈ Δ) :
    T ∈ Γ ↔ T ≤ normalizer ((sSup Γ : Subgroup G) : Set G) := by
  refine ⟨fun h => (le_sSup h).trans (sSup Γ).le_normalizer, fun hn => ?_⟩
  exact mem_of_centralizes hmax hT (hstep T hT hn)

end PairwiseCommutingFamily

/-- An `S`-invariant family inside a finite nilpotent subgroup `S` is pairwise
commuting if normalization forces distinct members to commute, and each member
permuting a pairwise commuting subfamily centralizes its distinct members.

Permutation is expressed by forward preservation for every element of `T`;
applying it to inverse elements supplies reverse preservation. -/
public theorem pairwise_commuting_of_normalizer_centralizes [Finite G]
    (Δ : Set (Subgroup G)) (S : Subgroup G) [Group.IsNilpotent S]
    (hsub : ∀ A ∈ Δ, A ≤ S)
    (hconj : ∀ A ∈ Δ, ∀ s ∈ S, A.map (MulAut.conj s).toMonoidHom ∈ Δ)
    (hnorm : ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B →
      B ≤ normalizer (A : Set G) → A ≤ centralizer (B : Set G))
    (hperm : ∀ Γ ⊆ Δ,
      Γ.Pairwise (fun A B => A ≤ centralizer (B : Set G)) →
      ∀ T ∈ Δ,
        (∀ t ∈ T, ∀ A ∈ Γ, A.map (MulAut.conj t).toMonoidHom ∈ Γ) →
        ∀ A ∈ Γ, T ≠ A → T ≤ centralizer (A : Set G)) :
    Δ.Pairwise (fun A B => A ≤ centralizer (B : Set G)) := by
  obtain ⟨Γ, hmax⟩ := PairwiseCommutingFamily.exists_maximal Δ
  let W := sSup Γ
  have hWS : W ≤ S := sSup_le fun A hA => hsub A (hmax.1.1 hA)
  have hstep : ∀ T ∈ Δ, T ≤ normalizer (W : Set G) →
      ∀ A ∈ Γ, T ≠ A → T ≤ centralizer (A : Set G) := by
    intro T hT hn
    apply hperm Γ hmax.1.1 hmax.1.2 T hT
    intro t ht A hA
    exact PairwiseCommutingFamily.conj_mem hconj hnorm hmax hA (hsub T hT ht) (hn ht)
  have hTΓ {T : Subgroup G} (hT : T ∈ Δ) :
      T ≤ normalizer (W : Set G) ↔ T ∈ Γ :=
    (PairwiseCommutingFamily.mem_iff_le_normalizer hmax hstep hT).symm
  let K := S ⊓ normalizer (W : Set G)
  have hWK : W ≤ K := le_inf hWS W.le_normalizer
  have hKS : K ≤ S := inf_le_left
  have hnormalizer : normalizer (K.subgroupOf S : Set S) ≤ K.subgroupOf S := by
    intro g hg
    have hgK : (g : G) ∈ normalizer (K : Set G) := by
      rw [← subgroupOf_normalizer_eq hKS] at hg
      exact hg
    have hpreserve (a : G) (haS : a ∈ S) (ha : a ∈ normalizer (K : Set G)) :
        W.map (MulAut.conj a).toMonoidHom ≤ W := by
      change (sSup Γ).map _ ≤ sSup Γ
      conv_lhs => rw [sSup_eq_iSup', map_iSup]
      apply iSup_le
      intro A
      have hcΔ : A.val.map (MulAut.conj a).toMonoidHom ∈ Δ :=
        hconj A.val (hmax.1.1 A.property) a haS
      have hcK : A.val.map (MulAut.conj a).toMonoidHom ≤ K := by
        rintro x ⟨y, hy, rfl⟩
        exact (mem_normalizer_iff.mp ha y).mp (hWK (le_sSup A.property hy))
      exact le_sSup ((hTΓ hcΔ).mp (hcK.trans inf_le_right))
    change (g : G) ∈ K
    refine ⟨g.property, ?_⟩
    change (g : G) ∈ normalizer (W : Set G)
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hpreserve g g.property hgK (mem_map_of_mem _ hx)
    · intro hx
      have hh := hpreserve (g : G)⁻¹ (S.inv_mem g.property)
        ((normalizer (K : Set G)).inv_mem hgK) (mem_map_of_mem _ hx)
      simpa [MulAut.conj_apply, mul_assoc] using hh
  have hKtop : K.subgroupOf S = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent) _
      (le_antisymm hnormalizer (K.subgroupOf S).le_normalizer)
  have hSK : S ≤ K := subgroupOf_eq_top.mp hKtop
  have hΔΓ : Δ ⊆ Γ := by
    intro T hT
    exact (hTΓ hT).mp ((hsub T hT).trans (hSK.trans inf_le_right))
  exact fun A hA B hB hne => hmax.1.2 (hΔΓ hA) (hΔΓ hB) hne

end Subgroup
