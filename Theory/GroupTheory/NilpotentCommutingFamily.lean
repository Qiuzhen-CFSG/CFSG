module

public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Order.Preorder.Finite

/-!
# Maximal commuting families in nilpotent groups

A maximal commuting subfamily contains exactly the original family's members
lying in its join. If every original member normalizing that join centralizes
its factors, the same description holds for the normalizer. Conjugation
invariance then makes the relative normalizer self-normalizing. The nilpotent
normalizer condition forces the maximal family to contain the whole family.

This is the group-theoretic normalizer argument of Aschbacher--Smith,
*The Classification of Quasithin Groups*, D.2.12, printed p.184. The action
and displacement hypotheses needed to apply it are deliberately separate.
-/

namespace Subgroup
variable {G : Type*} [Group G]

/-- Every two members centralize each other, including each member itself. -/
@[expose] public def IsCommutingFamily (F : Set (Subgroup G)) : Prop :=
  ∀ X ∈ F, ∀ Y ∈ F, X ≤ centralizer (Y : Set G)

/-- The join of a commuting family is abelian. -/
public theorem IsCommutingFamily.join_le_centralizer {F : Set (Subgroup G)}
    (hF : IsCommutingFamily F) : sSup F ≤ centralizer ((sSup F : Subgroup G) : Set G) := by
  apply sSup_le
  intro X hX
  apply le_centralizer_iff.mpr
  exact sSup_le fun Y hY => le_centralizer_iff.mp (hF X hX Y hY)

/-- A finite ambient group admits a maximal commuting subfamily. -/
public theorem exists_maximal_commuting_subfamily [Finite G] (F : Set (Subgroup G)) :
    ∃ Δ, Maximal (fun Δ => Δ ⊆ F ∧ IsCommutingFamily Δ) Δ := by
  apply Set.Finite.exists_maximal (Set.toFinite _)
  exact ⟨∅, Set.empty_subset F, by intro X hX; exact False.elim hX⟩

/-- Maximality absorbs every abelian member commuting with the chosen family. -/
public theorem mem_maximal_commuting_subfamily_of_centralizes
    {F Δ : Set (Subgroup G)}
    (hmax : Maximal (fun Δ => Δ ⊆ F ∧ IsCommutingFamily Δ) Δ)
    {X : Subgroup G} (hX : X ∈ F) (hself : X ≤ centralizer (X : Set G))
    (hcomm : ∀ Y ∈ Δ, X ≤ centralizer (Y : Set G)) : X ∈ Δ := by
  have hi : insert X Δ ⊆ F ∧ IsCommutingFamily (insert X Δ) := by
    refine ⟨Set.insert_subset hX hmax.1.1, ?_⟩
    intro A hA B hB
    rcases hA with rfl | hA <;> rcases hB with rfl | hB
    · exact hself
    · exact hcomm B hB
    · exact le_centralizer_iff.mp (hcomm A hA)
    · exact hmax.1.2 A hA B hB
  exact hmax.2 hi (Set.subset_insert X Δ) (Set.mem_insert X Δ)

/-- The canonical members contained in the join are exactly the maximal family. -/
public theorem mem_maximal_commuting_subfamily_iff_le_join
    {F Δ : Set (Subgroup G)}
    (habel : ∀ X ∈ F, X ≤ centralizer (X : Set G))
    (hmax : Maximal (fun Δ => Δ ⊆ F ∧ IsCommutingFamily Δ) Δ)
    {X : Subgroup G} (hX : X ∈ F) : X ∈ Δ ↔ X ≤ sSup Δ := by
  refine ⟨le_sSup, fun hXD => ?_⟩
  apply mem_maximal_commuting_subfamily_of_centralizes hmax hX (habel X hX)
  intro Y hY
  exact hXD.trans (hmax.1.2.join_le_centralizer.trans (centralizer_le (le_sSup hY)))

/-- Normalizing the join permutes the members of a maximal commuting family. -/
public theorem conj_mem_maximal_commuting_subfamily
    {F Δ : Set (Subgroup G)}
    (hconj : ∀ X ∈ F, ∀ g : G, X.conjBy g ∈ F)
    (habel : ∀ X ∈ F, X ≤ centralizer (X : Set G))
    (hmax : Maximal (fun Δ => Δ ⊆ F ∧ IsCommutingFamily Δ) Δ)
    {X : Subgroup G} (hX : X ∈ Δ) {g : G}
    (hg : g ∈ normalizer ((sSup Δ : Subgroup G) : Set G)) :
    X.conjBy g ∈ Δ := by
  apply (mem_maximal_commuting_subfamily_iff_le_join habel hmax
    (hconj X (hmax.1.1 hX) g)).mpr
  rintro x ⟨y, hy, rfl⟩
  exact (mem_normalizer_iff.mp hg y).mp (le_sSup hX hy)

/-- The normalizer has the same original factors as the maximal family, once
normalizing the join forces centralization. -/
public theorem mem_maximal_commuting_subfamily_iff_le_normalizer
    {F Δ : Set (Subgroup G)}
    (habel : ∀ X ∈ F, X ≤ centralizer (X : Set G))
    (hmax : Maximal (fun Δ => Δ ⊆ F ∧ IsCommutingFamily Δ) Δ)
    (hstep : ∀ X ∈ F, X ≤ normalizer ((sSup Δ : Subgroup G) : Set G) →
      ∀ Y ∈ Δ, X ≤ centralizer (Y : Set G))
    {X : Subgroup G} (hX : X ∈ F) :
    X ∈ Δ ↔ X ≤ normalizer ((sSup Δ : Subgroup G) : Set G) := by
  refine ⟨fun hX => (le_sSup hX).trans (sSup Δ).le_normalizer, fun hn => ?_⟩
  exact mem_maximal_commuting_subfamily_of_centralizes hmax hX (habel X hX)
    (hstep X hX hn)

/-- A conjugation-invariant family generating a nilpotent subgroup commutes if
normalizing a commuting subfamily's join forces centralization of its members. -/
public theorem commutingFamily_of_normalizer_centralizes [Finite G]
    (F : Set (Subgroup G)) (N : Subgroup G) [Group.IsNilpotent N]
    (hgen : sSup F = N)
    (hconj : ∀ X ∈ F, ∀ g : G, X.conjBy g ∈ F)
    (habel : ∀ X ∈ F, X ≤ centralizer (X : Set G))
    (hstep : ∀ Δ, Maximal (fun Δ => Δ ⊆ F ∧ IsCommutingFamily Δ) Δ →
      ∀ X ∈ F, X ≤ normalizer ((sSup Δ : Subgroup G) : Set G) →
      ∀ Y ∈ Δ, X ≤ centralizer (Y : Set G)) : IsCommutingFamily F := by
  obtain ⟨Δ, hmax⟩ := exists_maximal_commuting_subfamily F
  let D := sSup Δ
  have hDN : D ≤ N := by rw [← hgen]; exact sSup_le_sSup hmax.1.1
  have hXΔ {X : Subgroup G} (hX : X ∈ F) :
      X ≤ normalizer (D : Set G) ↔ X ∈ Δ := by
    exact (mem_maximal_commuting_subfamily_iff_le_normalizer
      habel hmax (hstep Δ hmax) hX).symm
  let K := N ⊓ normalizer (D : Set G)
  have hDK : D ≤ K := le_inf hDN D.le_normalizer
  have hKN : K ≤ N := inf_le_left
  have hnormalizer : normalizer (K.subgroupOf N : Set N) ≤ K.subgroupOf N := by
    intro g hg
    have hgK : (g : G) ∈ normalizer (K : Set G) := by
      rw [← subgroupOf_normalizer_eq hKN] at hg
      exact hg
    have hpreserve (a : G) (ha : a ∈ normalizer (K : Set G)) :
        D.map (MulAut.conj a).toMonoidHom ≤ D := by
      change (sSup Δ).map _ ≤ sSup Δ
      conv_lhs => rw [sSup_eq_iSup', map_iSup]
      apply iSup_le
      intro X
      have hcF : X.val.conjBy a ∈ F := hconj X.val (hmax.1.1 X.property) a
      have hcK : X.val.conjBy a ≤ K := by
        rintro x ⟨y, hy, rfl⟩
        exact (mem_normalizer_iff.mp ha y).mp (hDK (le_sSup X.property hy))
      exact le_sSup ((hXΔ hcF).mp (hcK.trans inf_le_right))
    change (g : G) ∈ K
    refine ⟨g.property, ?_⟩
    change (g : G) ∈ normalizer (D : Set G)
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hpreserve g hgK (mem_map_of_mem _ hx)
    · intro hx
      have hh := hpreserve (g : G)⁻¹ ((normalizer (K : Set G)).inv_mem hgK)
        (mem_map_of_mem _ hx)
      simpa [MulAut.conj_apply, mul_assoc] using hh
  have hKtop : K.subgroupOf N = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent) _
      (le_antisymm hnormalizer (K.subgroupOf N).le_normalizer)
  have hNK : N ≤ K := subgroupOf_eq_top.mp hKtop
  have hFΔ : F ⊆ Δ := by
    intro X hX
    apply (hXΔ hX).mp
    have hXN : X ≤ N := by rw [← hgen]; exact le_sSup hX
    exact hXN.trans (hNK.trans inf_le_right)
  exact fun X hX Y hY => hmax.1.2 X (hFΔ hX) Y (hFΔ hY)

end Subgroup
