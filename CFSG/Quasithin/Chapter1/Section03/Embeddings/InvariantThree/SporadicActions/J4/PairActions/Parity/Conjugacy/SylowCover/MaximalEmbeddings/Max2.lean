module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Reduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl


/-!
# Conjugacy of maximal embeddings of the literal J₄ max2 subgroup

The certified relative normal closure is a normal two-group and its relative
centralizer consists of the powers of the distinguished central involution.
Every local Sylow therefore has just that one nonidentity central element.
Transport a Sylow through the given isomorphism, then conjugate its image to
the ambient Sylow in the maximal subgroup. The unique central element is
central in both embeddings. Its ambient centralizer is proper by simplicity
and perfectness, so maximality and equal orders identify the embeddings.

The comparison `sourceSubgroupEquivLocal` is the proved word conjugation from
the original ATLAS outputs to the local carrier. The proof needs neither
exhaustive maximal-subgroup classification nor full centralizer generation.

Source context: Kleidman–Wilson, *The maximal subgroups of J₄*, Proc. London
Math. Soc. 56 (1988), 484–510; GLS3, Table 5.3i, printed p.270. Concrete
ATLAS provenance is recorded in `TwoCoreCentralizer.Max2Bridge`.
-/

public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover

open Subgroup

private theorem center_bot_of_perfect_simple {G : Type*} [Group G]
    [Group.IsPerfect G] [IsSimpleGroup G] : center G = ⊥ := by
  rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative G (center_eq_top_iff.mp h)).elim

private theorem conjugate_range_of_sylow_center
    {G H : Type*} [Group G] [Finite G] [Group.IsPerfect G] [IsSimpleGroup G]
    [Group H] [Finite H] (z : H) (hz : z ≠ 1) (hzc : z ∈ center H)
    (hlocal : ∀ P : Sylow 2 H, z ∈ P ∧
      ∀ x : H, x ∈ P → (∀ y : H, y ∈ P → y * x = x * y) → x ≠ 1 → x = z)
    (i : H →* G) (hi : Function.Injective i)
    (S : Sylow 2 G) (M : Subgroup G) (hM : IsCoatom M) (hSM : S.toSubgroup ≤ M)
    (e : M ≃* H) : ∃ g : G, M = i.range.map (MulAut.conj g).toMonoidHom := by
  let P := (S.subtype hSM).mapSurjective (f := e.toMonoidHom) e.surjective
  have hcard : Nat.card P = Nat.card S := by
    change Nat.card ((S.subtype hSM).toSubgroup.map e.toMonoidHom) = Nat.card S
    rw [card_map_of_injective e.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hSM).toEquiv
  let T : Sylow 2 G := Sylow.ofCard (P.toSubgroup.map i) (by
    rw [card_map_of_injective hi, hcard, S.card_eq_multiplicity])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  let j : H →* G := (MulAut.conj g).toMonoidHom.comp i
  have hj : Function.Injective j := (MulAut.conj g).injective.comp hi
  have hPS : P.toSubgroup.map j = S.toSubgroup := by
    change P.toSubgroup.map ((MulAut.conj g).toMonoidHom.comp i) = _
    rw [← map_map]
    exact congrArg Sylow.toSubgroup hg
  have hzP := (hlocal P).1
  have hzS : j z ∈ S := by
    change j z ∈ S.toSubgroup
    rw [← hPS]
    exact mem_map_of_mem j hzP
  have hzj : j z ≠ 1 := by
    intro h
    exact hz (hj (h.trans j.map_one.symm))
  have hjc (x : H) : j x * j z = j z * j x := by
    simpa only [map_mul] using congrArg j (mem_center_iff.mp hzc x)
  have hSc (x : G) (hx : x ∈ S) : x * j z = j z * x := by
    change x ∈ S.toSubgroup at hx
    rw [← hPS] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact hjc y
  let m : M := ⟨j z, hSM hzS⟩
  have hem : e m = z := by
    apply (hlocal P).2 (e m)
    · exact mem_map_of_mem e.toMonoidHom hzS
    · intro y hy
      obtain ⟨v, hv, rfl⟩ := hy
      have hv' : (v : G) ∈ S := hv
      have hc : v * m = m * v := Subtype.ext (hSc v hv')
      change e v * e m = e m * e v
      simpa only [map_mul] using congrArg e hc
    · intro h
      have hm : m = 1 := e.injective (h.trans e.map_one.symm)
      exact hzj (congrArg Subtype.val hm)
  have hMC : M ≤ centralizer ({j z} : Set G) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    have hc : (⟨x, hx⟩ : M) * m = m * ⟨x, hx⟩ := by
      apply e.injective
      simpa only [map_mul, hem] using mem_center_iff.mp hzc (e ⟨x, hx⟩)
    exact congrArg Subtype.val hc
  have hC : centralizer ({j z} : Set G) ≠ ⊤ := by
    intro h
    have hc : j z ∈ center G := by
      rw [mem_center_iff]
      intro x
      exact mem_centralizer_singleton_iff.mp (h ▸ mem_top x)
    rw [center_bot_of_perfect_simple] at hc
    exact hzj hc
  have hCM : centralizer ({j z} : Set G) = M := (hM.le_iff_eq hC).mp hMC
  have hrange : j.range ≤ M := by
    rw [← hCM]
    rintro x ⟨y, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (hjc y)
  have heq : M = j.range := by
    symm
    apply eq_of_le_of_card_ge hrange
    exact le_of_eq ((Nat.card_congr e.toEquiv).trans
      (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv))
  refine ⟨g, ?_⟩
  simpa only [j, MonoidHom.range_comp] using heq

open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

private theorem local_sylow_center (P : Sylow 2 localSubgroup) :
    subgroupInvolution ∈ P ∧
      ∀ x : localSubgroup, x ∈ P →
        (∀ y : localSubgroup, y ∈ P → y * x = x * y) →
        x ≠ 1 → x = subgroupInvolution := by
  classical
  have hNP := localNormalClosure_isPGroup.le_sylow_of_normal P
  refine ⟨hNP subgroupInvolution_mem_normalClosure, ?_⟩
  intro x _ hx hne
  have hc : x ∈ centralizer (localNormalClosure : Set localSubgroup) := by
    intro n hn
    exact hx n (hNP hn)
  rw [localNormalClosure_centralizer_eq_zpowers] at hc
  obtain ⟨k, hk, hpow⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hc)
  have hk' : k < 2 := by simpa only [Finset.mem_range, orderOf_subgroupInvolution] using hk
  interval_cases k
  · exact (hne (by simpa using hpow.symm)).elim
  · simpa using hpow.symm

attribute [local irreducible] sourceSubgroup localSubgroup sourceSubgroupEquivLocal

/-- Every maximal Sylow overgroup isomorphic to the original max2 word
subgroup is conjugate to that exact subgroup in the `g L g⁻¹` convention. -/
theorem max2MaximalEmbeddingConjugacy : MaximalEmbeddingConjugacyAt sourceSubgroup := by
  intro _ _ _ S M hM hSM he
  obtain ⟨e⟩ := he
  let c : sourceSubgroup ≃* localSubgroup := sourceSubgroupEquivLocal
  let i : localSubgroup →* Janko4.Model :=
    sourceSubgroup.subtype.comp c.symm.toMonoidHom
  have hi : Function.Injective i :=
    sourceSubgroup.subtype_injective.comp c.symm.injective
  have hirange : i.range = sourceSubgroup := by
    change (sourceSubgroup.subtype.comp c.symm.toMonoidHom).range = sourceSubgroup
    rw [MonoidHom.range_comp]
    rw [MonoidHom.range_eq_top.mpr c.symm.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hz : subgroupInvolution ≠ 1 := by
    intro h
    have ho := orderOf_subgroupInvolution
    rw [h, orderOf_one] at ho
    exact (by decide : (1 : ℕ) ≠ 2) ho
  obtain ⟨g, hg⟩ := conjugate_range_of_sylow_center (G := Janko4.Model) (H := localSubgroup)
    subgroupInvolution hz
    NormalClosureControl.involution_mem_center local_sylow_center i hi S M hM hSM
    (e.trans c)
  exact ⟨g, by rwa [hirange] at hg⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover
