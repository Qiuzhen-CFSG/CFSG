module
public import Theory.GroupTheory.PCoreNormalizerAction
public import Theory.GroupTheory.PrimeRankResidualCentralizer

/-!
# The literal core-quotient action kernel inside an overgroup

Intersect the normalizer's quotient-action kernel with a specified overgroup
N. Commutators in the embedded core characterize membership in this kernel.
When N normalizes J, this is exactly the image of the kernel of the restricted
action N → Aut(J/O_p(J)); the outer-action kernel is J times that kernel.

For an odd prime, the kernel and J have additive ranks whenever the center
of J/O₂(J) has coprime order. Passing to the quotient by O₂(J) reduces this
to the commuting-rank inequality, with all maps fixed.

Source application: Aschbacher--Smith 14.6.15, printed p.1035. The escaping
component's kernel contains K₂ and has five-rank one when J does.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] (p : ℕ) (J N : Subgroup G)

/-- The original ambient subgroup of actors trivial on J/O_p(J). -/
def pCoreActionKernelIn : Subgroup G :=
  N ⊓ ((pCoreNormalizerAction p J).ker).map (normalizer (J : Set G)).subtype

/-- Kernel elements normalize the original subgroup. -/
theorem pCoreActionKernelIn_le_normalizer :
    pCoreActionKernelIn p J N ≤ normalizer (J : Set G) :=
  inf_le_right.trans (map_subtype_le _)

/-- A specified normalized subgroup lies in the kernel exactly when its action is trivial. -/
theorem le_pCoreActionKernelIn_iff (K : Subgroup G)
    (hK : K ≤ normalizer (J : Set G)) :
    K ≤ pCoreActionKernelIn p J N ↔ K ≤ N ∧
      ∀ k : K, pCoreNormalizerAction p J (inclusion hK k) = 1 := by
  constructor
  · intro h
    refine ⟨h.trans inf_le_left,?_⟩
    intro k
    obtain ⟨x,hx,he⟩ := (h k.property).2
    have he' : x = inclusion hK k := Subtype.ext he
    exact he' ▸ hx
  · rintro ⟨hKN,ha⟩ k hk
    exact ⟨hKN hk,inclusion hK ⟨k,hk⟩,ha ⟨k,hk⟩,rfl⟩

/-- Commutator containment in the local core gives membership in this literal kernel. -/
theorem le_pCoreActionKernelIn_of_commutator (K : Subgroup G)
    (hKN : K ≤ N) (hKJ : K ≤ normalizer (J : Set G))
    (hc : ⁅J,K⁆ ≤ J.pCoreIn p) : K ≤ pCoreActionKernelIn p J N := by
  apply (le_pCoreActionKernelIn_iff p J N K hKJ).mpr
  refine ⟨hKN,?_⟩
  intro k
  apply (pCoreNormalizerAction_eq_one_iff p J (inclusion hKJ k)).mpr
  intro j
  rw [commutator_comm] at hc
  obtain ⟨u,hu,he⟩ := hc (commutator_mem_commutator k.property j.property)
  have he' : u = J.normalizerMonoidHom (inclusion hKJ k) j / j := by
    apply Subtype.ext
    change (u : G) = (k : G) * j * (k : G)⁻¹ / j
    simpa only [commutatorElement_def,div_eq_mul_inv,Subgroup.subtype_apply] using he
  exact he' ▸ hu

/-- When N normalizes J, the ambient kernel is the image of the restricted action kernel. -/
theorem pCoreActionKernelIn_eq_map_ker (hN : N ≤ normalizer (J : Set G)) :
    pCoreActionKernelIn p J N =
      (((pCoreNormalizerAction p J).comp (inclusion hN)).ker).map N.subtype := by
  ext x
  constructor
  · rintro ⟨hxN,y,hy,he⟩
    refine ⟨⟨x,hxN⟩,?_,rfl⟩
    have hy' : y = inclusion hN ⟨x,hxN⟩ := Subtype.ext he
    change pCoreNormalizerAction p J (inclusion hN ⟨x,hxN⟩) = 1
    rw [←hy']
    exact hy
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.property,inclusion hN y,hy,rfl⟩

/-- The outer-action kernel in N is its original J times the quotient-action kernel. -/
theorem pCoreNormalizerOuterAction_restrict_ker
    (hJN : J ≤ N) (hN : N ≤ normalizer (J : Set G)) :
    ((pCoreNormalizerOuterAction p J).comp (inclusion hN)).ker =
      J.subgroupOf N ⊔ ((pCoreNormalizerAction p J).comp (inclusion hN)).ker := by
  let f := (pCoreNormalizerAction p J).comp (inclusion hN)
  have hm : (J.subgroupOf N).map f = MulAut.innerSubgroup (J ⧸ pCore p J) := by
    apply le_antisymm
    · rintro α ⟨x,hx,rfl⟩
      exact ⟨QuotientGroup.mk' (pCore p J) ⟨x,hx⟩,
        (pCoreNormalizerAction_on_component p J ⟨x,hx⟩).symm⟩
    · rintro α ⟨y,rfl⟩
      obtain ⟨j,rfl⟩ := QuotientGroup.mk'_surjective (pCore p J) y
      exact ⟨inclusion hJN j,j.property,pCoreNormalizerAction_on_component p J j⟩
  have he : ((pCoreNormalizerOuterAction p J).comp (inclusion hN)).ker =
      (MulAut.innerSubgroup (J ⧸ pCore p J)).comap f := by
    ext x
    exact QuotientGroup.eq_one_iff _
  rw [he,←hm,comap_map_eq]

/-- Kernel commutators lie in O_p(J), without any ordinary centralization claim. -/
theorem pCoreActionKernelIn_commutator :
    ⁅J,pCoreActionKernelIn p J N⁆ ≤ J.pCoreIn p := by
  have h := (le_pCoreActionKernelIn_iff p J N (pCoreActionKernelIn p J N)
    (pCoreActionKernelIn_le_normalizer p J N)).mp le_rfl
  exact commutator_le_core_of_pCoreNormalizerAction_eq_one p J _
    (pCoreActionKernelIn_le_normalizer p J N) h.2

omit p in
/-- The quotient-action kernel and J consume independent odd rank. -/
theorem pCoreActionKernelIn_rank_add_le [Finite G] {r : ℕ} [Fact r.Prime]
    (hr : Odd r) (hJN : J ≤ N)
    (hz : Nat.Coprime r (Nat.card (center (J ⧸ pCore 2 J)))) :
    primeRank r (pCoreActionKernelIn 2 J N) + primeRank r J ≤ primeRank r N := by
  let K := pCoreActionKernelIn 2 J N
  have hc : ⁅(pResidual 2 K).map K.subtype,J⁆ ≤ J.pCoreIn 2 := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl (map_subtype_le _)).trans
      (pCoreActionKernelIn_commutator 2 J N)
  have h := Theory.GroupTheory.ResidualCentralizerRank.primeRank_sum_le_of_normalized_factor
    hr K J (pCoreActionKernelIn_le_normalizer 2 J N) hc hz
  exact h.trans (primeRank_mono r (sup_le inf_le_left hJN))
end Subgroup
