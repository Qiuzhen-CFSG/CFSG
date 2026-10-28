module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenCounts.Geometry

/-!
# Inversion subgroups in the seven-centralizer normalizer

The literal quotient of H = N_G(A) by A = C_G(S) is cyclic of order six.
Coprimality shows that A meets an external conjugate of H trivially:
an element in that intersection first maps trivially to its cyclic quotient,
and then the trivial-intersection criterion for A applies. Thus the two
normalizers intersect in a cyclic group of order dividing six. Equalizing
conjugation and inversion inside that group constructs the exact inverted
subgroup used by the fiber count.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), proof of (4.3), printed p.226.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
namespace BenderSevenStructure
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {h : Janko1CentralizerData G} {d : ℕ} (localData : BenderPrimeData G d)
    {S : Subgroup G} (hS : Nat.card S = 7) (structureData : BenderSevenStructure h S)

local notation "A" => centralizer (S : Set G)
local notation "H" => normalizer (A : Set G)
local notation "C" => (H ⊓ centralizer (Set.singleton structureData.t) : Subgroup G)

include localData hS structureData

/-- The quotient by the seven-centralizer is cyclic of order six. -/
public theorem fiber_quotient : IsCyclic (H ⧸ (A).subgroupOf H) ∧
    Nat.card (H ⧸ (A).subgroupOf H) = 6 := by
  let q := QuotientGroup.mk' ((A).subgroupOf H)
  let f : C →* H ⧸ (A).subgroupOf H := q.comp (inclusion inf_le_left)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((A).subgroupOf H) y
    obtain ⟨a, ha, c, hc, he⟩ := structureData.factorization x x.2
    refine ⟨⟨c, hc⟩, ?_⟩
    have hax : (⟨a, le_normalizer ha⟩ : H) * ⟨c, hc.1⟩ = x := Subtype.ext he.symm
    change q ⟨c, hc.1⟩ = q x
    have hqa : q ⟨a, le_normalizer ha⟩ = 1 :=
      (QuotientGroup.eq_one_iff (⟨a, le_normalizer ha⟩ : H)).mpr ha
    rw [← hax, map_mul, hqa, one_mul]
  let _ : IsCyclic C := structureData.complement_cyclic
  refine ⟨isCyclic_of_surjective f hf, ?_⟩
  have he := ((A).subgroupOf H).card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr (subgroupOfEquivOfLe (le_normalizer : A ≤ H)).toEquiv,
    structureData.normalizer_card localData hS] at he
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos he.symm

/-- Every subgroup of the normalizer disjoint from the kernel embeds in its cyclic quotient. -/
public theorem fiber_disjoint_cyclic (K : Subgroup G) (hKH : K ≤ H)
    (hKA : Disjoint K A) : IsCyclic K ∧ Nat.card K ∣ 6 := by
  let q := QuotientGroup.mk' ((A).subgroupOf H)
  let f : K →* H ⧸ (A).subgroupOf H := q.comp (inclusion hKH)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxA : (x : G) ∈ A := (QuotientGroup.eq_one_iff (⟨x, hKH x.2⟩ : H)).mp hx
    exact Subtype.ext (hKA.le_bot ⟨x.2, hxA⟩)
  obtain ⟨hcyc, hcard⟩ := structureData.fiber_quotient localData hS
  let _ := hcyc
  exact ⟨isCyclic_of_injective f hf, hcard ▸ card_dvd_of_injective f hf⟩

/-- An element whose order divides the kernel order belongs to the kernel. -/
public theorem fiber_coprime_order_mem_kernel (x : G) (hx : x ∈ H)
    (hp : x ^ Nat.card A = 1) : x ∈ A := by
  let q := QuotientGroup.mk' ((A).subgroupOf H)
  let y : H ⧸ (A).subgroupOf H := q ⟨x, hx⟩
  have hyA : y ^ Nat.card A = 1 := by
    rw [← map_pow]
    exact congrArg q (Subtype.ext hp)
  have hy6 : y ^ 6 = 1 := by
    rw [← (structureData.fiber_quotient localData hS).2]
    exact pow_card_eq_one'
  have hy1 := (pow_eq_one_iff_of_coprime
    ((h.seven_centralizer_coprime localData S hS).of_dvd_right (by decide : 6 ∣ 120))).mp
      ⟨hyA, hy6⟩
  exact (QuotientGroup.eq_one_iff (⟨x, hx⟩ : H)).mp hy1

/-- Distinct conjugate normalizers intersect in a cyclic group of order dividing six. -/
public theorem fiber_external_intersection (u : G) (huH : u ∉ H) :
    IsCyclic (H ⊓ (H).comap (MulAut.conj u).toMonoidHom : Subgroup G) ∧
      Nat.card (H ⊓ (H).comap (MulAut.conj u).toMonoidHom : Subgroup G) ∣ 6 := by
  apply structureData.fiber_disjoint_cyclic localData hS _ inf_le_left
  apply disjoint_iff_inf_le.mpr
  intro x hxx
  obtain ⟨hx, hxA⟩ := hxx
  change x = 1
  have hp : x ^ Nat.card A = 1 := congrArg Subtype.val
    (pow_card_eq_one' (x := (⟨x, hxA⟩ : A)))
  have huxA : (MulAut.conj u) x ∈ A :=
    structureData.fiber_coprime_order_mem_kernel localData hS _ hx.2 (by
      rw [← map_pow, hp, map_one])
  by_contra hx1
  exact huH (structureData.normalizes_of_conjugate_kernel_ne_one u x hxA hx1 huxA)

/-- The literal set of elements inverted by an external element is a cyclic subgroup of order dividing six. -/
public theorem fiber_inverted_subgroup (u : G) (huH : u ∉ H) :
    ∃ K : Subgroup G,
      (∀ x : G, x ∈ K ↔ x ∈ H ∧ u * x * u⁻¹ = x⁻¹) ∧
      IsCyclic K ∧ Nat.card K ∣ 6 := by
  let I := H ⊓ (H).comap (MulAut.conj u).toMonoidHom
  obtain ⟨hcyc, hcard⟩ := structureData.fiber_external_intersection localData hS u huH
  let _ : IsCyclic I := hcyc
  let _ : CommGroup I := IsCyclic.commGroup
  let e : I →* G := (MulAut.conj u).toMonoidHom.comp I.subtype
  let f : I →* G := I.subtype.comp invMonoidHom
  let K := (e.eqLocus f).map I.subtype
  refine ⟨K, ?_, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2.1, hy⟩
    · rintro ⟨hxH, hxinv⟩
      have hxI : x ∈ I := ⟨hxH, show u * x * u⁻¹ ∈ H by rw [hxinv]; exact inv_mem hxH⟩
      exact ⟨⟨x, hxI⟩, hxinv, rfl⟩
  · exact ((e.eqLocus f).equivMapOfInjective I.subtype I.subtype_injective).isCyclic.mp
      inferInstance
  · have hKI : K ≤ I := by
      rintro x ⟨y, _, rfl⟩
      exact y.2
    exact (card_dvd_of_le hKI).trans hcard

end BenderSevenStructure
end CFSG.Quasithin.Janko1CentralizerData
