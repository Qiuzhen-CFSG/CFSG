module
public import Theory.GroupTheory.CyclicQuotientEmbedding
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms
public import Theory.PGroupCore
/-!
# Odd cyclic subgroups across a two-group kernel

A surjection with two-group kernel lifts an odd cyclic subgroup with the
same order and exact image. Construct an order-preserving cyclic embedding
in its preimage; coprime cardinalities make its restriction injective.
Coprime normalizer lifting also lifts an escaping inverter of that image to
an escaping normalizer of every odd-primary subgroup upstairs.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Finite G] [Group H]
theorem exists_cyclic_lift_of_two_kernel
    (q : G →* H) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (C : Subgroup H) [IsCyclic C] (ho : Odd (Nat.card C)) :
    ∃ B : Subgroup G, IsCyclic B ∧ B.map q = C ∧ Nat.card B = Nat.card C := by
  let : Finite H := Finite.of_surjective q hq
  let R := C.comap q
  let r : R →* C := q.subgroupComap C
  have hr : Function.Surjective r := q.subgroupComap_surjective_of_surjective C hq
  obtain ⟨j,hj⟩ := cyclic_injective_of_surjective r hr (MonoidHom.id C) Function.injective_id
  let f := R.subtype.comp j
  have hf : Function.Injective f := R.subtype_injective.comp hj
  let B := f.range
  have hc : Nat.card B = Nat.card C := (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  have hB : IsCyclic B := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hmap : B.map q ≤ C := by
    rintro _ ⟨x,⟨c,rfl⟩,rfl⟩
    exact (j c).property
  obtain ⟨k,hkcard⟩ := hk.exists_card_eq
  have hdis : Disjoint B q.ker := disjoint_of_coprime_natCard (by
    rw [hc,hkcard]
    exact ho.coprime_two_right.pow_right k)
  have hi : Function.Injective (q.comp B.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    exact Subtype.ext (hdis.le_bot ⟨x.property,hx⟩)
  let e : B ≃* B.map q := MulEquiv.ofBijective (q.subgroupMap B) ⟨by
    intro x y h
    exact hi (congrArg Subtype.val h),q.subgroupMap_surjective B⟩
  refine ⟨B,hB,?_,hc⟩
  apply eq_of_le_of_card_ge hmap
  rw [← Nat.card_congr e.toEquiv,hc]

theorem normalizer_not_le_of_inverted_image
    (q : G →* H) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (M A C : Subgroup G) (hAC : A ≤ C) {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hA : IsPGroup p A) (w : H)
    (hw : ∀ x ∈ C.map q, w*x*w⁻¹=x⁻¹) (hout : w ∉ M.map q) :
    ¬ normalizer (A : Set G) ≤ M := by
  let : Finite H := Finite.of_surjective q hq
  have hmap : (A.map q).map (MulAut.conj w).toMonoidHom ≤ A.map q := by
    rintro _ ⟨x,hx,rfl⟩
    change w*x*w⁻¹ ∈ A.map q
    rw [hw x (map_mono hAC hx)]
    exact (A.map q).inv_mem hx
  have hn : w ∈ normalizer (A.map q : Set H) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge hmap
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj w).toMonoidHom) (MulAut.conj w).injective]
  obtain ⟨k,hkcard⟩ := hk.exists_card_eq
  let : Fact (IsPGroup p A) := ⟨hA⟩
  have he := normalizer_map_eq_of_coprime_kernel p A q hq (by
    rw [hkcard]
    exact hp.coprime_two_right.pow_right k)
  rw [he] at hn
  obtain ⟨x,hx,hxw⟩ := hn
  intro hle
  exact hout ⟨x,hle hx,hxw⟩
end Theory.GroupTheory
