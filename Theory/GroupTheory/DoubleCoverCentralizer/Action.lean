module
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic

/-!
# Inner actors and the order of the component centralizer

For a faithful action whose image is the full centralizer of the inner action
of a perfect subgroup J, the conjugation image of C_H(J) is exactly the inner
part of the actor group. Its kernel is Z(H), giving an exact cardinality formula.
An outer image of order at most two for a four-group gives a nonidentity inner
actor and a centralizer of order four or eight when the center has order two.

These are the group-theoretic deductions in the last paragraph of Aschbacher–Smith,
16.3.6, printed p.1179 / PDF p.1196 (1 March 2004 manuscript). The bound on the
outer image is a separate model-table obligation, not asserted here.
-/

@[expose] public section
namespace Theory.GroupTheory.DoubleCoverCentralizer
open Subgroup Theory.GroupTheory
variable {H A : Type*} [Group H] [Group A]

/-- The inner actors, defined as a subgroup of the given actor group. -/
def innerActors (α : A →* MulAut H) : Subgroup A :=
  (MulAut.conj : H →* MulAut H).range.comap α

/-- The conjugation image of the actual centralizer is the intersection of
the full action-centralizer image with the inner automorphism group. -/
theorem centralizer_conj_range (J : Subgroup H) [Group.IsPerfect J]
    (α : A →* MulAut H)
    (himage : α.range = centralizer (J.map MulAut.conj : Set (MulAut H))) :
    ((MulAut.conj : H →* MulAut H).comp (centralizer (J : Set H)).subtype).range =
      (innerActors α).map α := by
  ext a
  constructor
  · rintro ⟨f, rfl⟩
    have hm : MulAut.conj (f : H) ∈ α.range := by
      rw [himage]
      exact (conj_mem_centralizer_iff J f).mpr f.property
    obtain ⟨e, he⟩ := hm
    exact ⟨e, (show α e ∈ (MulAut.conj : H →* MulAut H).range from
      he.symm ▸ ⟨f, rfl⟩), he⟩
  · rintro ⟨e, he, rfl⟩
    obtain ⟨f, hf⟩ := he
    have hm : MulAut.conj f ∈ centralizer (J.map MulAut.conj : Set (MulAut H)) := by
      rw [hf, ← himage]
      exact ⟨e, rfl⟩
    exact ⟨⟨f, (conj_mem_centralizer_iff J f).mp hm⟩, hf⟩

/-- The centralizer has center-kernel times inner-action image order. -/
theorem centralizer_card (J : Subgroup H) [Group.IsPerfect J]
    (α : A →* MulAut H) (hinj : Function.Injective α)
    (himage : α.range = centralizer (J.map MulAut.conj : Set (MulAut H))) :
    Nat.card (centralizer (J : Set H)) = Nat.card (center H) * Nat.card (innerActors α) := by
  let C := centralizer (J : Set H)
  let f := (MulAut.conj : H →* MulAut H).comp C.subtype
  have hk : f.ker = (center H).subgroupOf C := by
    ext c
    change MulAut.conj (c : H) = 1 ↔ (c : H) ∈ center H
    rw [← conj_kernel]
    rfl
  have hkcard : Nat.card f.ker = Nat.card (center H) := by
    rw [hk]
    exact Nat.card_congr (subgroupOfEquivOfLe (center_le_centralizer (J : Set H))).toEquiv
  have hr : Nat.card f.range = Nat.card (innerActors α) := by
    rw [centralizer_conj_range J α himage]
    exact card_map_of_injective hinj
  calc
    Nat.card C = Nat.card f.ker * f.ker.index := f.ker.card_mul_index.symm
    _ = Nat.card (center H) * Nat.card (innerActors α) := by
      rw [index_ker, hkcard, hr]

/-- An index at most two in a four-group supplies at least two inner actors. -/
theorem innerActors_card (α : A →* MulAut H) (hA : Nat.card A = 4)
    (hidx : (innerActors α).index ≤ 2) :
    Nat.card (innerActors α) = 2 ∨ Nat.card (innerActors α) = 4 := by
  have hmul := (innerActors α).card_mul_index
  rw [hA] at hmul
  have hd : Nat.card (innerActors α) ∣ 2 ^ 2 := ⟨(innerActors α).index, hmul.symm⟩
  obtain ⟨k, hk, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases k <;> simp_all

/-- The same inequality follows from the ordinary outer automorphism index. -/
theorem innerActors_index_le_outer [Finite H] (α : A →* MulAut H)
    (houter : (MulAut.conj : H →* MulAut H).range.index ≤ 2) :
    (innerActors α).index ≤ 2 := by
  let Inn := (MulAut.conj : H →* MulAut H).range
  have hn : Inn.Normal := by
    refine ⟨?_⟩
    rintro a ⟨x, rfl⟩ b
    exact ⟨b x, by ext y; simp [MulAut.conj_apply]⟩
  let := hn
  have hd : (innerActors α).index ∣ Inn.index := by
    rw [innerActors, index_comap]
    exact relIndex_dvd_index_of_normal _ _
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Inn.index_ne_zero_of_finite) hd).trans houter

/-- A faithful four-group has a nonidentity inner actor as soon as its
image in the outer automorphism group has order at most two. -/
theorem exists_inner_actor [Finite A] (α : A →* MulAut H) (hA : Nat.card A = 4)
    (hidx : (innerActors α).index ≤ 2) :
    ∃ e : A, e ≠ 1 ∧ ∃ f : H, α e = MulAut.conj f := by
  have hc : 1 < Nat.card (innerActors α) := by
    rcases innerActors_card α hA hidx with h | h <;> omega
  let : Nontrivial (innerActors α) := Finite.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨e, he⟩ := exists_ne (1 : innerActors α)
  obtain ⟨f, hf⟩ := e.property
  exact ⟨e, fun hh => he (Subtype.ext hh), f, hf.symm⟩

end Theory.GroupTheory.DoubleCoverCentralizer
