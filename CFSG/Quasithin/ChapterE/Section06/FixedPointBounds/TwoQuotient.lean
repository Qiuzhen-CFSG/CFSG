module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Parameter
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The Cartan parameter across a two-group quotient

An odd Cartan subgroup maps trivially into a two-group. Intersecting the
ambient Sylow with a normal kernel then retains the complete Cartan
witness. For a centerless group with two-group outer automorphism group,
this bounds every intermediate automorphism subgroup by the inner group.

Source application: Aschbacher--Smith, Definition E.3.37 and the Mathieu
rows of Tables 7.2.1 and 7.3.4, printed pp.239 and 698--699.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds

universe u v
variable {G : Type u} [Group G] [Finite G]

noncomputable def NPrimeWitness.restrictNormal {c : ℕ} (w : NPrimeWitness G c)
    (N : Subgroup G) [N.Normal] (hB : w.abelianGroup ≤ N) : NPrimeWitness N c := by
  classical
  letI := w.abelian
  letI := w.cyclic
  let T := (w.sylow.exists_subgroupOf_eq_of_normal N).choose
  have hT : (T : Subgroup N) = (w.sylow : Subgroup G).subgroupOf N :=
    (w.sylow.exists_subgroupOf_eq_of_normal N).choose_spec
  let eB := subgroupOfEquivOfLe hB
  let eY := subgroupOfEquivOfLe (w.cyclic_le.trans hB)
  refine {
    abelianGroup := w.abelianGroup.subgroupOf N
    cyclicGroup := w.cyclicGroup.subgroupOf N
    sylow := T
    cyclic_le := comap_mono w.cyclic_le
    abelian := IsMulCommutative.of_comm (fun a b =>
      Subtype.ext (Subtype.ext (setLike_mul_comm (s := w.abelianGroup) a.property b.property)))
    odd := (Nat.card_congr eB.toEquiv).symm ▸ w.odd
    cyclic := isCyclic_of_surjective eY.symm eY.symm.surjective
    card := (Nat.card_congr eY.toEquiv).trans w.card
    permutes := ?_
  }
  change (w.abelianGroup.subgroupOf N : Set N) * (T : Subgroup N) =
    (T : Subgroup N) * (w.abelianGroup.subgroupOf N : Set N)
  rw [hT]
  ext x
  constructor
  · rintro ⟨b, hb, s, hs, rfl⟩
    have hx : (b.val * s.val) ∈
        (w.sylow : Set G) * (w.abelianGroup : Set G) := by
      rw [← w.permutes]
      exact ⟨b.val, hb, s.val, hs, rfl⟩
    obtain ⟨t, ht, a, ha, he⟩ := hx
    have htN : t ∈ N := by
      have htN := N.mul_mem (N.mul_mem b.property s.property) (N.inv_mem (hB ha))
      rwa [← he, mul_inv_cancel_right] at htN
    exact ⟨⟨t, htN⟩, ht, ⟨a, hB ha⟩, ha, Subtype.ext he⟩
  · rintro ⟨s, hs, b, hb, rfl⟩
    have hx : (s.val * b.val) ∈
        (w.abelianGroup : Set G) * (w.sylow : Set G) := by
      rw [w.permutes]
      exact ⟨s.val, hs, b.val, hb, rfl⟩
    obtain ⟨a, ha, t, ht, he⟩ := hx
    have htN : t ∈ N := by
      have htN := N.mul_mem (N.inv_mem (hB ha)) (N.mul_mem s.property b.property)
      rwa [← he, inv_mul_cancel_left] at htN
    exact ⟨⟨a, hB ha⟩, ha, ⟨t, htN⟩, ht, Subtype.ext he⟩

omit [Finite G] in
private theorem odd_subgroup_le_ker_of_two_group {Q : Type v} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (f : G →* Q) (B : Subgroup G) (hB : Odd (Nat.card B)) :
    B ≤ f.ker := by
  have hp := hQ.to_subgroup (B.map f)
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have ho := hB.of_dvd_nat (card_map_dvd B f)
  have hone : Nat.card (B.map f) = 1 := by
    rw [hn] at ho ⊢
    by_cases h : n = 0
    · simp [h]
    · exact (ho.not_two_dvd_nat (by
        rw [show n = (n - 1) + 1 by omega, pow_succ]
        exact dvd_mul_left _ _)).elim
  have hbot : B.map f = ⊥ := (Subgroup.card_eq_one).mp hone
  change B ≤ (⊥ : Subgroup Q).comap f
  rw [← map_le_iff_le_comap, hbot]

theorem nPrime_le_kernel_of_two_group {Q : Type v} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (f : G →* Q) : nPrime G ≤ nPrime f.ker := by
  obtain ⟨w⟩ := nPrime_spec (X := G)
  exact (w.restrictNormal f.ker (odd_subgroup_le_ker_of_two_group hQ f _ w.odd)).le_nPrime

theorem automorphism_subgroup_nPrime_le
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G))
    (houter : IsPGroup 2 (MulAut.Outer G))
    (A : Subgroup (MulAut G)) (hA : MulAut.innerSubgroup G ≤ A) :
    nPrime A ≤ nPrime G := by
  let q := (QuotientGroup.mk' (MulAut.innerSubgroup G)).comp A.subtype
  let f : G →* q.ker := {
    toFun := fun g => ⟨⟨MulAut.conj g, hA ⟨g, rfl⟩⟩,
      (QuotientGroup.eq_one_iff (N := MulAut.innerSubgroup G) _).mpr ⟨g, rfl⟩⟩
    map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one MulAut.conj
    map_mul' := by intro x y; apply Subtype.ext; apply Subtype.ext; exact map_mul MulAut.conj x y }
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact hinj (congrArg (fun a : q.ker => a.val.val) h)
    · intro a
      obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff
        (N := MulAut.innerSubgroup G) a.val.val).mp a.property
      exact ⟨g, Subtype.ext (Subtype.ext hg)⟩
  exact (nPrime_le_kernel_of_two_group houter q).trans
    (nPrime_eq_of_mulEquiv (MulEquiv.ofBijective f hf)).ge

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
