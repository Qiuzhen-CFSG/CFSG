module
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupAction.Defs


/-!
# A disjoint conjugate in a small center

A subgroup with a disjoint conjugate in an overgroup of twice its order has
order at most two: multiplication injects the product of the two conjugates
into that overgroup. Applied to a centralizer decomposition, this forces each
central factor to have order two. Relative normality then makes the smaller
center central in the larger two-group, so a nontrivial normal subgroup meets
the larger center.

All normalizers are in the original ambient group, with the acting subgroup
specified by containment. The center is the actual ambient image `centerIn`.

Source: the elementary finite-group argument in Aschbacher–Smith, combined
manuscript of 1 March 2004, proof of Lemma 16.5.7, printed p.1198.
-/

public section

open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

theorem centralizes_of_normalizes_card_two {C A : Subgroup G}
    (hc : Nat.card C = 2) (hn : A ≤ normalizer (C : Set G)) :
    A ≤ centralizer (C : Set G) := by
  obtain ⟨z, _, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : C)).mp hc
  intro a ha x hx
  by_cases hxone : x = 1
  · simp [hxone]
  let xC : C := ⟨x, hx⟩
  let yC : C := ⟨a * x * a⁻¹, (hn ha x).mp hx⟩
  have hyne : yC ≠ 1 := by
    intro hy
    have hy' : a * x * a⁻¹ = 1 := congrArg Subtype.val hy
    apply hxone
    have h := congrArg (fun b : G => a⁻¹ * b * a) hy'
    simpa [mul_assoc] using h
  have heq : yC = xC := (hzuniq yC hyne).trans (hzuniq xC (by
    intro hx'
    exact hxone (congrArg Subtype.val hx'))).symm
  have heq' : a * x * a⁻¹ = x := congrArg Subtype.val heq
  have h := congrArg (fun b : G => b * a) heq'
  simpa [mul_assoc] using h.symm

theorem centerIn_map_equiv (S : Subgroup G) (e : G ≃* G) :
    (centerIn S).map e.toMonoidHom = centerIn (S.map e.toMonoidHom) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    simpa using congrArg e (hx.2 y hy)
  · intro x hx
    refine ⟨e.symm x, ⟨?_, ?_⟩, e.apply_symm_apply x⟩
    · obtain ⟨y, hy, he⟩ := hx.1
      change e.symm x ∈ S
      rw [← he]
      simpa using hy
    · intro y hy
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using hx.2 (e y) ⟨y, hy, rfl⟩

theorem normalizes_centerIn {S A : Subgroup G}
    (hn : A ≤ normalizer (S : Set G)) :
    A ≤ normalizer (centerIn S : Set G) := by
  intro a ha
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (centerIn S).map (MulAut.conj a).toMonoidHom = centerIn S
  rw [centerIn_map_equiv]
  have he : S.map (MulAut.conj a).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp (hn ha)
  rw [he]

theorem centerIn_centralizes_of_card_two {S A : Subgroup G}
    (hc : Nat.card (centerIn S) = 2) (hn : A ≤ normalizer (S : Set G)) :
    centerIn S ≤ centralizer (A : Set G) :=
  le_centralizer_iff.mp (centralizes_of_normalizes_card_two hc (normalizes_centerIn hn))

/-- The centralizer formula splits the center of each intermediate subgroup. -/
theorem centerIn_eq_sup_of_centralizer {P S A C : Subgroup G}
    (hSP : S ≤ P) (hAS : A ≤ S) (hCS : C ≤ S)
    (hz : centerIn A ≤ centralizer (P : Set G))
    (hcent : P ⊓ centralizer (A : Set G) = C ⊔ centerIn A) :
    centerIn S = centerIn A ⊔ (C ⊓ centralizer (S : Set G)) := by
  have hzS : centerIn A ≤ centerIn S :=
    le_inf (inf_le_left.trans hAS) (hz.trans (centralizer_le hSP))
  have hZS : centerIn S ≤ C ⊔ centerIn A := by
    rw [← hcent]
    exact le_inf (inf_le_left.trans hSP)
      (inf_le_right.trans (centralizer_le hAS))
  have hn : centerIn A ≤ normalizer (C : Set G) :=
    (hz.trans (centralizer_le (hCS.trans hSP))).trans (centralizer_le_normalizer _)
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ (C : Set G) * (centerIn A : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left C (centerIn A) hn]
      exact hZS hx
    obtain ⟨c, hc, a, ha, rfl⟩ := hxprod
    have hcZ : c ∈ centralizer (S : Set G) := by
      have hh := (centralizer (S : Set G)).mul_mem hx.2
        ((centralizer (S : Set G)).inv_mem (hzS ha).2)
      simpa only [mul_inv_cancel_right] using hh
    exact mul_mem (mem_sup_right ⟨hc, hcZ⟩) (mem_sup_left ha)
  · exact sup_le hzS (le_inf (inf_le_left.trans hCS) inf_le_right)

variable [Finite G]

theorem card_le_two_of_disjoint_conjugate {C Z : Subgroup G} {g : G}
    (hCZ : C ≤ Z) (hg : g ∈ normalizer (Z : Set G))
    (hdis : Disjoint C (C.conjBy g)) (hc : Nat.card Z = 2 * Nat.card C) :
    Nat.card C ≤ 2 := by
  have hconjZ : C.conjBy g ≤ Z := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hCZ
    have he : Z.map (MulAut.conj g).toMonoidHom = Z :=
      mem_normalizer_iff_map_conj_eq.mp hg
    rwa [he] at hh
  let m : C × C.conjBy g → Z := fun x =>
    ⟨x.1 * x.2, Z.mul_mem (hCZ x.1.property) (hconjZ x.2.property)⟩
  have hi : Function.Injective m := fun _ _ hh =>
    mul_injective_of_disjoint hdis (congrArg Subtype.val hh)
  have hbound := Nat.card_le_card_of_injective m hi
  rw [Nat.card_prod, show Nat.card (C.conjBy g) = Nat.card C from
    card_map_of_injective (MulAut.conj g).injective, hc] at hbound
  have hpos : 0 < Nat.card C := Nat.card_pos
  nlinarith

/-- A nontrivial relatively normal subgroup meets the center of a finite
p-group. Both groups remain subgroups of the original ambient group. -/
theorem inf_centerIn_ne_bot {p : ℕ} [Fact p.Prime] {R S : Subgroup G}
    (hp : IsPGroup p S) (hR : R ≠ ⊥) (hRS : R ≤ S)
    (hn : S ≤ normalizer (R : Set G)) : R ⊓ centerIn S ≠ ⊥ := by
  let N := R.subgroupOf S
  have hN : N ≠ ⊥ := by
    intro hh
    apply hR
    change R.subgroupOf S = ⊥ at hh
    rw [← map_subgroupOf_eq_of_le hRS, hh, map_bot]
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  let : Nontrivial N := (nontrivial_iff_ne_bot N).mpr hN
  let : Fact (IsPGroup p S) := ⟨hp⟩
  obtain ⟨x, hx1, hxZ⟩ := exists_nontrivial_center_mem_normal N (p := p)
  intro he
  have hx : ((x : S) : G) ∈ R ⊓ centerIn S := by
    refine ⟨x.property, ?_⟩
    rw [centerIn_eq_map_center]
    exact ⟨x, hxZ, rfl⟩
  rw [he, mem_bot] at hx
  exact hx1 (Subtype.ext (Subtype.ext hx))

/-- Centrality of the smaller center upgrades its nontrivial intersection
to the center of the larger two-group. -/
theorem inf_centerIn_ne_bot_of_centerIn_le {p : ℕ} [Fact p.Prime]
    {R S P : Subgroup G} (hp : IsPGroup p S) (hR : R ≠ ⊥)
    (hRS : R ≤ S) (hn : S ≤ normalizer (R : Set G))
    (hSP : S ≤ P) (hz : centerIn S ≤ centralizer (P : Set G)) :
    R ⊓ centerIn P ≠ ⊥ := by
  have hne := inf_centerIn_ne_bot hp hR hRS hn
  intro he
  apply hne
  exact eq_bot_iff.mpr (he ▸ inf_le_inf_left R
    (le_inf (inf_le_left.trans hSP) hz))

/-- The order-two and centrality steps for a center with a disjoint
conjugate of one of its direct factors. -/
theorem centerIn_rank_two_of_disjoint_conjugate
    {P S A C : Subgroup G} {g : G}
    (hp : IsPGroup 2 P) (hSP : S ≤ P) (hAS : A ≤ S) (hCS : C ≤ S)
    (hSn : P ≤ normalizer (S : Set G))
    (hAn : P ≤ normalizer (A : Set G))
    (hCn : P ≤ normalizer (C : Set G)) (hCne : C ≠ ⊥)
    (hAC : Disjoint A C) (hZA : Nat.card (centerIn A) = 2)
    (hcent : P ⊓ centralizer (A : Set G) = C ⊔ centerIn A)
    (hg : g ∈ normalizer (S : Set G)) (hdis : Disjoint C (C.conjBy g)) :
    centerIn S = centerIn A ⊔ (C ⊓ centralizer (S : Set G)) ∧
    Nat.card ↥(C ⊓ centralizer (S : Set G)) = 2 ∧
    centerIn S ≤ centralizer (P : Set G) := by
  let ZC := C ⊓ centralizer (S : Set G)
  have hz := centerIn_centralizes_of_card_two hZA hAn
  have hsplit := centerIn_eq_sup_of_centralizer hSP hAS hCS hz hcent
  have hZCS : ZC ≤ centerIn S := le_inf (inf_le_left.trans hCS) inf_le_right
  have hZCn : P ≤ normalizer (ZC : Set G) := by
    have he : ZC = C ⊓ centerIn S := by
      ext x
      exact ⟨fun hx => ⟨hx.1, hCS hx.1, hx.2⟩, fun hx => ⟨hx.1, hx.2.2⟩⟩
    rw [he]
    exact (le_inf hCn (normalizes_centerIn hSn)).trans inf_normalizer_le_normalizer_inf
  have hZCne : ZC ≠ ⊥ := by
    have hne := inf_centerIn_ne_bot hp hCne (hCS.trans hSP) hCn
    intro he
    apply hne
    apply eq_bot_iff.mpr
    rw [← he]
    exact le_inf inf_le_left (inf_le_right.trans
      (inf_le_right.trans (centralizer_le hSP)))
  have hdis' : Disjoint ZC (ZC.conjBy g) :=
    hdis.mono inf_le_left (map_mono inf_le_left)
  have hZSn : g ∈ normalizer (centerIn S : Set G) :=
    normalizes_centerIn (S := S) (A := normalizer (S : Set G)) le_rfl hg
  have hcard : Nat.card (centerIn S) = 2 * Nat.card ZC := by
    rw [hsplit, card_sup_eq_mul_of_normalizes_of_disjoint]
    · rw [hZA]
    · exact (inf_le_left.trans ((le_centralizer_iff.mp hz).trans' (hCS.trans hSP))).trans
        (centralizer_le_normalizer _)
    · exact hAC.mono inf_le_left inf_le_left
  have hle := card_le_two_of_disjoint_conjugate hZCS hZSn hdis' hcard
  have hpos : 0 < Nat.card ZC := Nat.card_pos
  have hne1 : Nat.card ZC ≠ 1 := fun hh => hZCne (ZC.eq_bot_iff_card.mpr hh)
  have htwo : Nat.card ZC = 2 := by omega
  refine ⟨hsplit, htwo, ?_⟩
  rw [hsplit]
  exact sup_le hz (le_centralizer_iff.mp (centralizes_of_normalizes_card_two htwo hZCn))

end Subgroup
