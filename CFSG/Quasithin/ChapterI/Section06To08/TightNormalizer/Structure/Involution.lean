module

public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Structure.Reduction
public import Theory.GroupTheory.InvolutionCentralizerFourRecognition
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.SemidihedralStandardModel

/-!
# The involution branch of the tightly embedded normalizer argument

For the genuine I.7.7 setup with `S₁ < S₀`, an equivalence `S₁ ≃* R`, and
`|R| = 2`, a generator of `R` is a noncentral involution in `S`. Its centralizer
is the relative normalizer `S₁ × R` and has order four. The involution-centralizer
recognition theorem therefore gives a dihedral model with a valid two-power
parameter, or the full semidihedral presentation. The latter determines an
equivalence with the explicit standard semidirect product
`C_(2^(n-1)) ⋊ C₂`, for `n ≥ 4`, whose involution acts by exponent `2^(n-2)-1`.

Relative normality is proved independently: the nontrivial normal subgroup
`S₀` of the two-group `S` contains a central subgroup of order two. That subgroup
lies in `S₁`, which has order two, so `S₁` is central in `S` and normal in `S₀`.
Abelianness of `R` follows from its order and is not an additional hypothesis.

`involutionBranch` combines the genuine model alternative and relative normality
for the order-two branch of I.7.7(5a,6). The comparison equivalence `S₁ ≃* R`
is the explicit input supplied by the separate proof of I.7.7(2).

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, I.7.7(5a,6), printed p.427 (PDF p.438).
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section06To08.TightNormalizerSetup
variable {G : Type*} [Group G] [Finite G]
variable {K : Subgroup G} {g : G} {R S : Subgroup G}
variable (h : TightNormalizerSetup K g R S)
include h

/-- The order-two normalizer factor lies in the center of the actual group `S`. -/
theorem involution_intersection_le_center
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g)
    (hR : Nat.card R = 2) :
    (((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)).subgroupOf S) ≤ center S := by
  let S0 := S ⊓ conjSubgroup K g
  let S1 := S0 ⊓ normalizer (R : Set G)
  have h1S : S1 ≤ S := inf_le_left.trans inf_le_left
  have hc1 : Nat.card (S1.subgroupOf S) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe h1S).toEquiv,
      Nat.card_congr e.toEquiv, hR]
  let : (S0.subgroupOf S).Normal := h.intersection_normal
  let : Fact (IsPGroup 2 S) := ⟨h.hSp⟩
  have h0ne : S0 ≠ ⊥ := ne_bot_of_gt (bot_le.trans_lt hp)
  let : Nontrivial S0 := (nontrivial_iff_ne_bot _).mpr h0ne
  have h0card : Nat.card (S0.subgroupOf S) = Nat.card S0 :=
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : S0 ≤ S)).toEquiv
  have h0nt : Nontrivial (S0.subgroupOf S) :=
    Finite.one_lt_card_iff_nontrivial.mp (h0card ▸ Finite.one_lt_card)
  obtain ⟨Z, _, hZ0, hcZ, hZ⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) (S0.subgroupOf S) h0nt
  have hZ1 : Z ≤ S1.subgroupOf S := by
    intro z hz
    refine ⟨hZ0 hz, ?_⟩
    apply centralizer_le_normalizer (R : Set G)
    intro r hr
    exact congrArg Subtype.val (mem_center_iff.mp (hZ hz) ⟨r, h.hRS hr⟩)
  have heq : Z = S1.subgroupOf S := eq_of_le_of_card_ge hZ1 (by omega)
  exact heq ▸ hZ

/-- I.7.7(6) in the order-two branch, with normality relative to `S₀`. -/
theorem involution_relativeNormal
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g)
    (hR : Nat.card R = 2) :
    (((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)).subgroupOf
      (S ⊓ conjSubgroup K g)).Normal := by
  have hc := h.involution_intersection_le_center e hp hR
  constructor
  intro a ha b
  change (b : G) * (a : G) * (b : G)⁻¹ ∈
    (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)
  have haS : (a : G) ∈ S := a.property.1
  have hbS : (b : G) ∈ S := b.property.1
  have hab := congrArg Subtype.val
    (mem_center_iff.mp (hc (show (⟨a, haS⟩ : S) ∈ _ from ha)) ⟨b, hbS⟩)
  change (b : G) * (a : G) = (a : G) * (b : G) at hab
  rw [hab, mul_assoc, mul_inv_cancel, mul_one]
  exact ha

/-- A noncentral involution of `S` coming from `R`, with centralizer of order four. -/
theorem involution_centralizer_witness
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g)
    (hR : Nat.card R = 2) :
    ∃ x : S, (x : G) ∈ R ∧ orderOf x = 2 ∧ x ∉ center S ∧
      Nat.card (centralizer ({x} : Set S)) = 4 := by
  let : IsCyclic R := isCyclic_of_prime_card hR
  obtain ⟨r, hr⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := R)
  have hr2 : orderOf r = 2 := hr.trans hR
  have hrne : r ≠ 1 := by intro he; simp [he] at hr2
  have hall (y : R) : y = 1 ∨ y = r := by
    obtain ⟨t, ht, hu⟩ := (Nat.card_eq_two_iff' (1 : R)).mp hR
    by_cases hy : y = 1
    · exact Or.inl hy
    · exact Or.inr ((hu y hy).trans (hu r hrne).symm)
  let x : S := ⟨r, h.hRS r.property⟩
  have hx2 : orderOf x = 2 := by
    rw [← Subgroup.orderOf_coe, show (x : G) = (r : G) from rfl, Subgroup.orderOf_coe, hr2]
  let N := S ⊓ normalizer (R : Set G)
  let : IsMulCommutative N := h.normalizer_commutative e
  have hC : centralizer ({x} : Set S) = N.subgroupOf S := by
    ext y
    constructor
    · intro hy
      refine ⟨y.property, centralizer_le_normalizer (R : Set G) ?_⟩
      intro z hz
      rcases hall ⟨z, hz⟩ with he | he
      · have he' : z = 1 := congrArg Subtype.val he
        simp [he']
      · have he' : z = (r : G) := congrArg Subtype.val he
        rw [he']
        exact (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy)).symm
    · intro hy
      apply mem_centralizer_singleton_iff.mpr
      apply Subtype.ext
      exact setLike_mul_comm (s := N) hy ⟨h.hRS r.property, R.le_normalizer r.property⟩
  have hxZ : x ∉ center S := by
    intro hxZ
    apply hp.not_ge
    intro y hy
    refine ⟨hy, ?_⟩
    have hyC : (⟨y, hy.1⟩ : S) ∈ centralizer ({x} : Set S) :=
      mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hxZ _)
    exact (hC ▸ hyC).2
  refine ⟨x, r.property, hx2, hxZ, ?_⟩
  obtain ⟨_, _, d, _⟩ := h.directProduct
  rw [hC, Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : N ≤ S)).toEquiv,
    ← Nat.card_congr d.toEquiv, Nat.card_prod, Nat.card_congr e.toEquiv, hR]

/-- Recognition with the valid two-power dihedral parameter, or the full
semidihedral presentation used to identify the standard model. -/
theorem involution_presentation
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g)
    (hR : Nat.card R = 2) :
    (∃ m : ℕ, 2 ≤ m ∧ Nonempty (S ≃* DihedralGroup (2 ^ m))) ∨
      (∃ n : ℕ, 4 ≤ n ∧ Nat.card S = 2 ^ n ∧
        ∃ a b : S, orderOf a = 2 ^ (n - 1) ∧ orderOf b = 2 ∧
          b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1) ∧
          closure ({a, b} : Set S) = ⊤) := by
  obtain ⟨x, _, hx, hxZ, hC⟩ := h.involution_centralizer_witness e hp hR
  have hSc : 4 < Nat.card S := by
    rw [← hC]
    refine lt_of_le_of_ne (card_le_card_group _) ?_
    intro heq
    have htop : centralizer ({x} : Set S) = ⊤ := (card_eq_iff_eq_top _).mp heq
    exact hxZ (centralizer_eq_top_iff_subset.mp htop (Set.mem_singleton x))
  rcases exists_dihedral_or_semidihedral_of_involution_centralizer_card_four
    h.hSp x hx hxZ hC with ⟨m, ⟨f⟩⟩ | hs
  · obtain ⟨k, hkcard⟩ := IsPGroup.iff_card.mp h.hSp
    have hk : 3 ≤ k := by
      by_contra hk
      have hbound : 2 ^ k ≤ 4 := by
        calc
          2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
          _ = 4 := by norm_num
      omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    have hm : m = 2 ^ j := by
      have hc : Nat.card S = 2 * m :=
        (Nat.card_congr f.toEquiv).trans DihedralGroup.nat_card
      rw [pow_succ] at hkcard
      omega
    exact Or.inl ⟨j, by omega, ⟨hm ▸ f⟩⟩
  · exact Or.inr hs

/-- I.7.7(5a,6) in the order-two branch: an actual dihedral or standard
semidihedral model, with valid parameters, and normality of `S₁` in `S₀`.
The comparison equivalence is supplied by I.7.7(2). -/
theorem involutionBranch
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g)
    (hR : Nat.card R = 2) :
    let S0 := S ⊓ conjSubgroup K g
    let S1 := S0 ⊓ normalizer (R : Set G)
    ((∃ m : ℕ, 2 ≤ m ∧ Nonempty (S ≃* DihedralGroup (2 ^ m))) ∨
      (∃ (n : ℕ) (hn : 4 ≤ n), Nonempty (S ≃* Semidihedral.StandardModel n hn))) ∧
      (S1.subgroupOf S0).Normal := by
  refine ⟨?_, h.involution_relativeNormal e hp hR⟩
  rcases h.involution_presentation e hp hR with hd | ⟨n, hn, hc, a, b, ha, hb, hab, hgen⟩
  · exact Or.inl hd
  · exact Or.inr ⟨n, hn,
      Semidihedral.standardModel_equiv_of_presentation hn a b ha hb hab hgen hc⟩

end CFSG.Quasithin.ChapterI.Section06To08.TightNormalizerSetup
