module
public import Theory.GroupTheory.PCoreQuotientInnerAction
public import Theory.SpecificGroups.AlternatingSeven.CentralCoverFixer
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple

/-!
# Marked parabolics in a central three-cover of A₇

An order-168 two-core quotient in a subgroup of the order-7560 cover has
trivial two-core. Every subgroup of order 504 contains the cubic center:
otherwise its image in A₇ has index five, contradicting the faithful coset
action. Finally, inner action on a nonsolvable seven-divisible subgroup
fixes the cover's center, by the pointwise automorphism-fixer theorem.

The source point-component application retains its original parabolic and
quotient maps in NaturalSource.Local.Components.PointCoverExclusion.
Source: Aschbacher--Smith 12.5.3, printed pp.817--818, and GLS III 5.2.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace AlternatingSeven.CentralCoverParabolic

-- The odd index 45 above the binary-three section kills its two-core.
theorem twoCore_eq_bot_of_binary_three_section {X : Type*} [Group X] [Finite X]
    (hd : Nat.card X ∣ 7560)
    (hq : Nat.card (X ⧸ pCore 2 X) = 168) : pCore 2 X = ⊥ ∧ Nat.card X = 168 := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := X)).exists_card_eq
  have hb := card_eq_card_quotient_mul_card_subgroup (pCore 2 X)
  rw [hq,hn] at hb
  rw [hb] at hd
  have hd' : 2^n ∣ 45 := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 168)).mp hd
  have hn0 : n = 0 := by
    by_contra hh
    have he : 2 ∣ 45 := (dvd_pow_self 2 (by omega : n ≠ 0)).trans hd'
    norm_num at he
  subst n
  exact ⟨Subgroup.card_eq_one.mp (by simpa using hn),by simpa using hb⟩

-- A subgroup of order 504 in the triple cover must contain its center.
theorem center_le_of_card_504 {C : Type*} [Group C] [Finite C]
    (e : (C ⧸ center C) ≃* alternatingGroup (Fin 7))
    (hz : Nat.card (center C) = 3) (J : Subgroup C) (hj : Nat.card J = 504) :
    center C ≤ J := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  have hk : q.ker = center C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hdis : center C ≤ J ∨ Disjoint J (center C) := by
    have hc : Nat.card (J ⊓ center C : Subgroup C) ∣ 3 := hz ▸ card_dvd_of_le (show J ⊓ center C ≤ center C from inf_le_right)
    rcases (Nat.dvd_prime Nat.prime_three).mp hc with h1 | h3
    · exact .inr (disjoint_iff.mpr (Subgroup.card_eq_one.mp h1))
    · exact .inl ((eq_of_le_of_card_ge (show J ⊓ center C ≤ center C from inf_le_right)
        (by rw [hz,h3])).symm ▸ inf_le_left)
  rcases hdis with hh | hh
  · exact hh
  have hqi : Function.Injective (q.subgroupMap J) := by
    apply (injective_iff_map_eq_one _).mpr
    intro j hj'
    have hz' : (j : C) ∈ center C := hk ▸ congrArg Subtype.val hj'
    have he := (show J ⊓ center C = ⊥ from disjoint_iff.mp hh).le ⟨j.property,hz'⟩
    exact Subtype.ext he
  have hcard : Nat.card (J.map q) = 504 := by
    rw [←Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap J)
      ⟨hqi,q.subgroupMap_surjective J⟩).toEquiv,hj]
  have hi : (J.map q).index = 5 := by
    have he := (J.map q).card_mul_index
    rw [hcard,nat_card_alternatingGroup,Nat.card_fin] at he
    norm_num [Nat.factorial] at he
    omega
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have ht := Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt (J.map q) (by
    rw [hi,nat_card_alternatingGroup,Nat.card_fin]; norm_num [Nat.factorial])
  rw [ht,index_top] at hi
  omega

-- Inner action on a seven-divisible perfect subgroup fixes the center of the cover.
theorem center_fixed_of_inner_on_subgroup {X : Type*} [Group X]
    (A B C : Subgroup X) (hBC : B ≤ C)
    (f : PerfectCentralCovering.Cover C (alternatingGroup (Fin 7)))
    (hns : ¬ Group.IsSolvable ((B.subgroupOf C).map f.toMonoidHom))
    (hseven : 7 ∣ Nat.card ((B.subgroupOf C).map f.toMonoidHom))
    (hn : A ≤ normalizer (C : Set X))
    (hi : ∀ a : A, ∃ b : B, ∀ y : B,
      (a : X) * y * (a : X)⁻¹ = (b : X) * y * (b : X)⁻¹) :
    (center C).map C.subtype ≤ centralizer (A : Set X) := by
  rintro _ ⟨z,hz,rfl⟩ a ha
  obtain ⟨b,hb⟩ := hi ⟨a,ha⟩
  let t : X := (b : X)⁻¹ * a
  have htN : t ∈ normalizer (C : Set X) :=
    mul_mem (inv_mem (C.le_normalizer (hBC b.property))) (hn ha)
  have htB : t ∈ centralizer (B : Set X) := by
    intro y hy
    have he : t * y * t⁻¹ = y := by
      calc
        _ = (b : X)⁻¹ * (a * y * a⁻¹) * b := by dsimp [t]; group
        _ = (b : X)⁻¹ * ((b : X) * y * (b : X)⁻¹) * b := by rw [hb ⟨y,hy⟩]
        _ = y := by group
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have htC := AlternatingSeven.SevenFixer.central_cover_centralizes_of_centralizes_subgroup
    C B hBC f hns hseven t htN htB
  have hbz : Commute (b : X) (z : X) :=
    congrArg Subtype.val (mem_center_iff.mp hz ⟨b,hBC b.property⟩)
  have htz : Commute t (z : X) := (htC z z.property).symm
  change a * (z : X) = (z : X) * a
  simpa only [t,mul_inv_cancel_left] using (hbz.mul_left htz).eq


end AlternatingSeven.CentralCoverParabolic
