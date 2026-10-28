module
public import Theory.GroupTheory.UniqueFixedCosetCommutingProducts

/-!
# The cardinality obstruction in the AS91 fixed-coset argument

A single conjugacy orbit on the nonidentity elements of a normal subgroup
forces its size to divide the acting group order. Thus a normal binary
subgroup with an incompatible cardinality has two distinct local classes.
The commuting-product fixed-coset criterion then excludes a proper coset
stabilizer. The quotient form retains the entire specified normal kernel.

The application is the actual E/U of order 512 in the pair-plane normalizer.
Source: Aschbacher–Segev, Invent. Math. 105 (1991), proof of (6.3), p.602.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem normal_subgroup_nonidentity_card_dvd (A : Subgroup H) [A.Normal]
    (a : A) (ha : a ≠ 1)
    (hc : ∀ b : A, b ≠ 1 → IsConj (a : H) (b : H)) :
    Nat.card A - 1 ∣ Nat.card H := by
  have horbit : MulAction.orbit (ConjAct H) (a : H) = (A : Set H) \ {1} := by
    ext b
    rw [ConjAct.mem_orbit_conjAct]
    constructor
    · intro hb
      obtain ⟨g,hg⟩ := isConj_iff.mp hb.symm
      refine ⟨hg ▸ Subgroup.Normal.conj_mem (inferInstance : A.Normal) _ a.property g, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro h1
      have hh := (MulAut.conj g).map_eq_one_iff.mp (hg.trans h1)
      exact ha (Subtype.ext hh)
    · rintro ⟨hb,hb1⟩
      exact (hc ⟨b,hb⟩ (fun he => hb1 (congrArg Subtype.val he))).symm
  have hd : Nat.card (MulAction.orbit (ConjAct H) (a : H)) ∣ Nat.card H := by
    have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct H) (a : H))
    rw [Nat.card_prod] at he
    exact ⟨_,he.symm⟩
  rw [horbit] at hd
  have hn : Nat.card ↥((A : Set H) \ {1}) = Nat.card A - 1 := by
    change ((A : Set H) \ {1}).ncard = (A : Set H).ncard - 1
    exact Set.ncard_sdiff_singleton_of_mem A.one_mem
  rwa [hn] at hd

theorem normal_subgroup_two_classes (A : Subgroup H) [A.Normal]
    (hcard : 1 < Nat.card A) (hdiv : ¬ Nat.card A - 1 ∣ Nat.card H) :
    ∃ a b : A, a ≠ 1 ∧ b ≠ 1 ∧ ¬ IsConj (a : H) (b : H) := by
  have : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨a,ha⟩ := exists_ne (1 : A)
  by_contra hh
  apply hdiv
  apply normal_subgroup_nonidentity_card_dvd A a ha
  intro b hb
  by_contra hc
  exact hh ⟨a,b,ha,hb,hc⟩


/-- The standard fixed-coset argument after dividing by its actual kernel. -/
theorem fixed_coset_quotient_eq_top (M B U : Subgroup H) [U.Normal]
    (hUB : U ≤ B) (hBM : B ≤ M) (hBN : (B.subgroupOf M).Normal)
    (hB : ∀ b ∈ B, b ^ 2 = 1)
    (hlarge : 1 < Nat.card B / Nat.card U)
    (hdiv : ¬ (Nat.card B / Nat.card U - 1) ∣ Nat.card M)
    (hfix : ∀ b : H, b ∈ B → b ∉ U → ∃! q : H ⧸ M, b • q = q) :
    M = ⊤ := by
  let f := QuotientGroup.mk' U
  let MB := M.map f
  let BB := B.map f
  have hBB : BB ≤ MB := map_mono hBM
  let A := BB.subgroupOf MB
  let : A.Normal := by
    apply (normal_subgroupOf_iff hBB).mpr
    rintro x g ⟨b,hb,rfl⟩ ⟨m,hm,rfl⟩
    rw [←map_inv,←map_mul,←map_mul]
    exact ⟨m*b*m⁻¹,(normal_subgroupOf_iff hBM).mp hBN b m hb hm,rfl⟩
  have hcard : Nat.card A = Nat.card B / Nat.card U := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBB).toEquiv]
    change Nat.card (B.map f) = _
    rw [←relIndex_ker,QuotientGroup.ker_mk']
    have he := (U.subgroupOf B).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hUB).toEquiv] at he
    change Nat.card U * U.relIndex B = Nat.card B at he
    rw [←he,Nat.mul_comm,Nat.mul_div_cancel _ Nat.card_pos]
  obtain ⟨a,b,ha,hb,hne⟩ := normal_subgroup_two_classes A (by rwa [hcard]) (by
    rw [hcard]
    intro hd
    exact hdiv (hd.trans (M.card_map_dvd f)))
  refine UniqueFixedCoset.eq_top_of_normal_binary_image M f
    (QuotientGroup.mk'_surjective U) (by rw [QuotientGroup.ker_mk']; exact hUB.trans hBM)
    A ?_ a b ha hb hne ?_
  · intro x
    obtain ⟨v,hv,he⟩ := x.property
    apply Subtype.ext
    apply Subtype.ext
    change (((x : MB) : H ⧸ U)) ^ 2 = 1
    change f v = ((x : MB) : H ⧸ U) at he
    rw [←he,←map_pow,hB v hv,map_one]
  · intro x hx
    obtain ⟨v,hv,he⟩ := x.property
    refine ⟨⟨v,hBM hv⟩,he, hfix v hv ?_⟩
    intro hvU
    apply hx
    apply Subtype.ext
    apply Subtype.ext
    exact he.symm.trans ((QuotientGroup.eq_one_iff v).mpr hvU)


end Theory.GroupTheory.Recognition.JankoFour.SourceFusion
