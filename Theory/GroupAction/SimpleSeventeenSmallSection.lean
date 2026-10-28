module

public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.PGroup

/-!
# Small two-sections below a simple quotient divisible by seventeen

A two-group of order at most 64 has no automorphism of order 17: the powers
of two through 64 have distinct residues modulo 17, so a 17-group of
automorphisms fixes every element. If a finite group has a simple quotient
whose order is divisible by 17 and a two-group kernel, every image of order
prime to 17 is a two-group. Its two-residual therefore acts trivially on
all normal two-sections of order at most 64 in the kernel.

The application is the small normal-section step of MS93 (5.7), printed
p.919, for Sp4(4), of order 979200. No splitting of the section is used.
-/

public section
open Subgroup

/-- Automorphisms of a two-group of order at most 64 have order prime to 17. -/
theorem MulAut.not_seventeen_dvd_card_of_twoGroup_card_le_sixtyFour
    {V : Type*} [Group V] [Finite V] (hV : IsPGroup 2 V) (hcard : Nat.card V ≤ 64) :
    ¬ 17 ∣ Nat.card (MulAut V) := by
  let : Fact (Nat.Prime 17) := ⟨by decide⟩
  intro hdiv
  obtain ⟨n,hn⟩ := hV.exists_card_eq
  have hnle : n ≤ 6 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hn] using hcard
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 17 hdiv
  let P := zpowers a
  have hP : Nat.card P = 17 := by rw [Nat.card_zpowers,ha]
  have hp : IsPGroup 17 P := IsPGroup.of_card (n := 1) (by simpa using hP)
  let F := FixedPoints.subgroup P V
  have hmod := hp.card_modEq_card_fixedPoints V
  change Nat.card V % 17 = Nat.card F % 17 at hmod
  have hFdiv : Nat.card F ∣ 2^n := hn ▸ F.card_subgroup_dvd_card
  obtain ⟨k,hk,hFcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hFdiv
  have heq : Nat.card F = Nat.card V := by
    rw [hn,hFcard] at hmod ⊢
    interval_cases n <;> interval_cases k <;> norm_num at *
  have htop := F.eq_top_of_card_eq heq
  have haone : a = 1 := by
    apply MulEquiv.ext
    intro x
    exact (show x ∈ F from htop ▸ mem_top x) ⟨a,mem_zpowers a⟩
  rw [haone,orderOf_one] at ha
  norm_num at ha

/-- A simple quotient with an obstructing prime forces every image avoiding
that prime to lie entirely in the image of the two-group kernel. -/
theorem MonoidHom.isPGroup_range_of_simple_quotient
    {M S A : Type*} [Group M] [Finite M] [Group S] [Finite S]
    [IsSimpleGroup S] [Group A] [Finite A]
    (q : M →* S) (hq : Function.Surjective q) (hker : IsPGroup 2 q.ker)
    (f : M →* A) (r : ℕ) (hS : r ∣ Nat.card S) (hA : ¬ r ∣ Nat.card A) :
    IsPGroup 2 f.range := by
  let B := f.range
  let π := QuotientGroup.mk' (pCore 2 B)
  let g := π.comp f.rangeRestrict
  let N := q.ker.map f.rangeRestrict
  let : N.Normal := Normal.map inferInstance f.rangeRestrict f.rangeRestrict_surjective
  have hN : N ≤ pCore 2 B := le_sSup ⟨inferInstance,hker.map f.rangeRestrict⟩
  have hk : q.ker ≤ g.ker := by
    intro x hx
    exact (QuotientGroup.eq_one_iff _).mpr (hN (mem_map_of_mem f.rangeRestrict hx))
  let t := q.liftOfSurjective hq ⟨g,hk⟩
  have ht (x : M) : t (q x) = g x := by simp [t,MonoidHom.liftOfSurjective]
  have htonto : Function.Surjective t := by
    intro x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) x
    obtain ⟨z,rfl⟩ := f.rangeRestrict_surjective y
    exact ⟨q z,ht z⟩
  have hn : t.ker ≠ ⊥ := by
    intro hz
    have hd := card_dvd_of_injective t ((MonoidHom.ker_eq_bot_iff t).mp hz)
    exact hA (hS.trans (hd.trans
      ((card_quotient_dvd_card _).trans f.range.card_subgroup_dvd_card)))
  have htop : t.ker = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal t.ker inferInstance).resolve_left hn
  have hcard : Nat.card (B ⧸ pCore 2 B) = 1 := by
    have hi := index_ker t
    rw [htop,index_top,t.range_eq_top_of_surjective htonto,card_top] at hi
    exact hi.symm
  have hp : IsPGroup 2 (B ⧸ pCore 2 B) :=
    IsPGroup.of_card (n := 0) (by simpa using hcard)
  have hpker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hh := (hp.to_subgroup ⊤).comap_of_ker_isPGroup π hpker
  rw [comap_top] at hh
  exact hh.of_equiv (topEquiv : (⊤ : Subgroup B) ≃* B)

open scoped commutatorElement

/-- The actual residual centralizes the original small normal quotient,
including arbitrary central attachments and nonsplit two-group sections. -/
theorem Subgroup.commutator_pResidual_le_of_simple_seventeen_small_section
    {M S : Type*} [Group M] [Finite M] [Group S] [Finite S] [IsSimpleGroup S]
    (q : M →* S) (hq : Function.Surjective q) (hker : IsPGroup 2 q.ker)
    (hS : 17 ∣ Nat.card S) (D Z : Subgroup M) [D.Normal] [Z.Normal]
    (hD : D ≤ q.ker) (hcard : Z.relIndex D ≤ 64) :
    ⁅D,pResidual 2 M⁆ ≤ Z := by
  let V := D ⧸ Z.subgroupOf D
  have hV : IsPGroup 2 V := (hker.to_le hD).to_quotient _
  obtain ⟨a,ha⟩ := exists_quotient_conjugation_action (⊤ : Subgroup M) D Z
    (le_normalizer_of_normal) (le_normalizer_of_normal) inferInstance
  let f := a.comp (topEquiv : (⊤ : Subgroup M) ≃* M).symm.toMonoidHom
  have hf : IsPGroup 2 f.range := MonoidHom.isPGroup_range_of_simple_quotient q hq hker
    f 17 hS (MulAut.not_seventeen_dvd_card_of_twoGroup_card_le_sixtyFour hV hcard)
  have hk := pResidual_le_ker_of_isPGroup 2 f.rangeRestrict hf
  rw [MonoidHom.ker_rangeRestrict] at hk
  rw [commutator_comm]
  apply commutator_le.mpr
  intro m hm d hd
  have htriv : a ⟨m,mem_top _⟩ = 1 := hk hm
  have hfix := ha ⟨m,mem_top _⟩ ⟨d,hd⟩
  rw [htriv] at hfix
  have hmember := QuotientGroup.eq_iff_div_mem.mp hfix.symm
  change m*d*m⁻¹/d ∈ Z at hmember
  simpa only [div_eq_mul_inv,commutatorElement_def] using hmember
