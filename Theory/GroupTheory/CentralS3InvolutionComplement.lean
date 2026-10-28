module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic

/-!
# Splitting a small central extension of S3

Let a finite group map onto S3 with central kernel of order at most two.
An involution outside that kernel guarantees a complement to the kernel.
The outside-involution hypothesis is essential: a central extension need
not otherwise split.

The public Sylow lemma applies to any central subgroup of order at most
two and index six, independently of a chosen quotient map. A Sylow three
subgroup has order three. Multiplication by the central
kernel injects into its normalizer, so there are at most two Sylow three
subgroups. Sylow's congruence gives uniqueness and hence normality. This
normal subgroup and the given involution generate a subgroup of order six.
Its image contains subgroups of orders three and two, so maps bijectively
onto S3. It is consequently disjoint from, and complementary to, the kernel.

This is the central-extension step in the terminal group identification
of Stellmacher (8.2), journal p.38, in
`refs/latex/stellmacher-n-group.tex`. The intended application is the
quotient by the normal elementary subgroup of order four.
-/

open scoped Pointwise

/-- A central subgroup of order at most two and index six forces the Sylow three
subgroups to have order three and be normal. -/
public theorem central_small_sylow_three_normal
    {G : Type*} [Group G] [Finite G]
    (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G)
    (hZcard : Nat.card Z ≤ 2) (hGcard : Nat.card G = 6 * Nat.card Z)
    (P : Sylow 3 G) : Nat.card P = 3 ∧ (P : Subgroup G).Normal := by
  classical
  have hzpos : 0 < Nat.card Z := Nat.card_pos
  have hzcases : Nat.card Z = 1 ∨ Nat.card Z = 2 := by omega
  have hPcard : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, hGcard]
    have hf6 : Nat.factorization 6 3 = 1 := by
      change Nat.factorization (2 * 3) 3 = 1
      rw [Nat.factorization_mul (by decide) (by decide)]
      norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
    rcases hzcases with hz | hz
    · simp [hz, hf6]
    · rw [hz, Nat.factorization_mul (by decide) (by decide)]
      norm_num [hf6, Nat.prime_two.factorization]
  have hdis : Disjoint Z (P : Subgroup G) :=
    Subgroup.disjoint_of_coprime_natCard (by
      rw [hPcard]
      rcases hzcases with hz | hz <;> norm_num [hz])
  let N := Subgroup.normalizer (P : Set G)
  have hZN : Z ≤ N := hZ.trans ((Subgroup.center_le_centralizer _).trans
    (Subgroup.centralizer_le_normalizer _))
  let m : Z × P → N := fun x =>
    ⟨x.1 * x.2, N.mul_mem (hZN x.1.property) (Subgroup.le_normalizer x.2.property)⟩
  have hm : Function.Injective m := fun x y hxy =>
    Subgroup.mul_injective_of_disjoint hdis (congrArg Subtype.val hxy)
  have hNcard := Nat.card_le_card_of_injective m hm
  rw [Nat.card_prod, hPcard] at hNcard
  have hNindex := N.card_mul_index
  rw [hGcard] at hNindex
  have hnle : Nat.card (Sylow 3 G) ≤ 2 := by
    rw [Sylow.card_eq_index_normalizer P]
    change N.index ≤ 2
    nlinarith
  have hnmod := card_sylow_modEq_one 3 G
  have hnone : Nat.card (Sylow 3 G) = 1 := by
    change Nat.card (Sylow 3 G) % 3 = 1 % 3 at hnmod
    omega
  let : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp hnone).1
  exact ⟨hPcard, P.normal_of_subsingleton⟩

private theorem card_sup_three_two
    {G : Type*} [Group G] [Finite G]
    (P T : Subgroup G) [P.Normal]
    (hP : Nat.card P = 3) (hT : Nat.card T = 2) :
    Nat.card (P ⊔ T : Subgroup G) = 6 := by
  let B := P ⊔ T
  let m : P × T → B := fun x => ⟨x.1 * x.2,
    B.mul_mem ((show P ≤ B from le_sup_left) x.1.property)
      ((show T ≤ B from le_sup_right) x.2.property)⟩
  have hm : Function.Surjective m := by
    intro x
    obtain ⟨p, hp, t, ht, hpt⟩ := Subgroup.mem_sup_of_normal_left.mp x.property
    exact ⟨(⟨p, hp⟩, ⟨t, ht⟩), Subtype.ext hpt⟩
  have hle := Nat.card_le_card_of_surjective m hm
  rw [Nat.card_prod, hP, hT] at hle
  have hpdiv : 3 ∣ Nat.card B := hP ▸ Subgroup.card_dvd_of_le (show P ≤ B from le_sup_left)
  have htdiv : 2 ∣ Nat.card B := hT ▸ Subgroup.card_dvd_of_le (show T ≤ B from le_sup_right)
  have hdiv : 6 ∣ Nat.card B := (show Nat.Coprime 3 2 by decide).mul_dvd_of_dvd_of_dvd hpdiv htdiv
  have hpos : 0 < Nat.card B := Nat.card_pos
  have := Nat.le_of_dvd hpos hdiv
  change Nat.card B = 6
  omega

public theorem exists_complement_of_central_s3_quotient_involution
    {G : Type*} [Group G] [Finite G]
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G)
    (hZcard : Nat.card Z ≤ 2)
    (f : G →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hker : f.ker = Z) (t : G) (ht : t ∉ Z) (ht2 : t ^ 2 = 1) :
    ∃ B : Subgroup G, Z.IsComplement' B := by
  classical
  have hS3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hGcard : Nat.card G = 6 * Nat.card Z := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv, hker, hS3]
  let P : Sylow 3 G := Classical.choice inferInstance
  obtain ⟨hPcard, hPnormal⟩ := central_small_sylow_three_normal Z hZ hZcard hGcard P
  let : (P : Subgroup G).Normal := hPnormal
  let T := Subgroup.zpowers t
  have htne : t ≠ 1 := fun h => ht (h.symm ▸ Z.one_mem)
  have hTcard : Nat.card T = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ht2 htne
  let B : Subgroup G := (P : Subgroup G) ⊔ T
  have hBcard :=
    @card_sup_three_two G _ _ (P : Subgroup G) T hPnormal hPcard hTcard
  have hdis : Disjoint Z (P : Subgroup G) :=
    Subgroup.disjoint_of_coprime_natCard (by
      rw [show Nat.card (P : Subgroup G) = 3 from hPcard]
      have hzpos : 0 < Nat.card Z := Nat.card_pos
      interval_cases hz : Nat.card Z <;> norm_num)
  have hPinj : Function.Injective (f.domRestrict (P : Subgroup G)) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro p hp
    have hpZ : (p : G) ∈ Z := hker ▸ (MonoidHom.mem_ker.mpr hp)
    have hpone : (p : G) = 1 := (disjoint_iff_inf_le.mp hdis) ⟨hpZ, p.property⟩
    exact Subtype.ext hpone
  have hPmapcard : Nat.card ((P : Subgroup G).map f) = 3 := by
    rw [← MonoidHom.domRestrict_range]
    exact (Nat.card_congr (MonoidHom.ofInjective hPinj).toEquiv).symm.trans hPcard
  have hftne : f t ≠ 1 := fun h => ht (hker ▸ (MonoidHom.mem_ker.mpr h))
  have hTmapcard : Nat.card (T.map f) = 2 := by
    change Nat.card ((Subgroup.zpowers t).map f) = 2
    rw [MonoidHom.map_zpowers, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [← map_pow, ht2, map_one]) hftne
  have hPdiv : 3 ∣ Nat.card (B.map f) := by
    have hd := Subgroup.card_dvd_of_le (Subgroup.map_mono
      (f := f) (show (P : Subgroup G) ≤ B from le_sup_left))
    rwa [hPmapcard] at hd
  have hTdiv : 2 ∣ Nat.card (B.map f) := by
    have hd := Subgroup.card_dvd_of_le (Subgroup.map_mono
      (f := f) (show T ≤ B from le_sup_right))
    rwa [hTmapcard] at hd
  have hBmapcard : Nat.card (B.map f) = 6 := by
    have hdiv : 6 ∣ Nat.card (B.map f) :=
      (show Nat.Coprime 3 2 by decide).mul_dvd_of_dvd_of_dvd hPdiv hTdiv
    have hle : Nat.card (B.map f) ≤ 6 := by
      rw [← hS3]
      exact Nat.card_le_card_of_injective _ (B.map f).subtype_injective
    have hpos : 0 < Nat.card (B.map f) := Nat.card_pos
    exact le_antisymm hle (Nat.le_of_dvd hpos hdiv)
  let fb := (f.domRestrict B).rangeRestrict
  have hfb : Function.Bijective fb := by
    apply (Nat.bijective_iff_surjective_and_card fb).mpr
    refine ⟨MonoidHom.rangeRestrict_surjective _, ?_⟩
    rw [MonoidHom.domRestrict_range, hBcard, hBmapcard]
  have hBdis : Disjoint Z B := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    have hxmap : f x = 1 := MonoidHom.mem_ker.mp (hker.symm ▸ hx.1)
    have heq : fb (⟨x, hx.2⟩ : B) = fb 1 := Subtype.ext (by simpa [fb] using hxmap)
    exact congrArg Subtype.val (hfb.1 heq)
  exact ⟨B, Subgroup.isComplement'_of_card_mul_and_disjoint
    (by rw [hBcard, hGcard, Nat.mul_comm]) hBdis⟩
