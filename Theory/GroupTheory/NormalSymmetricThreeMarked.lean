module

public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Two-perfect subgroups normalized by a Sylow subgroup near a normal S₃

Let `K` be a normal subgroup marked as the symmetric group on three points,
and let `R` be its embedded two-residual. Then `R` has order three and is
normal in the ambient group. A two-perfect subgroup `B` centralizes `R`,
since the automorphism group of `R` is a two-group.

If an ambient Sylow two-subgroup normalizes `B`, either `R ≤ B` or `B`
centralizes `K`. Indeed, `C_K(R) = R`, so the commutator of `B` with the
Sylow intersection lies in `R ∩ B`. A proper intersection is trivial, and
the residual and that Sylow intersection generate `K`. An order bound
`|B| ∣ 3 * 2^n` strengthens containment to equality. Independently of the
Sylow hypothesis, ambient three-rank at most two and three-rank of `B`
at least two force containment: a disjoint cubic factor would increase
the rank of every elementary abelian subgroup of `B` by one.

No normality of `B` in the ambient group is assumed. The residual is
`O²(K)`, not the two-core.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, proof of 13.8.5, printed pp.947–948 (PDF pp.964–965), the normal
one-factor S₃ case. This module supplies the generic finite-group argument;
the source specialization and its representation-theoretic consequences
belong to the chapter consumer.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.NormalSymmetricThreeMarked
variable {A : Type*} [Group A]

/-- The two-residual of `K`, embedded in the ambient group. -/
abbrev residual (K : Subgroup A) : Subgroup A := (pResidual 2 K).map K.subtype

/-- The embedded two-residual of a marked S₃ has order three. -/
theorem residual_card (K : Subgroup A) (e : K ≃* Equiv.Perm (Fin 3)) :
    Nat.card (residual K) = 3 := by
  rw [residual, card_map_of_injective K.subtype_injective]
  rw [← card_map_of_injective (K := pResidual 2 K) (f := e.toMonoidHom) e.injective, map_pResidual,
    Equiv.Perm.twoResidual_eq_alternating, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- Under the marking, membership in the embedded residual is evenness. -/
theorem mem_residual_iff (K : Subgroup A) (e : K ≃* Equiv.Perm (Fin 3)) (x : K) :
    (x : A) ∈ residual K ↔ e x ∈ alternatingGroup (Fin 3) := by
  have he := map_pResidual 2 e
  rw [Equiv.Perm.twoResidual_eq_alternating] at he
  change K.subtype x ∈ (pResidual 2 K).map K.subtype ↔ e.toMonoidHom x ∈ _
  rw [mem_map_iff_mem K.subtype_injective, ← he, mem_map_iff_mem e.injective]

private theorem perm_centralizer :
    ∀ x : Equiv.Perm (Fin 3),
      (∀ y : Equiv.Perm (Fin 3), y ∈ alternatingGroup (Fin 3) → y * x = x * y) →
        x ∈ alternatingGroup (Fin 3) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

/-- Inside the marked S₃, the cubic residual is self-centralizing. -/
theorem inf_centralizer_residual_le (K : Subgroup A) (e : K ≃* Equiv.Perm (Fin 3)) :
    K ⊓ centralizer (residual K : Set A) ≤ residual K := by
  intro x hx
  apply (mem_residual_iff K e ⟨x, hx.1⟩).mpr
  apply perm_centralizer
  intro y hy
  have hr : (e.symm y : A) ∈ residual K :=
    (mem_residual_iff K e (e.symm y)).mpr (by simpa using hy)
  have hc := hx.2 (e.symm y : A) hr
  have hh : e.symm y * (⟨x, hx.1⟩ : K) = (⟨x, hx.1⟩ : K) * e.symm y := Subtype.ext hc
  simpa only [map_mul, e.apply_symm_apply] using congrArg e hh

variable [Finite A]

/-- A two-perfect subgroup centralizes the normal cubic residual. -/
theorem centralizes_residual (K : Subgroup A) [K.Normal]
    (e : K ≃* Equiv.Perm (Fin 3)) (B : Subgroup A) (hB : IsPPerfect 2 B) :
    B ≤ centralizer (residual K : Set A) := by
  let R := residual K
  have hR : Nat.card R = 3 := residual_card K e
  let : IsCyclic R := isCyclic_of_prime_card hR
  have hp : IsPGroup 2 (MulAut R) := IsPGroup.of_card (n := 1) (by
    rw [IsCyclic.card_mulAut, hR]; decide)
  let f : B →* MulAut R := (MulAut.conjNormal : A →* MulAut R).comp B.subtype
  have hf := hB.hom_eq_one_of_isPGroup hp f
  intro b hb r hr
  have hh := congrArg (fun g : B →* MulAut R => g ⟨b, hb⟩ ⟨r, hr⟩) hf
  have hconj : b * r * b⁻¹ = r := congrArg Subtype.val hh
  exact (mul_inv_eq_iff_eq_mul.mp hconj).symm

omit [Finite A] in
/-- A cubic subgroup not contained in another subgroup has trivial intersection with it. -/
theorem inf_eq_bot_of_not_le {R B : Subgroup A} (hR : Nat.card R = 3) (h : ¬ R ≤ B) :
    R ⊓ B = ⊥ := by
  let : Fact (Nat.card R).Prime := ⟨hR ▸ Nat.prime_three⟩
  rcases ((R ⊓ B).subgroupOf R).eq_bot_or_eq_top_of_prime_card with hb | ht
  · have hh := congrArg (fun U : Subgroup R => U.map R.subtype) hb
    simpa only [map_subgroupOf_eq_of_le inf_le_left, Subgroup.map_bot] using hh
  · exfalso
    apply h
    intro x hx
    have hm : (⟨x, hx⟩ : R) ∈ (R ⊓ B).subgroupOf R := ht.symm ▸ mem_top _
    exact hm.2

/-- Sylow normalization forces residual containment or pointwise centralization of K. -/
theorem residual_le_or_centralizes (K : Subgroup A) [K.Normal]
    (e : K ≃* Equiv.Perm (Fin 3)) (S : Sylow 2 A)
    (B : Subgroup A) (hB : IsPPerfect 2 B)
    (hS : (S : Subgroup A) ≤ normalizer (B : Set A)) :
    residual K ≤ B ∨ B ≤ centralizer (K : Set A) := by
  by_cases h : residual K ≤ B
  · exact Or.inl h
  right
  have hc := centralizes_residual K e B hB
  have hi := inf_eq_bot_of_not_le (residual_card K e) h
  let P := (S : Subgroup A) ⊓ K
  have hcR : ⁅B, P⁆ ≤ residual K := by
    apply (le_inf ?_ ?_).trans (inf_centralizer_residual_le K e)
    · exact (commutator_mono le_rfl inf_le_right).trans (commutator_le_right B K)
    · exact (commutator_mono hc le_rfl).trans (commutator_le_left _ P)
  have hcB : ⁅B, P⁆ ≤ B :=
    le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans hS)
  have hcomm : ⁅B, P⁆ = ⊥ := le_bot_iff.mp (by
    simpa only [hi] using le_inf hcR hcB)
  have hcP := commutator_eq_bot_iff_le_centralizer.mp hcomm
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal K
  have hgen := congrArg (fun U : Subgroup K => U.map K.subtype)
    (pResidual_sup_sylow_eq_top T)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype, hT, subgroupOf_map_subtype] at hgen
  apply le_centralizer_iff.mpr
  rw [← hgen]
  exact sup_le (le_centralizer_iff.mp hc) (le_centralizer_iff.mp hcP)

omit [Finite A] in
/-- Containment and a three-times-two-power order bound force equality with the residual. -/
theorem eq_residual_of_le_of_card_dvd (K : Subgroup A) [K.Normal]
    (e : K ≃* Equiv.Perm (Fin 3)) (B : Subgroup A) (hB : IsPPerfect 2 B)
    (hle : residual K ≤ B) (hcard : ∃ n : ℕ, Nat.card B ∣ 3 * 2 ^ n) :
    B = residual K := by
  let N := (residual K).subgroupOf B
  have hc : Nat.card N = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans (residual_card K e)
  obtain ⟨n, hn⟩ := hcard
  have hd : Nat.card (B ⧸ N) ∣ 2 ^ n := by
    have hh := N.index_mul_card
    rw [hc, index_eq_card, mul_comm] at hh
    rw [← hh] at hn
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 3)).mp hn
  have ht := hB N inferInstance (IsPGroup.of_card_dvd_pow hd)
  apply le_antisymm _ hle
  intro b hb
  have hm : (⟨b, hb⟩ : B) ∈ N := ht.symm ▸ mem_top _
  exact hm

/-- With the order bound, the Sylow-invariant alternative gives equality or centralization. -/
theorem eq_residual_or_centralizes_of_card_dvd (K : Subgroup A) [K.Normal]
    (e : K ≃* Equiv.Perm (Fin 3)) (S : Sylow 2 A)
    (B : Subgroup A) (hB : IsPPerfect 2 B)
    (hS : (S : Subgroup A) ≤ normalizer (B : Set A))
    (hcard : ∃ n : ℕ, Nat.card B ∣ 3 * 2 ^ n) :
    B = residual K ∨ B ≤ centralizer (K : Set A) := by
  rcases residual_le_or_centralizes K e S B hB hS with h | h
  · exact Or.inl (eq_residual_of_le_of_card_dvd K e B hB h hcard)
  · exact Or.inr h

/-- In ambient three-rank at most two, a subgroup commuting with an independent cubic
subgroup has three-rank at most one. -/
theorem rank_le_one_of_disjoint_cubic (R B : Subgroup A)
    (hR : Nat.card R = 3) (hc : B ≤ centralizer (R : Set A))
    (hi : R ⊓ B = ⊥) (hr : primeRank 3 A ≤ 2) : primeRank 3 B ≤ 1 := by
  apply (primeRank_le_iff_elementary_card_le B).mpr
  intro E hE
  let := hE
  let : IsCyclic R := isCyclic_of_prime_card hR
  let : CommGroup R := IsCyclic.commGroup
  let : CommGroup E := IsMulCommutative.instCommGroup
  let f : E →* A := B.subtype.comp E.subtype
  let F : R × E →* A :=
    { toFun := fun x => x.1.val * f x.2
      map_one' := by simp
      map_mul' := by
        intro x y
        change ((x.1 : A) * y.1) * f (x.2 * y.2) = _
        rw [map_mul]
        have hh : Commute (y.1 : A) (f x.2) := hc x.2.val.property y.1 y.1.property
        exact hh.mul_mul_mul_comm _ _ }
  have hinj : Function.Injective F := by
    apply (injective_iff_map_eq_one F).mpr
    intro x hx
    have he : (x.1 : A) = (f x.2)⁻¹ := mul_eq_one_iff_eq_inv.mp hx
    have hb : (x.1 : A) ∈ B := he.symm ▸ B.inv_mem x.2.val.property
    have h1 : (x.1 : A) = 1 := by
      have hh : (x.1 : A) ∈ R ⊓ B := ⟨x.1.property, hb⟩
      rwa [hi, mem_bot] at hh
    have h2 : f x.2 = 1 := by
      change (x.1 : A) * f x.2 = 1 at hx
      simpa only [h1, one_mul] using hx
    exact Prod.ext (Subtype.ext h1) (Subtype.ext (Subtype.ext h2))
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
  have hpow : ∀ x : R × E, x ^ 3 = 1 := by
    intro x
    apply Prod.ext
    · exact hR ▸ pow_card_eq_one' (x := x.1)
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.exponent_dvd_p x.2
  have hsize : Nat.card (R × E) = 3 ^ (n + 1) := by
    rw [Nat.card_prod, hR, hn, pow_succ, mul_comm]
  have hbound := (primeRank_ge_of_elementary_embedding hpow hsize F hinj).trans hr
  have hn1 : n ≤ 1 := by omega
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) hn1

/-- A two-perfect subgroup of three-rank at least two contains the marked cubic residual
when the ambient three-rank is at most two. This conclusion needs no Sylow normalization. -/
theorem residual_le_of_rank (K : Subgroup A) [K.Normal]
    (e : K ≃* Equiv.Perm (Fin 3)) (B : Subgroup A) (hB : IsPPerfect 2 B)
    (hA : primeRank 3 A ≤ 2) (hrB : 2 ≤ primeRank 3 B) : residual K ≤ B := by
  by_contra h
  have hh := rank_le_one_of_disjoint_cubic (residual K) B (residual_card K e)
    (centralizes_residual K e B hB) (inf_eq_bot_of_not_le (residual_card K e) h) hA
  omega
end Theory.GroupTheory.NormalSymmetricThreeMarked
