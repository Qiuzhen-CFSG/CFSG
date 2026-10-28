module
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.PGroupCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic

/-!
# Small normal sections above a symmetric-six quotient

Let M map onto S₆ with a two-group kernel. The two-residual O²(M)
centralizes every normal two-section inside that kernel of order at most
eight. The section is the literal D/(Z ∩ D), and its conjugation action
is induced by the original group.

Orbit counting modulo five shows that a two-group of order at most eight
has no automorphism of order five. For any image of M whose order is prime
to five, quotienting its two-core gives an image of S₆. Every nontrivial
normal subgroup of S₆ contains A₆, so this quotient has order at most two.
The original image is therefore a two-group, and O²(M) kills it.

Source application: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs
of rank two* (1993), (5.7), printed p.919, in the small normal-section
centrality step. The graph geometry and the section-order bound remain
with the source consumer.
-/

public section

open Subgroup

/-- No automorphism of order five acts on a two-group of order at most eight. -/
theorem MulAut.not_five_dvd_card_of_twoGroup_card_le_eight {V : Type*} [Group V] [Finite V]
    (hV : IsPGroup 2 V) (hcard : Nat.card V ≤ 8) :
    ¬ 5 ∣ Nat.card (MulAut V) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro hdiv
  obtain ⟨n, hn⟩ := hV.exists_card_eq
  have hnle : n ≤ 3 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hn] using hcard
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 5 hdiv
  let P := zpowers a
  have hP : Nat.card P = 5 := by rw [Nat.card_zpowers, ha]
  have hp : IsPGroup 5 P := IsPGroup.of_card (n := 1) (by simpa using hP)
  let F := FixedPoints.subgroup P V
  have hmod := hp.card_modEq_card_fixedPoints V
  change Nat.card V % 5 = Nat.card F % 5 at hmod
  have hFdiv : Nat.card F ∣ 2 ^ n := hn ▸ F.card_subgroup_dvd_card
  obtain ⟨k, hk, hFcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hFdiv
  have heq : Nat.card F = Nat.card V := by
    rw [hn, hFcard] at hmod ⊢
    interval_cases n <;> interval_cases k <;> norm_num at *
  have htop := F.eq_top_of_card_eq heq
  have haone : a = 1 := by
    apply MulEquiv.ext
    intro x
    exact (show x ∈ F from htop ▸ mem_top x) ⟨a, mem_zpowers a⟩
  rw [haone, orderOf_one] at ha
  norm_num at ha

/-- An image of a two-group extension of S₆ has two-power order whenever its
target has order prime to five. -/
theorem MonoidHom.isPGroup_range_of_symmetricSix_quotient {M A : Type*} [Group M] [Finite M] [Group A] [Finite A]
    (q : M →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q)
    (hker : IsPGroup 2 q.ker) (f : M →* A) (hfive : ¬ 5 ∣ Nat.card A) :
    IsPGroup 2 f.range := by
  let B := f.range
  let π := QuotientGroup.mk' (pCore 2 B)
  let g := π.comp f.rangeRestrict
  let N := q.ker.map f.rangeRestrict
  let : N.Normal := Normal.map inferInstance f.rangeRestrict f.rangeRestrict_surjective
  have hN : N ≤ pCore 2 B := le_sSup ⟨inferInstance, hker.map f.rangeRestrict⟩
  have hk : q.ker ≤ g.ker := by
    intro x hx
    exact (QuotientGroup.eq_one_iff _).mpr (hN (mem_map_of_mem f.rangeRestrict hx))
  let t := q.liftOfSurjective hq ⟨g,hk⟩
  have ht (x : M) : t (q x) = g x := by simp [t, MonoidHom.liftOfSurjective]
  have htonto : Function.Surjective t := by
    intro x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) x
    obtain ⟨z,rfl⟩ := f.rangeRestrict_surjective y
    exact ⟨q z, ht z⟩
  have hfiveB : ¬ 5 ∣ Nat.card (B ⧸ pCore 2 B) := by
    intro hd
    exact hfive (hd.trans ((card_quotient_dvd_card _).trans f.range.card_subgroup_dvd_card))
  have hn : t.ker ≠ ⊥ := by
    intro hz
    have hd := card_dvd_of_injective t ((MonoidHom.ker_eq_bot_iff t).mp hz)
    have h5 : 5 ∣ Nat.card (Equiv.Perm (Fin 6)) := by
      rw [Nat.card_perm, Nat.card_fin]
      decide
    exact hfiveB (h5.trans hd)
  have hAlt : alternatingGroup (Fin 6) ≤ t.ker :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp) ((nontrivial_iff_ne_bot _).mpr hn)
  have htwo : Nat.card (B ⧸ pCore 2 B) ∣ 2 := by
    have hi := index_dvd_of_le hAlt
    rw [alternatingGroup.index_eq_two, index_ker,
      t.range_eq_top_of_surjective htonto, card_top] at hi
    exact hi
  have hp : IsPGroup 2 (B ⧸ pCore 2 B) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp htwo with h | h
    · exact IsPGroup.of_card (n := 0) (by simpa using h)
    · exact IsPGroup.of_card (n := 1) (by simpa using h)
  have hpker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hh := (hp.to_subgroup ⊤).comap_of_ker_isPGroup π hpker
  rw [comap_top] at hh
  exact hh.of_equiv (topEquiv : (⊤ : Subgroup B) ≃* B)

open scoped commutatorElement

/-- The original two-residual centralizes a normal section of order at most
eight in the kernel of the supplied symmetric-six quotient. -/
theorem Subgroup.commutator_pResidual_le_of_symmetricSix_small_section {M : Type*} [Group M] [Finite M]
    (q : M →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q)
    (hker : IsPGroup 2 q.ker) (D Z : Subgroup M) [D.Normal] [Z.Normal]
    (hD : D ≤ q.ker) (hcard : Z.relIndex D ≤ 8) :
    ⁅D,pResidual 2 M⁆ ≤ Z := by
  let V := D ⧸ Z.subgroupOf D
  have hV : IsPGroup 2 V := (hker.to_le hD).to_quotient _
  obtain ⟨a,ha⟩ := exists_quotient_conjugation_action (⊤ : Subgroup M) D Z
    (le_normalizer_of_normal) (le_normalizer_of_normal) inferInstance
  let f := a.comp (topEquiv : (⊤ : Subgroup M) ≃* M).symm.toMonoidHom
  have hf : IsPGroup 2 f.range := MonoidHom.isPGroup_range_of_symmetricSix_quotient q hq hker f
    (MulAut.not_five_dvd_card_of_twoGroup_card_le_eight hV hcard)
  have hk := pResidual_le_ker_of_isPGroup 2 f.rangeRestrict hf
  rw [MonoidHom.ker_rangeRestrict] at hk
  rw [commutator_comm]
  apply commutator_le.mpr
  intro m hm d hd
  have htriv : a ⟨m, mem_top _⟩ = 1 := hk hm
  have hfix := ha ⟨m, mem_top _⟩ ⟨d,hd⟩
  rw [htriv] at hfix
  have hmember := QuotientGroup.eq_iff_div_mem.mp hfix.symm
  change m*d*m⁻¹/d ∈ Z at hmember
  simpa only [div_eq_mul_inv,commutatorElement_def] using hmember
