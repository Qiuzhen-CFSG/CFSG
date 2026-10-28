module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.AlternatingBinary.Basic
public import Theory.Alternating.Aut
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Reducing the A₇ central-cover case to its permutation action

If R ∩ Z(Q) is visible in R/Φ(R), it already gives an invariant proper
subgroup. Otherwise the quotient image of R is noncyclic: cyclicity would
lift through the Frattini kernel. Its order is therefore nine, and the
odd-complement exponent hypothesis makes it elementary abelian.

An invariant line in that image pulls back to a proper subgroup of R which
is not contained in Φ(R). Its image in R/Φ(R) is consequently nonzero and
proper. Every extending automorphism descends through the actual central
quotient, and the proved Aut(A₇) = S₇ theorem identifies that action with
permutation conjugation. This handles all central covers without a multiplier
assumption or a faithfulness assumption on the action of the cover's center.

`SevenPermutationLine` isolates the remaining finite permutation calculation.
The conditional theorem below proves the complete central-cover reduction;
it does not assert that this remaining input has been established.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.4, printed p.511 (PDF p.528). The source's order-72 subgroup
exists, so its exclusion requires the action in S₇, not an order contradiction.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.AlternatingBinary

private abbrev A7 := alternatingGroup (Fin 7)

/-- The concrete A₇ action calculation needed by the cover reduction: an
order-nine subgroup permuting with a Sylow two-subgroup has a line preserved
by every permutation normalizing both members of the pair. -/
def SevenPermutationLine : Prop :=
  ∀ (P : Sylow 2 (alternatingGroup (Fin 7))) (D : Subgroup (alternatingGroup (Fin 7))),
    Nat.card D = 9 →
    (D : Set (alternatingGroup (Fin 7))) * (P : Set (alternatingGroup (Fin 7))) =
      (P : Set (alternatingGroup (Fin 7))) * (D : Set (alternatingGroup (Fin 7))) →
    ∃ C : Subgroup (alternatingGroup (Fin 7)), C ≤ D ∧ Nat.card C = 3 ∧
      ∀ σ : Equiv.Perm (Fin 7),
        (∀ x : alternatingGroup (Fin 7), MulAut.conjNormal σ x ∈ P ↔ x ∈ P) →
        (∀ x : alternatingGroup (Fin 7), MulAut.conjNormal σ x ∈ D ↔ x ∈ D) →
        ∀ x ∈ C, MulAut.conjNormal σ x ∈ C

private theorem sylow_three_card_seven (P : Sylow 3 A7) : Nat.card P = 9 := by
  rw [P.card_eq_multiplicity, nat_card_alternatingGroup]
  norm_num [Nat.factorial]
  rw [show 2520 = 3 ^ 2 * 280 by decide,
    Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    Nat.prime_three.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 280)]
  rfl

private theorem card_nine_of_not_cyclic {D : Subgroup A7} (hD : IsPGroup 3 D)
    (hn : ¬ IsCyclic D) : Nat.card D = 9 := by
  obtain ⟨P, hDP⟩ := hD.exists_le_sylow
  have hd := card_dvd_of_le hDP
  rw [sylow_three_card_seven] at hd
  obtain ⟨n, hn', hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (show Nat.card D ∣ 3 ^ 2 from hd)
  interval_cases n
  · exact (hn (isCyclic_of_card_dvd_prime (p := 3) (by rw [hc]; decide))).elim
  · exact (hn (isCyclic_of_prime_card (p := 3) (by simpa using hc))).elim
  · simpa using hc

universe u v
variable {Q : Type u} [Group Q] [Finite Q]

omit [Finite Q] in
private theorem pair_preserves_right {R : Subgroup Q} {b : MulAut R}
    {c : MulAut Q} (he : ∀ x : R, (b x : Q) = c x) (x : Q) :
    c x ∈ R ↔ x ∈ R := by
  constructor
  · intro hx
    have hh := he (b.symm ⟨c x, hx⟩)
    have hh' : c ((b.symm ⟨c x, hx⟩ : R) : Q) = c x := by
      rw [← hh]
      exact congrArg Subtype.val (b.apply_symm_apply ⟨c x, hx⟩)
    exact c.injective hh' ▸ (b.symm ⟨c x, hx⟩).property
  · intro hx
    rw [← he ⟨x, hx⟩]
    exact (b ⟨x, hx⟩).property

omit [Finite Q] in
private theorem image_preserved {G : Type v} [Group G]
    (f : Q →* G) (U : Subgroup Q) (b : MulAut Q) (c : MulAut G)
    (he : ∀ x, c (f x) = f (b x)) (hU : ∀ x, b x ∈ U ↔ x ∈ U) (y : G) :
    c y ∈ U.map f ↔ y ∈ U.map f := by
  constructor
  · rintro ⟨x, hx, hx'⟩
    refine ⟨b.symm x, (hU _).mp (by simpa using hx), ?_⟩
    apply c.injective
    rw [he, b.apply_symm_apply, hx']
  · rintro ⟨x, hx, rfl⟩
    exact ⟨b x, (hU x).mpr hx, (he x).symm⟩

private theorem reducible_of_image_line {G : Type v} [Group G] [Finite G]
    {S R : Subgroup Q} (f : Q →* G)
    (hphi : frattini R ≤ (f.subgroupMap R).ker)
    (C : Subgroup G) (hCD : C ≤ R.map f) (hCb : C ≠ ⊥) (hCt : C ≠ R.map f)
    (hi : ∀ b ∈ pairAutomizer S R, ∀ x : R, f x ∈ C → f (b x) ∈ C) :
    PairReducible S R := by
  let K : Subgroup R := (C.comap f).subgroupOf R
  let q := QuotientGroup.mk' (frattini R)
  have hK : ¬ K ≤ frattini R := by
    intro hk
    apply hCb
    apply eq_bot_iff.mpr
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hCD hy
    have hxK : (⟨x, hx⟩ : R) ∈ K := hy
    have hfx := congrArg Subtype.val (hphi (hk hxK))
    exact mem_bot.mpr hfx
  have hKt : K ≠ ⊤ := by
    intro ht
    apply hCt
    apply le_antisymm hCD
    rintro y ⟨x, hx, rfl⟩
    exact show (⟨x, hx⟩ : R) ∈ K from ht ▸ mem_top _
  apply pairReducible_of_invariant
  refine ⟨K.map q, ?_, ?_, ?_⟩
  · intro he
    apply hK
    intro x hx
    exact (QuotientGroup.eq_one_iff x).mp
      (mem_bot.mp (he ▸ (mem_map.mpr ⟨x, hx, rfl⟩ : q x ∈ K.map q)))
  · intro he
    apply hKt
    apply frattini_nongenerating
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using
      congrArg (Subgroup.comap q) he
  · rintro b hb _ ⟨x, hx, rfl⟩
    rw [quotientAut_apply_mk]
    exact mem_map.mpr ⟨b x, hi b hb x hx, rfl⟩

/-- The A₇ exclusion for every finite central cover, conditional only on the
explicit permutation-line calculation. The final source theorem must supply
`SevenPermutationLine`; no local irreducibility is assumed here. -/
theorem alternating_seven_of_permutationLine (hline : SevenPermutationLine)
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (e : Q ⧸ center Q ≃* alternatingGroup (Fin 7)) : PairReducible (S : Subgroup Q) R := by
  by_contra hn
  have hK : (center Q).subgroupOf R ≤ frattini R := by
    by_contra hv
    exact hn (pairReducible_of_centralIntersection (not_le_center h) hv)
  let f : Q →* A7 := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := S.mapSurjective hf
  have hker : (f.subgroupMap R).ker ≤ frattini R := by
    intro x hx
    apply hK
    change (x : Q) ∈ center Q
    apply (QuotientGroup.eq_one_iff (x : Q)).mp
    apply e.injective
    have hx' : f x = 1 := congrArg Subtype.val hx
    simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply, map_one] using hx'
  have hnoncyc : ¬ IsCyclic (R.map f) := by
    intro hc
    let _ := hc
    exact h.oddComplement.not_isCyclic
      (isCyclic_of_frattini_kernel (f.subgroupMap R) (f.subgroupMap_surjective R) hker)
  have hDcard : Nat.card (R.map f) = 9 :=
    card_nine_of_not_cyclic (h.oddComplement.isPGroup.map f) hnoncyc
  have hDcomm : IsMulCommutative (R.map f) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hDcard
  let _ := hDcomm
  have hexp : Monoid.exponent R ∣ 3 := by
    rcases h.oddComplement with ⟨he, _⟩ | ⟨_, _, he⟩
    · exact he.exponent_dvd_p
    · rw [he]
  let _ : IsElementaryAbelian 3 (R.map f) := {
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      obtain ⟨y, rfl⟩ := f.subgroupMap_surjective R x
      rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp y, map_one] }
  let _ : Fact (IsPGroup 3 (R.map f)) := ⟨h.oddComplement.isPGroup.map f⟩
  have hphi : frattini R ≤ (f.subgroupMap R).ker := by
    have hh := frattini_le_comap_frattini_of_surjective (f.subgroupMap_surjective R)
    simpa only [frattini_eq_bot_of_isElementaryAbelian (p := 3), MonoidHom.comap_bot] using hh
  have hp : (R.map f : Set A7) * (P : Set A7) = (P : Set A7) * (R.map f : Set A7) := by
    have hh := congrArg (fun A : Set Q => f '' A) h.permutes
    simpa only [P, ← Sylow.coe_coe, Sylow.coe_mapSurjective, coe_map, Set.image_mul] using hh
  obtain ⟨C, hCD, hCcard, hC⟩ := hline P (R.map f) hDcard hp
  apply hn
  apply reducible_of_image_line f hphi C hCD
  · intro he
    rw [he, card_bot] at hCcard
    omega
  · intro he
    rw [he, hDcard] at hCcard
    omega
  · rintro b ⟨c, hc, he⟩ x hx
    let a := MulAut.centralQuotientAction e c
    have ha : ∀ x, a (f x) = f (c x) := MulAut.centralQuotientAction_apply e c
    obtain ⟨σ, hσ⟩ :=
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide)
        (by decide)).surjective a
    have hs : ∀ y : A7, MulAut.conjNormal σ y ∈ P ↔ y ∈ P := by
      intro y
      rw [hσ]
      exact image_preserved f (S : Subgroup Q) c a ha hc y
    have hr : ∀ y : A7, MulAut.conjNormal σ y ∈ R.map f ↔ y ∈ R.map f := by
      intro y
      rw [hσ]
      exact image_preserved f R c a ha (pair_preserves_right he) y
    have hh := hC σ hs hr (f x) hx
    rw [hσ, ha, ← he x] at hh
    exact hh

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.AlternatingBinary
