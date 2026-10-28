module

public import Theory.Frattini.Rank
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.PGroup.Omega
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.GroupTheory.PrimeRankWitness

/-!
# Prime rank computed on elementary abelian subgroups

For finite groups, the existing prime rank, defined using generator ranks
of abelian p-subgroups, is bounded by n exactly when every elementary abelian
p-subgroup has order at most p^n. This certifies the convention used in the
quasithin definition against the elementary-rank convention in the source.

For an abelian p-group A, the p-th power map has kernel first omega and
image the Frattini subgroup. Hence first omega and A/Frattini(A) have the
same order. Generator lifting from the Frattini quotient bounds the rank
of A by its elementary subgroup. The opposite inequality follows from the
exponent bound on the order of a finitely generated abelian group.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, §0.1,
printed p.4. The power-map calculation generalizes the binary calculation
in Theory.GroupTheory.PGroup.AbelianOmegaFrattini without changing that API.
-/

public section

open scoped IsMulCommutative

/-- The p-th powers form the Frattini subgroup of a finite abelian p-group. -/
theorem IsPGroup.pow_range_eq_frattini {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommGroup A] [Finite A] (hA : IsPGroup p A) :
    (powMonoidHom p : A →* A).range = frattini A := by
  let : Fact (IsPGroup p A) := ⟨hA⟩
  let R := (powMonoidHom p : A →* A).range
  have hR : IsElementaryAbelian p (A ⧸ R) := by
    refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective R q
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := R) _).mpr ⟨a, rfl⟩
  let : IsElementaryAbelian p (A ⧸ R) := hR
  let : Fact (IsPGroup p (A ⧸ R)) := ⟨hA.to_quotient R⟩
  have hphi : frattini (A ⧸ R) = ⊥ :=
    frattini_eq_bot_of_isElementaryAbelian (p := p)
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    exact pth_power_mem_frattini_of_isPGroup (p := p) a
  · have h := frattini_le_comap_frattini_of_surjective
      (φ := QuotientGroup.mk' R) (QuotientGroup.mk'_surjective R)
    simpa only [hphi, MonoidHom.comap_bot, QuotientGroup.ker_mk'] using h

/-- First omega is the kernel of the p-th power map in an abelian group. -/
theorem powMonoidHom_ker_eq_omega_one {p : ℕ} {A : Type*} [CommGroup A] :
    (powMonoidHom p : A →* A).ker = omega₁ A (p := p) := by
  apply le_antisymm
  · intro x hx
    exact Subgroup.subset_closure (by simpa using hx)
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    simpa using hx

/-- A bound on first omega bounds the generator rank of an abelian p-group. -/
theorem IsPGroup.rank_le_of_card_omega_one_le {p n : ℕ} [Fact p.Prime]
    (A : Type*) [Group A] [Finite A] [IsMulCommutative A]
    (hA : IsPGroup p A) (hcard : Nat.card (omega₁ A (p := p)) ≤ p ^ n) :
    Group.rank A ≤ n := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  let : Fact (IsPGroup p A) := ⟨hA⟩
  let : IsElementaryAbelian p (A ⧸ frattini A) :=
    isElementaryAbelian_quotient_frattini (p := p)
  have hsize : Nat.card (A ⧸ frattini A) = Nat.card (omega₁ A (p := p)) := by
    rw [← IsPGroup.pow_range_eq_frattini hA, ← Subgroup.index_eq_card,
      Subgroup.index_range, powMonoidHom_ker_eq_omega_one]
  rw [Group.rank_eq_rank_quotient_frattini A]
  exact IsElementaryAbelian.rank_le_of_card_le _ (hsize ▸ hcard)

/-- The abelian-generator and elementary-abelian definitions of prime-rank bounds agree. -/
theorem primeRank_le_iff_elementary_card_le {p n : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] :
    primeRank p G ≤ n ↔ ∀ E : Subgroup G,
      IsElementaryAbelian p E → Nat.card E ≤ p ^ n := by
  constructor
  · intro h E hE
    let : IsElementaryAbelian p E := hE
    let : CommGroup E := IsMulCommutative.instCommGroup
    have hpow : ∀ x : E, x ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p E)
    calc
      Nat.card E ≤ p ^ Group.rank E :=
        Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos _)
          (card_dvd_exponent_pow_rank' E hpow)
      _ ≤ p ^ n := pow_le_pow_right' (Fact.out : p.Prime).one_lt.le
        ((E.rank_le_primeRank p (IsElementaryAbelian.isPGroup p E)).trans h)
  · intro h
    apply csSup_le'
    rintro k ⟨A, hAp, hAc, _, hk⟩
    let : IsMulCommutative A := hAc
    let : IsElementaryAbelian p (omega₁ A (p := p)) :=
      IsElementaryAbelian.omega₁_of_isMulCommutative A
    have hcard := h ((omega₁ A (p := p)).map A.subtype)
      IsElementaryAbelian.map_subtype
    rw [Subgroup.card_map_of_injective A.subtype_injective] at hcard
    exact hk.trans (IsPGroup.rank_le_of_card_omega_one_le A hAp hcard)

/-- A small subgroup containing every element whose p-th power is one bounds
the ambient prime rank. The ambient group need not itself be a p-group. -/
theorem primeRank_le_of_pow_eq_one_subset {p n : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] [Finite G] (E : Subgroup G)
    (hcard : Nat.card E ≤ p ^ n)
    (hpow : ∀ x : G, x ^ p = 1 → x ∈ E) : primeRank p G ≤ n := by
  apply (primeRank_le_iff_elementary_card_le G).mpr
  intro A hA
  have hAE : A ≤ E := by
    intro x hx
    apply hpow x
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      hA.exponent_dvd_p (⟨x, hx⟩ : A)
    exact congrArg Subtype.val h
  exact (Subgroup.card_le_of_le hAE).trans hcard
