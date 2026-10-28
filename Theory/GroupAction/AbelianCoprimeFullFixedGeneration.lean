module

public import Theory.GroupAction.AbelianCoprimeFixedGeneration
public import Mathlib.GroupTheory.Sylow

/-!
# Fixed-point generation for coprime abelian p-group actors

An abelian p-group acting coprimely on a finite group generates that group
through the fixed subgroups of actor subgroups with cyclic quotient.
No solvability or noncyclicity hypothesis is needed.

The p-group orbit congruence supplies an invariant Sylow q-subgroup for
each prime q dividing the target order. Apply coprime fixed-point generation
inside each Sylow subgroup. Their images lie in the corresponding fixed
groups of the target, and their orders force the generated subgroup to be
the whole target.

Extracted from the full-group step of Feit–Thompson background Proposition
(1.16)(b), formerly in `FeitThompson.GroupAction.NoncyclicAbelianPGroup`.
That module re-exports the invariant Sylow theorem and retains its original
noncyclic fixed-generation interfaces.
-/

open scoped Pointwise

theorem fixedPointSubgroup_map_subtype_le
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (H : Subgroup G) [IsInvariant A G H] (Y : Subgroup A) :
    (fixedPointSubgroup (↥Y) H).map H.subtype ≤ fixedPointSubgroup (↥Y) G := by
  intro g hg
  rcases hg with ⟨x, hx, rfl⟩
  have hx' : ∀ y : Y, y • x = x := by
    simpa [FixedPoints.mem_subgroup] using hx
  show ∀ y : Y, ((y : A) • ((x : H) : G)) = ((x : H) : G)
  intro y
  exact congrArg Subtype.val (hx' y)

public theorem exists_invariant_sylow
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [Fact (IsPGroup p A)] [MulDistribMulAction A G]
    (hG : Nat.Coprime p (Nat.card G)) :
    ∃ P : Sylow q G, IsInvariant A G (P : Subgroup G) := by
  classical
  let P₀ : Sylow q G := default
  have hcard_dvd : Nat.card (Sylow q G) ∣ Nat.card G := by
    exact dvd_trans (Sylow.card_dvd_index P₀) (Subgroup.index_dvd_card (H := (P₀ : Subgroup G)))
  have hcop_sylow : Nat.Coprime p (Nat.card (Sylow q G)) :=
    Nat.Coprime.of_dvd_right hcard_dvd hG
  have hpSylow : ¬ p ∣ Nat.card (Sylow q G) :=
    ((Fact.out : p.Prime).coprime_iff_not_dvd).1 hcop_sylow
  rcases (Fact.out : IsPGroup p A).nonempty_fixed_point_of_prime_not_dvd_card (Sylow q G) hpSylow with
    ⟨P, hPfix⟩
  refine ⟨P, ?_⟩
  constructor
  intro a g
  have hsmulP : a • (P : Subgroup G) = (P : Subgroup G) := by
    simpa [Sylow.pointwise_smul_def] using
      congrArg (fun Q : Sylow q G => (Q : Subgroup G)) ((MulAction.mem_fixedPoints.mp hPfix) a)
  constructor
  · intro hg
    have : a • g ∈ a • (P : Subgroup G) :=
      Subgroup.smul_mem_pointwise_smul g a (P : Subgroup G) hg
    simpa [hsmulP] using this
  · intro hg
    have hsmulPinv : a⁻¹ • (P : Subgroup G) = (P : Subgroup G) := by
      simpa [Sylow.pointwise_smul_def] using congrArg (fun Q : Sylow q G => (Q : Subgroup G))
        ((MulAction.mem_fixedPoints.mp hPfix) a⁻¹)
    have : a⁻¹ • (a • g) ∈ a⁻¹ • (P : Subgroup G) :=
      Subgroup.smul_mem_pointwise_smul (a • g) a⁻¹ (P : Subgroup G) hg
    simpa [hsmulPinv] using this

theorem eq_top_of_exists_sylow_le
    {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hSyl :
      ∀ p : ℕ, p ∈ (Nat.card G).primeFactors → ∀ [Fact p.Prime],
        ∃ P : Sylow p G, (P : Subgroup G) ≤ H) :
    H = ⊤ := by
  rw [← Subgroup.card_eq_iff_eq_top]
  apply Nat.eq_of_factorization_eq Nat.card_pos.ne' Nat.card_pos.ne'
  intro p
  by_cases hp : p.Prime
  · let _ : Fact p.Prime := ⟨hp⟩
    by_cases hd : p ∈ (Nat.card G).primeFactors
    · obtain ⟨P, hPle⟩ := hSyl p hd
      refine le_antisymm
        ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
          (Subgroup.card_subgroup_dvd_card H) p) ?_
      rw [← pow_le_pow_iff_right₀ (Nat.Prime.one_lt hp), ← Sylow.card_eq_multiplicity P]
      have hc : Nat.card P = Nat.card (P.subgroupOf H) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).symm
      have hpP : IsPGroup p (P.subgroupOf H) := by
        refine IsPGroup.of_card (n := (Nat.card G).factorization p) ?_
        rw [← hc, ← Sylow.card_eq_multiplicity P]
      rcases IsPGroup.exists_le_sylow hpP with ⟨P', hP'⟩
      rw [← Sylow.card_eq_multiplicity P', hc]
      exact Subgroup.card_le_of_le hP'
    · have hnpG : ¬ p ∣ Nat.card G := by
        intro hpG
        exact hd ((Nat.mem_primeFactors).2 ⟨hp, hpG, Nat.card_pos.ne'⟩)
      have hnpH : ¬ p ∣ Nat.card H := by
        intro hpH
        exact hnpG (dvd_trans hpH (Subgroup.card_subgroup_dvd_card H))
      simp [Nat.factorization_eq_zero_of_not_dvd hnpG, Nat.factorization_eq_zero_of_not_dvd hnpH]
  · simp [Nat.factorization_eq_zero_of_not_prime (n := Nat.card G) (p := p) hp,
      Nat.factorization_eq_zero_of_not_prime (n := Nat.card H) (p := p) hp]

/-- A coprime abelian p-group action generates the target from cyclic-quotient fixed groups. -/
public theorem iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup_action
    {G A : Type*} [Group G] [Finite G] [CommGroup A] [Finite A] (p : ℕ) [Fact p.Prime]
    (hG : Nat.Coprime p (Nat.card G)) [Fact (IsPGroup p A)] [MulDistribMulAction A G] :
    (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), fixedPointSubgroup (↥Y) G) = ⊤ := by
  classical
  let H : Subgroup G := ⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), fixedPointSubgroup (↥Y) G
  have hHtop : H = ⊤ := by
    refine eq_top_of_exists_sylow_le H ?_
    intro q hq _hq
    obtain ⟨Q, hQinv⟩ := exists_invariant_sylow (G := G) (A := A) (p := p) (q := q) hG
    let _ : IsInvariant A G (Q : Subgroup G) := hQinv
    have hq_dvd_G : q ∣ Nat.card G := (Nat.mem_primeFactors.mp hq).2.1
    have hp_not_dvd_q : ¬ p ∣ q := by
      intro hpq
      exact (((Fact.out : p.Prime).coprime_iff_not_dvd).1 hG) (dvd_trans hpq hq_dvd_G)
    obtain ⟨n, hn⟩ := (Fact.out : IsPGroup p A).exists_card_eq
    have hAq : Nat.Coprime (Nat.card A) q := by
      rw [hn]
      exact ((Fact.out : p.Prime).coprime_pow_of_not_dvd (m := n) hp_not_dvd_q).symm
    let _ : Fact (IsPGroup q (Q : Subgroup G)) := ⟨Q.isPGroup'⟩
    have hQtop :
        (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)),
          fixedPointSubgroup (↥Y) (Q : Subgroup G)) = ⊤ := by
      exact iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup (G := (Q : Subgroup G)) (A := A) (q := q) hAq
    have hQle : (Q : Subgroup G) ≤ H := by
      calc
        (Q : Subgroup G) = (⊤ : Subgroup (Q : Subgroup G)).map (Q : Subgroup G).subtype := by
              ext x
              simp
        _ = (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)),
              fixedPointSubgroup (↥Y) (Q : Subgroup G)).map (Q : Subgroup G).subtype := by
              exact congrArg (fun K : Subgroup (Q : Subgroup G) => K.map (Q : Subgroup G).subtype)
                hQtop.symm
        _ = ⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)),
              (fixedPointSubgroup (↥Y) (Q : Subgroup G)).map (Q : Subgroup G).subtype := by
              simp [Subgroup.map_iSup]
        _ ≤ H := by
              refine iSup_le ?_
              intro Y
              refine iSup_le ?_
              intro hY
              exact (fixedPointSubgroup_map_subtype_le (A := A) (G := G) (H := (Q : Subgroup G)) Y).trans
                (le_iSup_of_le Y (le_iSup_of_le hY le_rfl))
    exact ⟨Q, hQle⟩
  simpa [H] using hHtop

