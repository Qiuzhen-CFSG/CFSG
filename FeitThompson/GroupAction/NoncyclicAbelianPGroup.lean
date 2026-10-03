module

public import FeitThompson.BGsection1.Defs
public import Theory.GroupAction.AbelianCoprimeFullFixedGeneration

/-!
# Fixed-point generation by a noncyclic abelian p-group

A noncyclic abelian p-group acting coprimely on a finite group generates
that group by fixed subgroups of its nonidentity cyclic subgroups. The
cyclic-quotient fixed-generation argument for invariant Sylow subgroups
is supplied by the shared Theory lemma; invariant Sylows and their orders
then give generation of the full group. Every cyclic-quotient actor
subgroup is nontrivial, so its fixed subgroup lies inside the fixed
subgroup of some nonidentity cyclic actor.

The three existing public statements and their supplied actions are
preserved. The representation/Frattini proof of the q-group intermediate
lives in Theory.GroupAction.AbelianCoprimeFixedGeneration, and the full-group
step lives in Theory.GroupAction.AbelianCoprimeFullFixedGeneration; the local
statements below are compatibility wrappers. This is the background
fixed-generation result used in Feit–Thompson Proposition (1.16).
-/

open scoped Pointwise

theorem proposition_1_16_b_qgroup
    {G A : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime] [Fact (IsPGroup q G)]
    [CommGroup A] [Finite A] [MulDistribMulAction A G]
    (hAq : Nat.Coprime (Nat.card A) q) :
    (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), fixedPointSubgroup (↥Y) G) = ⊤ := by
  exact iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup
    (G := G) (A := A) (q := q) hAq

public theorem iSup_fixedPointSubgroup_cyclicQuot_eq_top_of_noncyclic_abelian_pGroup_action
    {G A : Type*} [Group G] [Finite G] [CommGroup A] [Finite A] (p : ℕ) [Fact p.Prime]
    (hG : Nat.Coprime p (Nat.card G)) [Fact (IsPGroup p A)] [MulDistribMulAction A G]
    (hncyc : ¬ IsCyclic A) :
    (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), fixedPointSubgroup (↥Y) G) = ⊤ := by
  let _ := hncyc
  exact iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup_action p hG

public theorem iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    {G A : Type*} [Group G] [Finite G] [CommGroup A] [Finite A] (p : ℕ) [Fact p.Prime]
    (hG : Nat.Coprime p (Nat.card G)) [Fact (IsPGroup p A)] [MulDistribMulAction A G]
    (hncyc : ¬ IsCyclic A) :
    (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) G) = ⊤ := by
  let _ := hG
  have hcyc :
      (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), fixedPointSubgroup (↥Y) G) = ⊤ :=
    iSup_fixedPointSubgroup_cyclicQuot_eq_top_of_noncyclic_abelian_pGroup_action
      (G := G) (A := A) (p := p) hG (hncyc := hncyc)
  have hle :
      (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), fixedPointSubgroup (↥Y) G) ≤
        (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) G) := by
    refine iSup₂_le ?_
    intro Y hY
    have hY_ne_bot : Y ≠ ⊥ := by
      intro hY_bot
      subst hY_bot
      have _ : IsCyclic (A ⧸ (⊥ : Subgroup A)) := hY
      have hcycA : IsCyclic A :=
        isCyclic_of_surjective
          (QuotientGroup.quotientBot (G := A))
          (QuotientGroup.quotientBot (G := A)).surjective
      exact hncyc hcycA
    obtain ⟨a, ha_ne_one⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hY_ne_bot
    have ha_ne_one' : (a : A) ≠ 1 := by
      intro ha1
      exact ha_ne_one (Subtype.ext (by simpa using ha1))
    have hzpow_le : Subgroup.zpowers (a : A) ≤ Y := (Subgroup.zpowers_le).2 a.2
    have hfix_le :
        fixedPointSubgroup (↥Y) G ≤ fixedPointSubgroup (↥(Subgroup.zpowers (a : A))) G := by
      intro g hg
      rw [FixedPoints.mem_subgroup] at hg ⊢
      intro z
      change ((z : A) • g) = g
      exact hg (⟨z, hzpow_le z.2⟩ : Y)
    exact le_iSup_of_le (a : A) (le_iSup_of_le ha_ne_one' hfix_le)
  have htop_le :
      (⊤ : Subgroup G) ≤ (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) G) := by
    calc
      (⊤ : Subgroup G) =
          (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), fixedPointSubgroup (↥Y) G) := hcyc.symm
      _ ≤ (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) G) := hle
  exact top_le_iff.mp htop_le
