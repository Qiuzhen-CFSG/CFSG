module

public import Stellmacher.SectionFiveToSeven.Result5_1

/-!
# A strict Hypothesis Two pair in the unique-maximal branch

Every pair satisfying (5.1) under a unique maximal two-local over the ambient
Sylow has a strictly smaller common subgroup. If that subgroup were the whole
Sylow, both local members would lie in the unique maximum M. Its two-core lies
in the Sylow and is normal in the pair join, contradicting the trivial core of
that join and characteristic two of M.

Consequently the actual unique-branch witness of (5.1), together with the
all-two-local hypotheses of the reduced Theorem 2 setting, supplies Hypothesis
Two with the strict inclusion required for cases (I) and (II).

Source: refs/latex/stellmacher-n-group.tex, (5.1)(c) and Section 11.
-/
namespace Stellmacher.SectionEleven

open SectionsFiveToSeven

universe u

variable {H : Type u} [Group H] [Finite H]

omit [Finite H] in
private theorem core_le_normalizer (P : Subgroup H) :
    P ≤ Subgroup.normalizer (twoCoreIn P : Set H) := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (show twoCoreIn P ≤ P from Subgroup.map_subtype_le _)).mp
  change (Subgroup.comap P.subtype ((pCore 2 P).map P.subtype)).Normal
  rw [Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  infer_instance

omit [Finite H] in
private theorem normal_two_le_core (Q P : Subgroup H)
    (hQP : Q ≤ P) (hQp : IsPGroup 2 Q)
    (hQnormal : (Q.subgroupOf P).Normal) : Q ≤ twoCoreIn P := by
  have hQpP : IsPGroup 2 (Q.subgroupOf P) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm
  have hle : Q.subgroupOf P ≤ pCore 2 P := le_sSup ⟨hQnormal, hQpP⟩
  calc
    Q = (Q.subgroupOf P).map P.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hQP).symm
    _ ≤ (pCore 2 P).map P.subtype := Subgroup.map_mono hle

private theorem family_le_unique_maximal
    (S0 : Sylow 2 H) (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M)
    (P : Subgroup H) (hP : P ∈ PFamily (⊤ : Subgroup H) (S0 : Subgroup H)) :
    P ≤ M := by
  have hlocal : IsTwoLocal (Subgroup.normalizer (twoCoreIn P : Set H)) :=
    ⟨twoCoreIn P, hP.1.2.2.1,
      (pCore_isPGroup (p := 2) (G := P)).map P.subtype, rfl⟩
  obtain ⟨N, hNle, hNmax⟩ := Finite.exists_le_maximal hlocal
  have hPN : P ≤ N := (core_le_normalizer P).trans hNle
  exact hM.2 N ⟨hNmax, hP.1.2.1.1.trans hPN⟩ ▸ hPN

public theorem fiveOne_ne_sylow_of_unique_maximal
    {S0 : Sylow 2 H} {S P1 P2 M : Subgroup H}
    (h : HypothesisOne H S0)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M)
    (hfive : FiveOneConditions H S0 S P1 P2) :
    S ≠ (S0 : Subgroup H) := by
  intro heq
  subst S
  have hP1M := family_le_unique_maximal S0 M hM P1 hfive.P1_mem
  have hP2M := family_le_unique_maximal S0 M hM P2 hfive.P2_mem
  have hJM : P1 ⊔ P2 ≤ M := sup_le hP1M hP2M
  have hQS : twoCoreIn M ≤ (S0 : Subgroup H) := by
    have hle := Subgroup.map_mono (f := M.subtype)
      ((pCore_isPGroup (p := 2) (G := M)).le_sylow_of_normal (S0.subtype hM.1.2))
    change twoCoreIn M ≤ ((S0 : Subgroup H).subgroupOf M).map M.subtype at hle
    rwa [Subgroup.map_subgroupOf_eq_of_le hM.1.2] at hle
  have hQJ : twoCoreIn M ≤ P1 ⊔ P2 :=
    hQS.trans (hfive.P1_mem.1.2.1.1.trans le_sup_left)
  have hQcore : twoCoreIn M ≤ twoCoreIn (P1 ⊔ P2) :=
    normal_two_le_core _ _ hQJ
      ((pCore_isPGroup (p := 2) (G := M)).map M.subtype)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQJ).mpr
        (hJM.trans (core_le_normalizer M)))
  have hQbot : pCore 2 M = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp
    exact le_bot_iff.mp (hQcore.trans hfive.join_twoCore_eq_bot.le)
  have hchar := (h.local_solvable_characteristicTwo M hM.1.1.1 hM.1.2).2
  have hMbot : M = ⊥ := by
    apply le_bot_iff.mp
    intro element helement
    have hcent : (⟨element, helement⟩ : M) ∈
        Subgroup.centralizer (pCore 2 M : Set M) := by
      rw [hQbot, Subgroup.mem_centralizer_iff]
      intro other hother
      have hotherOne : other = 1 := hother
      simp only [hotherOne, one_mul, mul_one]
    have helementOne : (⟨element, helement⟩ : M) = 1 := by
      have hmem := hchar hcent
      rwa [hQbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val helementOne
  exact hfive.S_nontrivial (le_bot_iff.mp (hM.1.2.trans hMbot.le))


public theorem exists_unique_hypothesis_two
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (hLocal : ∀ U : Subgroup H, IsTwoLocal U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    ∃ S P1 P2 : Subgroup H,
      HypothesisTwo H S0 S P1 P2 ∧ S < (S0 : Subgroup H) := by
  obtain ⟨S, P1, P2, hfive⟩ := five_one_unique_branch S0 h M hM
  refine ⟨S, P1, P2, ⟨h, hfive, fun U hU _ => hLocal U hU⟩, ?_⟩
  exact lt_of_le_of_ne hfive.S_le_S0 (fiveOne_ne_sylow_of_unique_maximal h hM hfive)


end Stellmacher.SectionEleven
