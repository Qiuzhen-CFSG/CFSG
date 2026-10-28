module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.Reduction
public import Theory.SpecificGroups.OddThreeRank
public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.GroupTheory.PrimeRankHom

/-!
# Outer elementary actors in the literal PSL₃ graph extension

The quotient by the marked inner subgroup has order dividing two. Combining
this exact quotient calculation with the checked inner two-rank bound shows
that every large elementary actor has order four or eight. An outer actor
has an inner intersection of half its order. A proper weak-closure normalizer
ensures that there is a nontrivial actor in the original family.

These facts preserve the actual family and quotient maps; intersections are
never declared to be family members. They prepare the two local construction
branches of Aschbacher--Smith E.1.14(7), printed p.214, with E.1.1--5 on
pp.209--210 and A.2.3(2) on p.33. The local E-members are separate obligations.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

omit [Finite F] [IsSimpleGroup PSL(3,F)] in
/-- The literal quotient of the inner-and-graph join has order dividing two. -/
theorem quotient_card_dvd_two : Nat.card (graphExtension F ⧸ innerPart F) ∣ 2 := by
  change (MulAut.innerSubgroup PSL(3,F)).relIndex (graphExtension F) ∣ 2
  rw [graphExtension, relIndex_sup_left]
  exact (relIndex_dvd_card _ _).trans (by
    simpa only [Nat.card_zpowers] using
      orderOf_dvd_of_pow_eq_one (Matrix.PSL3.OuterSolvable.graph_sq F))

omit [IsSimpleGroup PSL(3,F)] in
/-- The quotient contributes at most one elementary generator. -/
theorem quotient_primeRank_le_one : primeRank 2 (graphExtension F ⧸ innerPart F) ≤ 1 := by
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro A _
  exact (Nat.card_le_card_of_injective A.subtype A.subtype_injective).trans
    (Nat.le_of_dvd (by decide) (quotient_card_dvd_two F))

/-- The two-rank bound includes outer actors in the actual graph extension. -/
theorem ambient_primeRank_le_three {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p) :
    primeRank 2 (graphExtension F) ≤ 3 := by
  have hi : primeRank 2 (innerPart F) ≤ 2 :=
    (primeRank_equiv 2 (innerPartEquiv F)).symm.le.trans
      (Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le hp ho hF)
  have h := primeRank_le_ker_add (p := 2) (QuotientGroup.mk' (innerPart F))
  rw [QuotientGroup.ker_mk'] at h
  exact h.trans (Nat.add_le_add hi (quotient_primeRank_le_one F))

omit [IsSimpleGroup PSL(3,F)] in
/-- Every subgroup outside the inner part has index two over its inner intersection. -/
theorem outer_intersection_card (A : Subgroup (graphExtension F))
    (hout : ¬ A ≤ innerPart F) :
    Nat.card (A ⊓ innerPart F : Subgroup (graphExtension F)) * 2 = Nat.card A := by
  let q := QuotientGroup.mk' (innerPart F)
  have hne : A.map q ≠ ⊥ := by
    intro h
    apply hout
    intro x hx
    exact (QuotientGroup.eq_one_iff _).mp (mem_bot.mp (h ▸ mem_map_of_mem q hx))
  let : Nontrivial (A.map q) := (nontrivial_iff_ne_bot _).mpr hne
  have hlo : 2 ≤ Nat.card (A.map q) := Finite.one_lt_card
  have hhi : Nat.card (A.map q) ≤ 2 :=
    (Nat.card_le_card_of_injective (A.map q).subtype (A.map q).subtype_injective).trans
      (Nat.le_of_dvd (by decide) (quotient_card_dvd_two F))
  have hc : Nat.card (A.map q) = 2 := by omega
  simpa only [q, QuotientGroup.ker_mk', hc] using
    IsElementaryAbelian.card_inf_ker_mul_card_map A q


/-- A large elementary actor has order four or eight. -/
theorem large_actor_card {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p) (A : Subgroup (graphExtension F))
    [IsElementaryAbelian 2 A] (hlarge : 1 < Group.rank A) :
    Nat.card A = 4 ∨ Nat.card A = 8 := by
  have hc : Nat.card A ≤ 2 ^ 3 :=
    (primeRank_le_iff_elementary_card_le _).mp
      (ambient_primeRank_le_three F hp ho hF) A inferInstance
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hnle : n ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hn ▸ hc)
  have hnlo : 2 ≤ n := by
    by_contra h
    have hn1 : n ≤ 1 := by omega
    have hc1 : Nat.card A ≤ 2 ^ 1 := by
      rw [hn]
      exact pow_le_pow_right' (by decide) hn1
    have hr := IsElementaryAbelian.rank_le_of_card_le A hc1
    omega
  have hncase : n = 2 ∨ n = 3 := by omega
  rcases hncase with rfl | rfl
  · exact Or.inl hn
  · exact Or.inr hn

omit [Finite F] [IsSimpleGroup PSL(3,F)] in
/-- The proper-normalizer assumption rules out a family with only trivial actors. -/
theorem exists_nontrivial_actor (T : Sylow 2 (graphExtension F))
    (Ω : Set (Subgroup (graphExtension F))) (M : Subgroup (graphExtension F))
    (hM : M ≠ ⊤)
    (hN : normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) ≤ M) :
    ∃ A ∈ Ω, A ≤ (T : Subgroup _) ∧ A ≠ ⊥ := by
  classical
  by_contra! h
  have hW : weakClosure (T : Subgroup _) Ω = ⊥ := by
    apply le_bot_iff.mp
    apply sSup_le
    intro A hA
    exact (h A hA.1 hA.2).le
  rw [hW, normalizer_eq_top] at hN
  exact hM (top_unique hN)

/-- With trivial ambient two-core, tau centralizes every actual actor element. -/
theorem tau_le_centralizer_element (T A : Subgroup (graphExtension F))
    {t : graphExtension F} (ht : t ∈ A) :
    tau T A ≤ centralizer ({t} : Set (graphExtension F)) := by
  intro x hx
  have hc := (mem_centralizerModulo_iff.mp hx).2 t ht
  rw [twoCore_eq_bot F, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact mem_centralizer_singleton_iff.mpr hc.symm

/-- Select a genuine outer actor, its inner-intersection size, and an outer
involution centralized by both the actor and ambient tau. -/
theorem exists_large_outer_actor {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p) (T : Sylow 2 (graphExtension F))
    (Ω : Set (Subgroup (graphExtension F))) (hΩ : IsElementaryFamily Ω)
    (hlarge : LargeActors F T Ω) (houter : ¬ HasInnerActor F T Ω)
    (M : Subgroup (graphExtension F)) (hM : M ≠ ⊤)
    (hN : normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) ≤ M) :
    ∃ A ∈ Ω, A ≤ (T : Subgroup _) ∧ A ≠ ⊥ ∧
      ((Nat.card A = 4 ∧ Nat.card (A ⊓ innerPart F : Subgroup _) = 2) ∨
       (Nat.card A = 8 ∧ Nat.card (A ⊓ innerPart F : Subgroup _) = 4)) ∧
      ∃ t : graphExtension F, t ∈ A ∧ t ∉ innerPart F ∧ orderOf t = 2 ∧
        A ≤ centralizer ({t} : Set _) ∧
        tau (T : Subgroup _) A ≤ centralizer ({t} : Set _) := by
  obtain ⟨A, hA, hAT, hne⟩ := exists_nontrivial_actor F T Ω M hM hN
  let := hΩ.1 A hA
  have hout : ¬ A ≤ innerPart F := fun h => houter ⟨A, hA, hAT, hne, h⟩
  have hdouble := outer_intersection_card F A hout
  have hcard := large_actor_card F hp ho hF A (hlarge A hA hAT hne)
  have hcases :
      (Nat.card A = 4 ∧ Nat.card (A ⊓ innerPart F : Subgroup _) = 2) ∨
      (Nat.card A = 8 ∧ Nat.card (A ⊓ innerPart F : Subgroup _) = 4) := by omega
  obtain ⟨t, htA, htL⟩ := SetLike.not_le_iff_exists.mp hout
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t htA
  refine ⟨A, hA, hAT, hne, hcases, t, htA, htL,
    orderOf_eq_prime ht2 (fun h => htL (h ▸ (innerPart F).one_mem)), ?_,
    tau_le_centralizer_element F _ _ htA⟩
  intro a ha
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val ((hΩ.1 A hA).is_comm.comm (⟨a, ha⟩ : A) ⟨t, htA⟩))

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
