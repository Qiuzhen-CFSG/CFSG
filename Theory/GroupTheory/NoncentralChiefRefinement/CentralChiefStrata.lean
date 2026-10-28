module

public import Theory.GroupTheory.NoncentralChiefRefinement.Accounting

/-!
# Accounting with central binary chief strata

A coarse interval may have nontrivial action while all its binary chief
sections are central. Such an interval contributes zero to the noncentral
binary chief count. This extends homogeneous-module accounting without
requiring that the entire interval be central or elementary abelian.
In particular a terminal quotient may have central binary chief factors.

Refine each stratum and concatenate the resulting actual chief series.
Equivariant Jordan–Hölder then transports the count and module coordinates.
Source application: Aschbacher–Smith, 14.7.71(1), printed p.1075.
-/

public section
open Subgroup
namespace NoncentralChiefRefinement
variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) K V} {A B : NormalNode K}

/-- A stratum either has only central binary chief sections, or is an actual
homogeneous binary module section with the specified multiplicity. -/
@[expose] def IsChiefModuleStratum (ρ : Representation (ZMod 2) K V)
    (A B : NormalNode K) (m : ℕ) : Prop :=
  ((∀ C D : NormalNode K, A ≤ C → D ≤ B → C ⋖ D →
      IsPGroup 2 (Section C D) → IsCentral C D) ∧ m = 0) ∨
    Nonempty (SectionCoordinates A B ρ m)

/-- Actual chief refinement of a stratum whose binary chief factors are
central, or whose module coordinates are given. -/
theorem IsChiefModuleStratum.exists_chief_refinement [Finite K] {m : ℕ}
    (h : IsChiefModuleStratum ρ A B m) (hAB : A ≤ B)
    [Representation.IsIrreducible ρ] (hρ : ∃ k v, ρ k v ≠ v) :
    ∃ s : ChiefSeries K, s.head = A ∧ s.last = B ∧ s.noncentralTwoCount = m ∧
      ∀ i : Fin s.length, IsNoncentralTwo (s i.castSucc) (s i.succ) →
        Nonempty (SectionCoordinates (s i.castSucc) (s i.succ) ρ 1) := by
  rcases h with ⟨hc, rfl⟩ | hc
  · obtain ⟨s, hs0, hsl⟩ := exists_chiefSeries A B hAB
    have hz (i : Fin s.length) : ¬ IsNoncentralTwo (s i.castSucc) (s i.succ) := by
      intro hi
      exact hi.2 (hc _ _ (hs0 ▸ s.head_le _) (hsl ▸ s.le_last _) (s.step i) hi.1)
    refine ⟨s, hs0, hsl, ?_, fun i hi => (hz i hi).elim⟩
    exact Nat.card_eq_zero.mpr (Or.inl ⟨fun i => hz i.val i.property⟩)
  · obtain ⟨c⟩ := hc
    obtain ⟨s, hs0, hsl, _, hcount, hf⟩ := c.exists_chief_refinement hAB hρ
    exact ⟨s, hs0, hsl, hcount, fun i _ => (hf i).1⟩

private theorem forall_factors_smash (s t : ChiefSeries K) (hst : s.last = t.head)
    (P : NormalNode K → NormalNode K → Prop)
    (hs : ∀ i : Fin s.length, P (s i.castSucc) (s i.succ))
    (ht : ∀ i : Fin t.length, P (t i.castSucc) (t i.succ)) :
    ∀ i : Fin (s.smash t hst).length,
      P ((s.smash t hst) i.castSucc) ((s.smash t hst) i.succ) := by
  intro i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  rcases j with j | j
  · exact (congrArg₂ P (RelSeries.smash_castAdd hst j)
      (RelSeries.smash_succ_castAdd hst j)).mpr (hs j)
  · exact (congrArg₂ P (RelSeries.smash_natAdd hst j)
      (RelSeries.smash_succ_natAdd hst j)).mpr (ht j)

private theorem exists_chief_strata_refinement_terms [Finite K] [Representation.IsIrreducible ρ]
    (hρ : ∃ k v, ρ k v ≠ v) {n : ℕ} (f : Filtration K n) (m : Fin n → ℕ)
    (hf : ∀ i, IsChiefModuleStratum ρ (f.term i.castSucc) (f.term i.succ) (m i)) :
    ∃ s : ChiefSeries K, s.head = f.term 0 ∧ s.last = f.term (Fin.last n) ∧
      s.noncentralTwoCount = ∑ i, m i ∧
      (∀ i, ∃ j, s j = f.term i) ∧
      ∀ i : Fin s.length, IsNoncentralTwo (s i.castSucc) (s i.succ) →
        Nonempty (SectionCoordinates (s i.castSucc) (s i.succ) ρ 1) := by
  induction n with
  | zero =>
    refine ⟨RelSeries.singleton _ (f.term 0), rfl, rfl, ?_, ?_, ?_⟩
    · simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact Nat.card_eq_zero.mpr (Or.inl ⟨fun i => Fin.elim0 i.val⟩)
    · intro i
      exact ⟨0, congrArg f.term (Fin.ext (by omega))⟩
    · exact fun i => Fin.elim0 i
  | succ n ih =>
    let f' : Filtration K n := ⟨fun i => f.term i.castSucc, fun _ _ h => f.monotone h⟩
    obtain ⟨s, hs0, hsl, hsc, hs, hsa⟩ :=
      ih f' (fun i => m i.castSucc) (fun i => hf i.castSucc)
    obtain ⟨t, ht0, htl, htc, hta⟩ :=
      (hf (Fin.last n)).exists_chief_refinement (f.monotone (Fin.castSucc_le_succ _)) hρ
    have hst : s.last = t.head := hsl.trans ht0.symm
    refine ⟨s.smash t hst, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [RelSeries.head_smash, f', Fin.castSucc_zero] using hs0
    · simpa only [RelSeries.last_smash, Fin.succ_last] using htl
    · rw [ChiefSeries.noncentralTwoCount_smash, hsc, htc, Fin.sum_univ_castSucc]
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · exact ⟨Fin.last _, (RelSeries.last_smash hst).trans htl⟩
      · obtain ⟨j, hj⟩ := hs i
        exact ⟨j.castLE (by simp), (RelSeries.smash_castLE hst j).trans hj⟩
    · exact forall_factors_smash s t hst
        (fun A B => IsNoncentralTwo A B → Nonempty (SectionCoordinates A B ρ 1)) hsa hta

/-- A normal filtration with central binary chief strata or homogeneous
binary module strata has an
actual chief refinement, retaining every coarse term, the sum of multiplicities,
and the specified conjugation action on every noncentral two-chief factor.
Repeated terms and zero multiplicities are allowed. -/
theorem Filtration.exists_chief_strata_refinement [Finite K] [Representation.IsIrreducible ρ]
    {n : ℕ} (f : Filtration K n) (m : Fin n → ℕ)
    (hf : ∀ i, IsChiefModuleStratum ρ (f.term i.castSucc) (f.term i.succ) (m i))
    (hρ : ∃ k v, ρ k v ≠ v) :
    ∃ (s : ChiefSeries K) (ι : Fin (n + 1) →o Fin (s.length + 1)),
      (∀ i, s (ι i) = f.term i) ∧ ι 0 = 0 ∧ ι (Fin.last n) = Fin.last s.length ∧
      s.head = f.term 0 ∧ s.last = f.term (Fin.last n) ∧
      s.noncentralTwoCount = ∑ i, m i ∧
      ∀ i : Fin s.length, IsNoncentralTwo (s i.castSucc) (s i.succ) →
        Nonempty (SectionCoordinates (s i.castSucc) (s i.succ) ρ 1) := by
  classical
  obtain ⟨s, hs0, hsl, hsc, hs, hsa⟩ := exists_chief_strata_refinement_terms hρ f m hf
  let j := fun i => (hs i).choose
  have hj : ∀ i, s (j i) = f.term i := fun i => (hs i).choose_spec
  let ι : Fin (n + 1) →o Fin (s.length + 1) :=
    ⟨j, fun i k hik => s.strictMono.le_iff_le.mp (by rw [hj, hj]; exact f.monotone hik)⟩
  refine ⟨s, ι, hj, ?_, ?_, hs0, hsl, hsc, hsa⟩
  · exact s.injective ((hj 0).trans hs0.symm)
  · exact s.injective ((hj (Fin.last n)).trans hsl.symm)

/-- A chief interval whose endpoints occur in a chief series is already a
single step of that series. -/
theorem ChiefSeries.exists_step_of_covBy (s : ChiefSeries K)
    (A B : NormalNode K) (hAB : A ⋖ B)
    (j k : Fin (s.length + 1)) (hj : s j = A) (hk : s k = B) :
    ∃ i : Fin s.length, s i.castSucc = A ∧ s i.succ = B := by
  have hjk : j < k := s.strictMono.lt_iff_lt.mp (by rw [hj, hk]; exact hAB.lt)
  have hjs : j.val < s.length := by have := k.isLt; change j.val < k.val at hjk; omega
  let i : Fin s.length := ⟨j.val, hjs⟩
  have hi : i.castSucc = j := Fin.ext rfl
  have hiA : s i.castSucc = A := hi ▸ hj
  have hlt : A < s i.succ := hiA ▸ (s.step i).lt
  have hle : s i.succ ≤ B := by
    rw [← hk]
    apply s.strictMono.monotone
    change j.val + 1 ≤ k.val
    exact hjk
  refine ⟨i, hiA, ?_⟩
  exact (hAB.eq_or_eq hlt.le hle).resolve_left hlt.ne'

/-- Once two distinct noncentral binary factors exhaust the computed count,
they are precisely all the counted factors. -/
theorem ChiefSeries.noncentralTwo_iff_eq_or_eq (s : ChiefSeries K)
    (hc : s.noncentralTwoCount = 2) (i j : Fin s.length) (hij : i ≠ j)
    (hi : IsNoncentralTwo (s i.castSucc) (s i.succ))
    (hj : IsNoncentralTwo (s j.castSucc) (s j.succ)) (k : Fin s.length) :
    IsNoncentralTwo (s k.castSucc) (s k.succ) ↔ k = i ∨ k = j := by
  constructor
  · intro hk
    let a : {l : Fin s.length // IsNoncentralTwo (s l.castSucc) (s l.succ)} := ⟨i, hi⟩
    let b : {l : Fin s.length // IsNoncentralTwo (s l.castSucc) (s l.succ)} := ⟨j, hj⟩
    let z : {l : Fin s.length // IsNoncentralTwo (s l.castSucc) (s l.succ)} := ⟨k, hk⟩
    by_cases hki : k = i
    · exact Or.inl hki
    right
    obtain ⟨y, _, hy⟩ := (Nat.card_eq_two_iff' a).mp hc
    have hb : b ≠ a := fun h => hij (congrArg Subtype.val h).symm
    have hz : z ≠ a := fun h => hki (congrArg Subtype.val h)
    exact congrArg Subtype.val ((hy z hz).trans (hy b hb).symm)
  · rintro (rfl | rfl)
    · exact hi
    · exact hj

end NoncentralChiefRefinement
