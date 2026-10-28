module
public import Theory.GroupTheory.NoncentralChiefRefinement.CentralChiefInterval
/-!
# Counting a unique noncentral chief interval

Refine a central initial stratum and two outer intervals whose individual
chief factors are central, then concatenate them around a prescribed
noncentral chief interval. Equivariant Jordan–Hölder transfers the resulting
count of one to every series on the same normal two-subgroup. The outer
intervals need not themselves be central.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
15.2.27(2), printed p.1119, where a marked actor detects every noncentral
chief factor and fixes the outer intervals.
-/

public section
open Subgroup
namespace NoncentralChiefRefinement
variable {K : Type*} [Group K]

/-- A stratum with only central chief factors has zero noncentral count. -/
theorem ChiefSeries.noncentralTwoCount_eq_zero_of_central_chief_intervals
    (s : ChiefSeries K)
    (hc : ∀ A B : NormalNode K, s.head ≤ A → B ≤ s.last → A ⋖ B → IsCentral A B) :
    s.noncentralTwoCount = 0 := by
  apply Nat.card_eq_zero.mpr
  exact Or.inl ⟨fun i => i.property.2
    (hc _ _ (s.head_le _) (s.le_last _) (s.step i.val))⟩

variable [Finite K]

/-- A single noncentral interval accounts for the count when all three
remaining strata have central chief factors. -/
theorem SeriesOn.noncentralCount_eq_one_of_central_chief_intervals
    {Q : Subgroup K} [Q.Normal] (hp : IsPGroup 2 Q)
    (Z A B : NormalNode K) (hZ : IsCentral ⊥ Z) (hZA : Z ≤ A)
    (hAB : A ⋖ B) (hn : ¬ IsCentral A B) (hBQ : B.val ≤ Q)
    (hlo : ∀ C D : NormalNode K, Z ≤ C → D ≤ A → C ⋖ D → IsCentral C D)
    (hhi : ∀ C D : NormalNode K, B ≤ C → D.val ≤ Q → C ⋖ D → IsCentral C D)
    (s : SeriesOn Q) : s.noncentralCount = 1 := by
  obtain ⟨z,hz0,hz1⟩ := exists_chiefSeries (⊥ : NormalNode K) Z bot_le
  obtain ⟨a,ha0,ha1⟩ := exists_chiefSeries Z A hZA
  let b : ChiefSeries K := (RelSeries.singleton _ A).snoc B hAB
  obtain ⟨c,hc0,hc1⟩ := exists_chiefSeries B ⟨Q,inferInstanceAs Q.Normal⟩ hBQ
  have hza : z.last = a.head := hz1.trans ha0.symm
  have hab : (z.smash a hza).last = b.head := (RelSeries.last_smash hza).trans ha1
  have hbc : ((z.smash a hza).smash b hab).last = c.head :=
    (RelSeries.last_smash hab).trans ((RelSeries.last_snoc _ _ _).trans hc0.symm)
  have hz : z.noncentralTwoCount = 0 := by
    apply z.noncentralTwoCount_eq_zero_of_central
    rwa [hz0,hz1]
  have ha : a.noncentralTwoCount = 0 := by
    apply a.noncentralTwoCount_eq_zero_of_central_chief_intervals
    rwa [ha0,ha1]
  have hb : b.noncentralTwoCount = 1 := by
    change Nat.card {i : Fin 1 // IsNoncentralTwo (b i.castSucc) (b i.succ)} = 1
    apply Nat.card_eq_one_iff_exists.mpr
    have hi : IsNoncentralTwo (b (0 : Fin 1).castSucc) (b (0 : Fin 1).succ) := by
      change IsNoncentralTwo A B
      exact ⟨(hp.to_le hBQ).to_quotient _,hn⟩
    exact ⟨⟨0,hi⟩,fun i => Subtype.ext (Subsingleton.elim _ _)⟩
  have hc : c.noncentralTwoCount = 0 := by
    apply c.noncentralTwoCount_eq_zero_of_central_chief_intervals
    rwa [hc0,hc1]
  rw [s.noncentralCount_eq_twoCount hp,
    s.series.noncentralTwoCount_eq (((z.smash a hza).smash b hab).smash c hbc)
      (by simpa using s.head_eq.trans hz0.symm)
      (by simpa using s.last_eq.trans hc1.symm),
    ChiefSeries.noncentralTwoCount_smash,ChiefSeries.noncentralTwoCount_smash,
    ChiefSeries.noncentralTwoCount_smash,hz,ha,hb,hc]

end NoncentralChiefRefinement
