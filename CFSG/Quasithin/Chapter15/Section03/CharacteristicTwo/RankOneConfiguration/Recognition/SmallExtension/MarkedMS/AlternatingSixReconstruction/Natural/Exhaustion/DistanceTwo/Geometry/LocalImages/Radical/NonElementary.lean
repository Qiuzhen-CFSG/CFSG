module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.Radical.Model
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.Basic
public import Theory.GroupTheory.NormalizedSupCard
/-!
# The remaining proper non-elementary radical image

A binary subgroup of S₆ with a central transposition is either elementary,
of order sixteen, or the internal product of a cyclic four-group and that
transposition. Conjugation into the existing sixteen-element Sylow model
bounds element orders and separates the transposition from the cyclic
four-group. The product then has order eight and fills every proper
non-elementary possibility.

Assembly.ResidualImages.Source applies this calculation to the literal
replacement projection and the whole-core exhaustion consumer. This is a
reduction of the unfinished source cases, not their exclusion.
Source context: MS93 (3.3), (3.6), printed pp.866--871.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
private instance (t : Six.Perm) : Decidable t.IsSwap := by
  unfold Equiv.Perm.IsSwap
  infer_instance
private theorem fourth_table : ∀ i : Fin 16, Six.sylowWords i ^ 4 = 1 := by
  decide +kernel
private theorem independent_table : ∀ i j : Fin 16,
    (Six.sylowWords j).IsSwap → Six.sylowWords i ^ 2 ≠ 1 →
      ∀ n : Fin 4, Six.sylowWords i ^ n.val ≠ Six.sylowWords j := by
  decide +kernel

private theorem binary_card_le_eight
    (B : Subgroup Six.Perm) (hp : IsPGroup 2 B) (h16 : Nat.card B ≠ 16) :
    Nat.card B ≤ 8 := by
  classical
  obtain ⟨P,hBP⟩ := hp.exists_le_sylow
  have hPc : Nat.card (P : Subgroup Six.Perm) = 16 := by
    rw [P.card_eq_multiplicity,Nat.card_perm,Nat.card_fin]
    decide +kernel
  have hB16 := (card_le_of_le hBP).trans_eq hPc
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hn4 : n < 4 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    change 2^n < 16
    omega
  rw [hn]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n ≤ 3)

private theorem exists_nonsquare (B : Subgroup Six.Perm)
    (hne : ¬ IsElementaryAbelian 2 B) : ∃ a ∈ B, a ^ 2 ≠ 1 := by
  classical
  by_contra! hs
  have hpow : ∀ x : B, x ^ 2 = 1 := fun x => Subtype.ext (hs x x.property)
  exact hne {
    toIsMulCommutative := ⟨⟨fun a b =>
      Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (hpow x)) a b⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }

/-- The non-elementary proper binary image with a central transposition is
literally the internal product of a cyclic four-group and that transposition. -/
theorem cyclic_four_times_swap_of_non_elementary
    (B : Subgroup Six.Perm) (hp : IsPGroup 2 B) (h16 : Nat.card B ≠ 16)
    (t : Six.Perm) (ht : t.IsSwap) (htB : t ∈ B)
    (hcent : ∀ b ∈ B, t*b=b*t) (hne : ¬ IsElementaryAbelian 2 B) :
    ∃ a ∈ B, orderOf a = 4 ∧
      B = zpowers a ⊔ zpowers t ∧ Disjoint (zpowers a) (zpowers t) ∧
      Commute a t ∧ Nat.card B = 8 := by
  classical
  obtain ⟨a,ha,ha2⟩ := exists_nonsquare B hne
  obtain ⟨P,hBP⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Six.Perm P Six.sylow
  let c := (MulAut.conj g).toMonoidHom
  have hBs {x : Six.Perm} (hx : x ∈ B) : c x ∈ Six.sylowCarrier := by
    change (MulAut.conj g) x ∈ (Six.sylow : Subgroup Six.Perm)
    rw [←hg]
    exact mem_map_of_mem _ (hBP hx)
  obtain ⟨i,hi⟩ := (Six.mem_sylowCarrier_iff _).mp (hBs ha)
  obtain ⟨j,hj⟩ := (Six.mem_sylowCarrier_iff _).mp (hBs htB)
  have ha4 : a ^ 4 = 1 := by
    apply (MulAut.conj g).injective
    change c (a^4) = c 1
    rw [map_pow,map_one,←hi]
    exact fourth_table i
  have hoa : orderOf a = 4 := by
    have hd := orderOf_dvd_of_pow_eq_one ha4
    have hn : ¬ orderOf a ∣ 2 := fun hh => ha2 ((orderOf_dvd_iff_pow_eq_one).mp hh)
    have hh : orderOf a = 1 ∨ orderOf a = 2 ∨ orderOf a = 4 := by
      obtain ⟨k,hk,hval⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        (show orderOf a ∣ 2^2 from hd)
      interval_cases k
      · exact Or.inl hval
      · exact Or.inr (Or.inl hval)
      · exact Or.inr (Or.inr hval)
    rcases hh with h1 | h2 | h4
    · exact (hn (by rw [h1];decide)).elim
    · exact (hn (by rw [h2])).elim
    · exact h4
  have htc : (c t).IsSwap := by
    obtain ⟨x,y,hxy,rfl⟩ := ht
    change (g * Equiv.swap x y * g⁻¹).IsSwap
    rw [←Equiv.swap_apply_apply]
    exact ⟨g x,g y,g.injective.ne hxy,rfl⟩
  have hc2 : (c a)^2 ≠ 1 := by
    intro hh
    apply ha2
    apply (MulAut.conj g).injective
    change c (a^2) = c 1
    simpa only [map_pow,map_one] using hh
  have htn : t ∉ zpowers a := by
    intro hh
    rw [mem_zpowers_iff_mem_range_orderOf,hoa] at hh
    obtain ⟨n,hn,hval⟩ := Finset.mem_image.mp hh
    have hnn := Finset.mem_range.mp hn
    have he := congrArg c hval
    rw [map_pow,←hi,←hj] at he
    exact independent_table i j (hj ▸ htc) (hi ▸ hc2) ⟨n,hnn⟩ he
  have hdisj : Disjoint (zpowers a) (zpowers t) := disjoint_def.mpr (by
    intro x hxa hxt
    rw [mem_zpowers_iff_mem_range_orderOf,ht.orderOf] at hxt
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hxt
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · exact pow_zero _
    · exact (htn (by simpa only [pow_one] using hxa)).elim)
  have hcomm : Commute a t := (hcent a ha).symm
  have hnorm : zpowers t ≤ normalizer (zpowers a : Set Six.Perm) := by
    apply zpowers_le.mpr
    apply Subgroup.centralizer_le_normalizer
    exact centralizer_le (zpowers_le.mpr ha) (fun b hb => (hcent b hb).symm)
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes (zpowers a) (zpowers t) hnorm
  rw [Nat.card_zpowers,Nat.card_zpowers,hoa,ht.orderOf,hdisj.eq_bot,card_bot,one_mul] at hc
  have hle : zpowers a ⊔ zpowers t ≤ B := sup_le (zpowers_le.mpr ha) (zpowers_le.mpr htB)
  have h8 : Nat.card B = 8 := Nat.le_antisymm (binary_card_le_eight B hp h16)
    (by have hh := card_le_of_le hle; rw [←hc] at hh; exact hh)
  refine ⟨a,ha,hoa,?_,hdisj,hcomm,h8⟩
  exact (eq_of_le_of_card_ge hle (by rw [h8,←hc])).symm
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
