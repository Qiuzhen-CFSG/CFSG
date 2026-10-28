module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.OrthogonalRestriction
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.NaturalParabolic

/-!
# The complete noncentral two-chief count in13.5.22

Refine the literal filtration of L₁ and concatenate its chief series.
The orthogonal, central, natural and parabolic intervals contribute
1,0,2s,1. The quotient above O₂(L₁) has odd order and contributes zero.
Equivariant Jordan–Hölder then gives the same2s+2 count for every
complete chief series of the original residual. The three-factor
alternative of13.5.24 is therefore impossible.
Source: Aschbacher–Smith13.5.22(2),13.5.24, printed pp.924–925.
-/
public section
open Subgroup NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount
open ChapterG.Section02 ChapterG.Section02.Setup
open ChapterG.Section02.AlternatingFive
open ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

/-- The full count on the literal residual, using the same natural multiplicity. -/
theorem complete_count (d : Hypothesis D g) (hgen : D.I g = D.L)
    [((AlternatingFive.S₂ D g).subgroupOf (D.S g)).Normal]
    {s : ℕ} (c : NaturalLayer D g F4 s d.L_le_I)
    (t : ChiefSeries D.L₁) (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    t.noncentralTwoCount = 2 * s + 2 := by
  obtain ⟨a,ha0,ha1⟩ := exists_chiefSeries (⊥ : NormalNode D.L₁) (first d) bot_le
  obtain ⟨b,hb0,hb1⟩ := exists_chiefSeries (first d) (second d) (first_le_second d)
  obtain ⟨e,he0,he1⟩ := exists_chiefSeries (second d) (core d) (second_le_core d)
  obtain ⟨f,hf0,hf1⟩ := exists_chiefSeries (core d) (localCore D) (core_le_localCore d)
  obtain ⟨z,hz0,hz1⟩ := exists_chiefSeries (localCore D) (⊤ : NormalNode D.L₁) le_top
  have ha := OrthogonalRestriction.count_one d hgen a ha0 ha1
  have hb := middle_count_zero d b hb0 hb1
  have he := natural_upper_count d hgen c e he0 he1
  have hf := parabolic_core_count d f hf0 hf1
  have hz := z.noncentralTwoCount_eq_zero_of_quotient (localCore D) hz0.ge (terminal_no_two d)
  have hab : a.last = b.head := ha1.trans hb0.symm
  have habe : (a.smash b hab).last = e.head :=
    (RelSeries.last_smash hab).trans (hb1.trans he0.symm)
  have habef : ((a.smash b hab).smash e habe).last = f.head :=
    (RelSeries.last_smash habe).trans (he1.trans hf0.symm)
  have habefz : (((a.smash b hab).smash e habe).smash f habef).last = z.head :=
    (RelSeries.last_smash habef).trans (hf1.trans hz0.symm)
  let r : ChiefSeries D.L₁ := (((a.smash b hab).smash e habe).smash f habef).smash z habefz
  have hcount : r.noncentralTwoCount = 2 * s + 2 := by
    simp only [r,ChiefSeries.noncentralTwoCount_smash,ha,hb,he,hf,hz]
    omega
  have hr0 : r.head = ⊥ := by simpa only [r,RelSeries.head_smash] using ha0
  have hr1 : r.last = ⊤ := by simpa only [r,RelSeries.last_smash] using hz1
  exact (t.noncentralTwoCount_eq r (ht0.trans hr0.symm) (ht1.trans hr1.symm)).trans hcount

/-- The actual three-chief-factor alternative contradicts13.5.22. -/
theorem not_three (d : Hypothesis D g) (hgen : D.I g = D.L)
    [((AlternatingFive.S₂ D g).subgroupOf (D.S g)).Normal]
    {s : ℕ} (c : NaturalLayer D g F4 s d.L_le_I)
    (t : ChiefSeries D.L₁) (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    t.noncentralTwoCount ≠ 3 := by
  have hc := complete_count d hgen c t ht0 ht1
  omega

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount
