module
public import Theory.GroupTheory.NoncentralChiefRefinement.CentralQuotient
public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualCentralization
public import Theory.GroupTheory.PCoreSurjective

/-!
# Noncentral chief factors through a central-chief kernel

If every ambient chief factor below a normal subgroup Z is central, quotienting
by Z preserves the number of noncentral chief factors in any normal 2-subgroup
containing Z. A chief series through Z and Jordan–Hölder invariance give the
count identity; the final application uses the literal two-cores before and
after quotienting. This is the chief-factor passage in Niles, *Pushing-up in
finite groups* (1979), Theorem B, printed p.62.
-/

public section
open Subgroup
namespace NoncentralChiefRefinement
variable {H : Type*} [Group H] [Finite H]

theorem SeriesOn.exists_quotient_of_central_chief_kernel
    {U Z : Subgroup H} [U.Normal] [Z.Normal]
    (s : SeriesOn U) (hU : IsPGroup 2 U) (hZU : Z ≤ U)
    (z : SeriesOn Z) (hzc : ∀ i, z.Central i) :
    ∃ t : SeriesOn (U.map (QuotientGroup.mk' Z)),
      s.noncentralCount = t.noncentralCount := by
  let zz : NormalNode H := ⟨Z,inferInstanceAs Z.Normal⟩
  let uu : NormalNode H := ⟨U,inferInstanceAs U.Normal⟩
  obtain ⟨b,hb0,hb1⟩ := exists_chiefSeries zz uu hZU
  have hab : z.series.last = b.head := z.last_eq.trans hb0.symm
  have hz : z.series.noncentralTwoCount = 0 := by
    rw [← z.noncentralCount_eq_twoCount (hU.to_le hZU)]
    exact z.noncentralCount_eq_zero_iff.mpr hzc
  let t : SeriesOn (U.map (QuotientGroup.mk' Z)) := {
    series := b.mapQuotient zz hb0.ge
    head_eq := by
      rw [ChiefSeries.mapQuotient_head,hb0]
      apply Subtype.ext
      change Z.map (QuotientGroup.mk' Z) = ⊥
      exact QuotientGroup.map_mk'_self Z
    last_eq := by
      rw [ChiefSeries.mapQuotient_last,hb1]
      rfl }
  refine ⟨t,?_⟩
  rw [s.noncentralCount_eq_twoCount hU,
    t.noncentralCount_eq_twoCount (hU.map (QuotientGroup.mk' Z))]
  change s.series.noncentralTwoCount = (b.mapQuotient zz hb0.ge).noncentralTwoCount
  rw [ChiefSeries.mapQuotient_noncentralTwoCount]
  calc
    s.series.noncentralTwoCount = ChiefSeries.noncentralTwoCount (z.series.smash b hab) :=
      s.series.noncentralTwoCount_eq _
        (s.head_eq.trans ((RelSeries.head_smash hab).trans z.head_eq).symm)
        (s.last_eq.trans ((RelSeries.last_smash hab).trans hb1).symm)
    _ = b.noncentralTwoCount := by rw [ChiefSeries.noncentralTwoCount_smash,hz,zero_add]

/-- Every prescribed quotient series has the original noncentral count. -/
theorem SeriesOn.noncentralCount_eq_of_central_chief_kernel
    {U Z : Subgroup H} [U.Normal] [Z.Normal]
    (s : SeriesOn U) (hU : IsPGroup 2 U) (hZU : Z ≤ U)
    (z : SeriesOn Z) (hzc : ∀ i, z.Central i)
    (t : SeriesOn (U.map (QuotientGroup.mk' Z))) :
    s.noncentralCount = t.noncentralCount := by
  obtain ⟨r,hr⟩ := s.exists_quotient_of_central_chief_kernel hU hZU z hzc
  rw [hr,r.noncentralCount_eq_twoCount (hU.map (QuotientGroup.mk' Z)),
    t.noncentralCount_eq_twoCount (hU.map (QuotientGroup.mk' Z))]
  exact r.series.noncentralTwoCount_eq t.series (r.head_eq.trans t.head_eq.symm)
    (r.last_eq.trans t.last_eq.symm)

/-- The exact core-count passage in the final paragraph of Niles TheoremB. -/
theorem core_noncentralCount_eq_of_central_chief_kernel
    (Z : Subgroup H) [Z.Normal] (hZ : Z ≤ pCore 2 H)
    (z : SeriesOn Z) (hzc : ∀ i, z.Central i)
    (s : SeriesOn (pCore 2 H)) (t : SeriesOn (pCore 2 (H ⧸ Z))) :
    s.noncentralCount = t.noncentralCount := by
  let q := QuotientGroup.mk' Z
  have hp : IsPGroup 2 q.ker := by
    exact ((pCore_isPGroup (G := H) (p := 2)).to_le hZ).of_equiv
      (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' Z).symm)
  have he : (pCore 2 H).map q = pCore 2 (H ⧸ Z) := by
    rw [← q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective Z) hp,
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z)]
  let t' : SeriesOn ((pCore 2 H).map q) := {
    series := t.series
    head_eq := t.head_eq
    last_eq := t.last_eq.trans (by apply Subtype.ext; exact he.symm) }
  exact s.noncentralCount_eq_of_central_chief_kernel pCore_isPGroup hZ z hzc t'

end NoncentralChiefRefinement
