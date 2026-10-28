module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.ElementaryGeometry.Conjugacy
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.ElementaryGeometry.FiveCommutators
public import Theory.SpecificGroups.Tits.Atlas1600SylowTwo
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.ElementaryGeometry.Centralizers.Certificate

/-!
# Avoidance bounds in both Tits root centralizers

Conjugate an elementary two-subgroup into the certified Sylow subgroup. The
finite certificate bounds its order by 28 if it avoids the s4 class. Its
power-of-two order is therefore at most 16. The certified s4 conjugacy to the
literal five-inverter transports exactly the forbidden class back to Parrott's
group. This proves the required relative-normality bounds for both s1 and s4;
the counting argument in fact does not need the centralizer hypotheses.

These are the `hlong` and `hshort` inputs of
`localGeometry_of_rank_and_root_bounds`. Source: GM04 Lemmas 2.3 and 8.8,
internal pp.6 and 57; Aschbacher–Smith K.3, printed p.457. The finite witness
provenance and the shorter source-compatible route are in `Centralizers/Source.md`.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement.ElementaryGeometry
open Subgroup Tits

private theorem power_two_bound (K : Subgroup Atlas1600Group) (hE : IsElementaryAbelian 2 K)
    (h28 : Nat.card K ≤ 28) : Nat.card K ≤ 16 := by
  let := hE
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 K).exists_card_eq
  rw [hn] at h28 ⊢
  have hn5 : n < 5 := by
    by_contra h
    have h32 : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  calc
    2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 16 := by decide

private theorem atlas_bound (K : Subgroup Atlas1600Group) (hE : IsElementaryAbelian 2 K)
    (havoid : ∀ k ∈ K, ¬ IsConj (atlas1600ParrottAssignment .s4) k) :
    Nat.card K ≤ 16 := by
  let := hE
  obtain ⟨P, hP⟩ := (IsElementaryAbelian.isPGroup 2 K).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Atlas1600Group P atlas1600SylowTwo
  let e := MulAut.conj g
  have hm : (P : Subgroup Atlas1600Group).map e.toMonoidHom =
      atlas1600SylowTwoSubgroup := by
    have hh := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, atlas1600SylowTwo_coe] at hh
    exact hh
  let L := K.map e.toMonoidHom
  have hL : L ≤ atlas1600SylowTwoSubgroup := by
    rw [← hm]
    exact map_mono hP
  have hav : ∀ l ∈ L, ¬ IsConj (atlas1600ParrottAssignment .s4) l := by
    rintro _ ⟨k, hk, rfl⟩ hc
    apply havoid k hk
    apply hc.trans
    apply isConj_iff.mpr
    refine ⟨g⁻¹, ?_⟩
    simp [e, mul_assoc]
  let hEL : IsElementaryAbelian 2 L := IsElementaryAbelian.map e.toMonoidHom
  have h28 := Centralizers.Certificate.card_le_twenty_eight L hL
    (fun k hk => elemPow_eq_one_of_isElementaryAbelian k hk) hav
  have hb := power_two_bound L hEL h28
  simpa only [L, card_map_of_injective (f := e.toMonoidHom) e.injective] using hb

/-- Every elementary two-subgroup avoiding the literal five-inverter class
has order at most sixteen. The finite Sylow certificate supplies the bound. -/
theorem elementary_card_le_of_avoid_fiveInverter (K : Subgroup ParrottGroup)
    (hE : IsElementaryAbelian 2 K)
    (havoid : ∀ k ∈ K, ¬ IsConj fiveInverter k) : Nat.card K ≤ 16 := by
  let := hE
  let e := parrottFiniteImageEquiv
  let L := K.map e.toMonoidHom
  have hav : ∀ l ∈ L, ¬ IsConj (atlas1600ParrottAssignment .s4) l := by
    rintro _ ⟨k, hk, rfl⟩ hc
    have hh : IsConj (parrottGenerator .s4) k := by
      have hp := e.symm.toMonoidHom.map_isConj hc
      simpa only [e, MulEquiv.coe_toMonoidHom, ← parrottFiniteImageEquiv_generator,
        MulEquiv.symm_apply_apply] using hp
    exact havoid k hk (s4_isConj_fiveInverter.symm.trans hh)
  have hb := atlas_bound L (IsElementaryAbelian.map e.toMonoidHom) hav
  simpa only [L, card_map_of_injective (f := e.toMonoidHom) e.injective] using hb

/-- The exact centralizer predicate follows for every marked element.
In particular its original relative-normality hypothesis is preserved. -/
theorem normal_elementary_bound (t : ParrottGroup) : NormalElementaryBound t := by
  intro K _ hE _ havoid
  exact elementary_card_le_of_avoid_fiveInverter K hE havoid

/-- Discharges `hlong` in `localGeometry_of_rank_and_root_bounds`. -/
theorem long_normal_elementary_bound : NormalElementaryBound (parrottGenerator .s1) :=
  normal_elementary_bound _

/-- Discharges `hshort` in `localGeometry_of_rank_and_root_bounds`. -/
theorem short_normal_elementary_bound : NormalElementaryBound (parrottGenerator .s4) :=
  normal_elementary_bound _

end CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement.ElementaryGeometry
