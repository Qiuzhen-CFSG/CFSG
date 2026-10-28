module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.RankOneCovers
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.SpecificGroups.ReeF4.OddSupplement
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.LocalIdentification
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.PerfectSeeds
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.TwoLocalOrders

/-!
# Placing the actual Ree local component

A proper local C-component normalized by a full Sylow two-subgroup has a
proper join with that Sylow subgroup. Align the Sylow subgroup with the
unipotent group and apply the proved full-Sylow overgroup theorem. When
three divides the component order, the three-free Suzuki parabolic is
excluded. Perfectness places the component in the linear residual, and
the local-component theorem for its SL₂ quotient identifies the two.

The output is a literal conjugacy of subgroups, consumed by RankTwo.Ree.
Source: Aschbacher–Smith A.3.12, F.1.12 and 10.2.9,
printed pp.47–48,263–264,750–751.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo.ReePlacement
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings.FiveLocalFF
noncomputable section

private theorem perfect_le_local {m : ℕ} (s : Side)
    (B : Subgroup (Model m)) [Group.IsPerfect B] (hB : B ≤ parabolic m s) :
    B ≤ localFactor m s := by
  let P := parabolic m s
  let N := (localFactor m s).subgroupOf P
  let H := (borel m).subgroupOf P
  let : Group.IsSolvable (borel m) := OddSupplement.borel_isSolvable m
  let : Group.IsSolvable H := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (borel_le_parabolic m s)).toMonoidHom)
    (subgroupOfEquivOfLe (borel_le_parabolic m s)).injective
  have hsup : N ⊔ H = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (localFactor_le_parabolic m s),
      map_subgroupOf_eq_of_le (borel_le_parabolic m s),
      ← parabolic_eq_localFactor_sup_borel, ← MonoidHom.range_eq_map, range_subtype]
  let q := QuotientGroup.mk' N
  have hq : Function.Surjective (q.comp H.subtype) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, range_subtype]
    have hNq : N.map q = ⊥ := (map_eq_bot_iff N).mpr (by rw [QuotientGroup.ker_mk'])
    have hh := congrArg (map q) hsup
    simpa only [Subgroup.map_sup, hNq, bot_sup_eq,
      map_top_of_surjective q (QuotientGroup.mk'_surjective N)] using hh
  let : Group.IsSolvable (P ⧸ N) := Group.isSolvable_of_surjective hq
  let : Group.IsPerfect (B.subgroupOf P) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hB).symm.toMonoidHom) (subgroupOfEquivOfLe hB).symm.surjective
  have hh := le_of_isPerfect_of_solvable_quotient (B.subgroupOf P) N
  intro x hx
  exact hh (show (⟨x,hB hx⟩ : P) ∈ B.subgroupOf P from hx)

/-- Three-divisibility singles out the actual linear residual after full-Sylow alignment. -/
theorem local_placement {m : ℕ} (hm : 1 ≤ m) [IsSimpleGroup (Model m)]
    (S : Sylow 2 (Model m)) (B : Subgroup (Model m))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (hSN : (S : Subgroup (Model m)) ≤ normalizer (B : Set (Model m)))
    (h3 : 3 ∣ Nat.card B) :
    ∃ g : Model m, B.map (MulAut.conj g).toMonoidHom = localFactor m .linear := by
  have hjoin : B ⊔ (S : Subgroup (Model m)) ≠ ⊤ := by
    intro ht
    have hc : B.Normal := normalizer_eq_top_iff.mp (by
      apply top_unique
      rw [← ht]
      exact sup_le B.le_normalizer hSN)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B hc with hb | ht
    · have hcard : Nat.card B = 1 := by rw [hb, card_bot]
      rw [hcard] at h3
      norm_num at h3
    · exact hproper ht
  obtain ⟨g,hg⟩ := ReeF4.Parabolics.ThreeSylowContainment.exists_conjugate_eq_unipotent S
  let a := MulAut.conj g
  let R := S.mapSurjective (f := a.toMonoidHom) a.surjective
  have hR : (R : Subgroup (Model m)) = unipotent m := hg
  let C := B.map a.toMonoidHom
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  have hC : C ∈ localCComponents R :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB a.toMonoidHom
  let := hC.perfect
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show C ≤ C ⊔ (R : Subgroup _) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  have hproper' : (B ⊔ (S : Subgroup (Model m))).map a.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hjoin
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [ht, map_top_of_surjective _ a.surjective]
  have hU : unipotent m ≤ (B ⊔ (S : Subgroup (Model m))).map a.toMonoidHom :=
    hg ▸ map_mono (show (S : Subgroup _) ≤ B ⊔ (S : Subgroup _) from le_sup_right)
  obtain ⟨s,hs⟩ := OddSupplement.le_parabolic m hm _ hU hproper'
  rw [ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.parabolic_eq_rootParabolic] at hs
  have hCP : C ≤ parabolic m s := (map_mono le_sup_left).trans hs
  cases s with
  | suzuki =>
    have hd := card_dvd_of_le hCP
    have h3C : 3 ∣ Nat.card C := by rwa [card_map_of_injective a.injective]
    have hn := ConverseParabolics.suzuki_parabolic_three_free hm
    rw [MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.parabolic_eq_rootParabolic] at hn
    exact (hn (h3C.trans hd)).elim
  | linear =>
    refine ⟨g, ?_⟩
    let := OuterLocal.localFactor_perfect hm Side.linear
    apply local_eq_of_sl2_core_quotient (localFactor m .linear) (F := CoefficientField m) ?_
      ((linearLocalQuotientEquiv m).trans
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := CoefficientField m)).symm)
      R C hC (perfect_le_local .linear C hCP)
    · rw [hR]
      exact unipotent_le_localFactor m .linear
    · rw [field_card]
      exact lt_of_lt_of_le (by decide : 2 < 2 ^ 3)
        (Nat.pow_le_pow_right (by decide) (by omega))

end
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo.ReePlacement
