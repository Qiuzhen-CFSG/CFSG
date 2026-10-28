module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.SeedReduction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeExchangedHall
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalFermatRank
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.PairedMarked
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NumericalPairedPrime

/-!
# The original Hall plane in the paired local Cartan branch

Restrict the actual moved seed to H and use E.2.2 to construct its exchanged
marking. The original generation parameter excludes the odd-prime source
row. Its intrinsic PSL₂(4) quotient then makes the prescribed right Hall
subgroup B elementary abelian of order nine. No quotient of the full paired
residual is identified with either factor.

The cyclic left Cartan and odd right Hall normalize and centralize every
cubic subgroup D of A. If D is outside B, their join is E₂₇ in N_G(L),
contrary to quasithinness. Thus any cubic escaping the residual normalizer
excludes the moved seed. Both original Hall conditions are retained.

Source: Aschbacher–Smith E.2.2 and 5.1.13, printed pp.215–216,636–637.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem maximal_eq_overlap {T : Sylow 2 G} {M H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) :
    ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP = M.subgroupOf H := by
  let J := ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP
  have hJ := ChapterB.minimalParabolicMax_spec (T.subtype hH.1.1.2) hP
  have hTJ : (T : Subgroup G) ≤ J.map H.subtype := by
    have hh := map_mono (f := H.subtype) hJ.2
    change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ J.map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hJH : J.map H.subtype < H := by
    have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hJ.1.lt_top
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hh
  have hJM : J ≤ M.subgroupOf H := map_le_iff_le_comap.mp
    (Chapter3.HStar.proper_overgroup_le T hH hTJ hJH)
  have hn : M.subgroupOf H ≠ ⊤ := fun he => hH.1.2 (subgroupOf_eq_top.mp he)
  exact ((hJ.1.le_iff.mp hJM).resolve_left hn).symm

/-- A moved A₅ seed identifies the original right Hall subgroup as E₉. -/
theorem moved_seed_right_hall_plane
    {T : Sylow 2 G} {L W H A B K : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hmoved : K ≠ residual H)
    (hlinear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    IsElementaryAbelian 3 B ∧ Nat.card B = 9 := by
  let C := K.subgroupOf H
  let S := T.subtype hH.1.1.2
  have hP := hstar_minimalParabolic_of_generation_gt_one h.sylow_normalizes hH hpar
  have hmax := maximal_eq_overlap hH hP
  have hQ := Chapter3.sqtk_of_mem_H h.qtke hH.1.1.1
  have hs : ¬ Group.IsSolvable H := by
    intro hh
    let := hh
    exact (Nat.not_le_of_gt hpar) ChapterE.generationParameter_le_one_of_solvable
  have hg : C ⊔ (S : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    change (K.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H).map H.subtype = _
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hKH,
      map_subgroupOf_eq_of_le hH.1.1.2, ← MonoidHom.range_eq_map, range_subtype]
    exact hgen
  have hn : ¬ C.Normal := by
    intro hc
    have ht := hH.1.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hc)
    apply hmoved
    exact (le_antisymm (iSup_conjugates_le_of_le_normalizer K T K le_rfl ht)
      (le_componentOrbit K T)).symm.trans horbit
  let e := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKH))
  have hqc : IsQuasisimple (C ⧸ pCore 2 C) := by
    let := hqs
    exact IsQuasisimple.of_mulEquiv e.symm
  have hAc : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4 := by
    obtain ⟨F, hF, hfin, hcard, ⟨f⟩⟩ := hlinear
    exact ⟨F, hF, hfin, hcard, ⟨e.trans f⟩⟩
  have hc := source_exchanged_clauses
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X)) hQ S hP hs hK hqc hg hn
  obtain ⟨f, _, hm⟩ | ⟨p, hp, _, hseven, hm⟩ := source_exchanged_marked_cases
    ChapterA.Section02.theoremA_knownSimple
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    hQ S hP hs C hK hg hn
  · rw [hmax] at hc hm
    exact c.right_cubic_plane_of_exchanged_A5 h hH hK hqc hc hm hAc
  · let : Fact p.Prime := ⟨hp⟩
    have hh := paired_prime_parameter_le_one ChapterA.Section02.theoremA_knownSimple
      hQ S hP hs C hK hg hn (by omega : 5 < p) hm
    omega

/-- Quasithinness forces every cubic of the actual left Cartan into the right Hall plane. -/
theorem cubic_le_right_of_plane {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (h : Input κ T L W n) (c : CartanPair T L H A B)
    (hB : IsElementaryAbelian 3 B) (hBc : Nat.card B = 9)
    (hDA : D ≤ A) (hDc : Nat.card D = 3) : D ≤ B := by
  classical
  by_contra hDB
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic D := isCyclic_of_prime_card hDc
  let : IsElementaryAbelian 3 D := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun d => by
      simpa only [hDc] using (pow_card_eq_one' (x := d))) }
  let := hB
  have hc := c.centralizes_fermat_actor h (Or.inl rfl) hDA hDc
  have hdis : Disjoint D B := by
    let : Fact (Nat.card D).Prime := ⟨hDc ▸ (by decide : Nat.Prime 3)⟩
    rcases (B.subgroupOf D).eq_bot_or_eq_top_of_prime_card with hb | ht
    · apply disjoint_iff.mpr
      apply eq_bot_iff.mpr
      intro x hx
      have hx' : (⟨x, hx.1⟩ : D) ∈ B.subgroupOf D := hx.2
      rw [hb] at hx'
      exact congrArg Subtype.val (mem_bot.mp hx')
    · exact (hDB (subgroupOf_eq_top.mp ht)).elim
  let : IsElementaryAbelian 3 (D ⊔ B : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hc
  have hcard : Nat.card (D ⊔ B : Subgroup G) = 27 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint D B
      (hc.trans (Subgroup.centralizer_le_normalizer _)) hdis, hDc, hBc]
  let M := normalizer (L : Set G)
  have hJM : D ⊔ B ≤ M := sup_le
    ((hDA.trans c.left_le).trans (inf_le_left.trans L.le_normalizer))
    (c.right_le.trans inf_le_left)
  let : IsElementaryAbelian 3 ((D ⊔ B).subgroupOf M) :=
    IsElementaryAbelian.subgroupOf hJM
  have hsize : Nat.card ((D ⊔ B).subgroupOf M) = 3 ^ 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hJM).toEquiv, hcard]
    norm_num
  have hlower := IsElementaryAbelian.primeRank_ge_of_card ((D ⊔ B).subgroupOf M) hsize
  have hupper := isQuasithin_iff_twoLocal.mp h.qtke.quasithin M h.maximal.1
    3 (by decide) (by decide)
  omega

/-- An escaping cubic excludes the paired seed without assuming a field degree. -/
theorem escape_seed_eq_residual_of_cubic
    {T : Sylow 2 G} {L W H A B K Y D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup G) = H) (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hDA : D ≤ A) (hDc : Nat.card D = 3)
    (hD : ¬ D ≤ normalizer (residual H : Set G)) : K = residual H := by
  by_contra hmoved
  have hlinear := moved_seed_linear_four_of_escape h.qtke hKL hgen horbit hmoved hY hescape
  obtain ⟨hB, hBc⟩ := moved_seed_right_hall_plane h hH hpar c hKH hK hqs
    hgen horbit hmoved hlinear
  exact hD ((cubic_le_right_of_plane h c hB hBc hDA hDc).trans
    ((c.right_le.trans inf_le_right).trans (le_normalizer_residual H)))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
