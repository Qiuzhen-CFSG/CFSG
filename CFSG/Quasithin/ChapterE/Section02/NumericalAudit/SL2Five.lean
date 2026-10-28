module
public import CFSG.Quasithin.ChapterE.Section01.ValuesCentral
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.Quotient
public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.ParabolicSections
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.GroupTheory.PrimeRankCubeFree
public import GorensteinWalter.SL2ProjectiveCover
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The central-cover numerical obstruction at SL₂(5)

The actual group SL₂(ZMod 5) has order 120 and is nonsolvable and SQTK for
`KnownSimple.IsKnownSimple`. Its canonical central quotient, transported by
PSL₂(5) ≃ PSL₂(4), maps onto SL₂(4) with kernel of order two. Pulling back
the rank-one Sylow geometry proves the original minimal-parabolic hypothesis
for every Sylow two-subgroup. The maximal core and the two-core are both the
center. A choice of Sylow also marks the image of its unique maximal subgroup
as the actual upper triangular Borel.

Every involution of the cover is central, so its generation parameter is one.
Its star quotient has binary field exponent two. Thus the source hypotheses
and the marked quotient do not justify identifying the generation parameter
of the original group with that exponent. No negation of the complete six-row
classification predicate is asserted here, and no old source interface changes.
The later marked E.6 consumer's condition `1 < n(H)` excludes this example;
that observation does not prove a numerical replacement on the restricted domain.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.1.5–E.1.6
(p.210) and the final numerical sentence and quotient reduction in E.2.2
(pp.215–216). All group and subgroup data here are Lean constructions;
no GAP calculation is a proof input.
-/

public section
noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.CentralCoverAudit
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
abbrev H := SL(2,ZMod 5)
abbrev F := GaloisField 2 2
abbrev Q := SL(2,F)

def comparison : PSL(2,ZMod 5) ≃* Q :=
  ProjectiveSpecialLinearGroup.five_equiv_four.some.trans
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm

def projection : H →* Q :=
  comparison.toMonoidHom.comp (QuotientGroup.mk' (center H))

theorem projection_surjective : Function.Surjective projection :=
  comparison.surjective.comp (QuotientGroup.mk'_surjective _)

theorem projection_ker : projection.ker = center H := by
  rw [projection, MonoidHom.ker_comp_of_injective _ _ comparison.injective,
    QuotientGroup.ker_mk']

theorem center_card : Nat.card (center H) = 2 := by
  rw [← GorensteinWalter.sl2ProjectiveProjection_ker]
  exact GorensteinWalter.sl2ProjectiveProjection_ker_card (ZMod 5) (by norm_num)

theorem center_twoGroup : IsPGroup 2 (center H) :=
  IsPGroup.of_card (n := 1) (by simpa using center_card)

theorem card_group : Nat.card H = 120 := by
  rw [GorensteinWalter.sl2_card_formula]; norm_num

theorem card_target : Nat.card Q = 60 := by
  rw [GorensteinWalter.sl2_card_formula, GaloisField.card 2 2 (by decide)]; norm_num

theorem stronglyQuasithin : IsStronglyQuasithin H := by
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  apply primeRank_le_two_of_cube_not_dvd
  rw [card_group]
  intro hd
  have hpd : p ∣ 2 ^ 3 * (3 * 5) :=
    (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  rw [hp.dvd_mul,hp.dvd_mul] at hpd
  rcases hpd with h | h | h
  · have he : p = 2 := Nat.prime_eq_prime_of_dvd_pow hp (by decide) h
    subst p
    exact ho.not_two_dvd_nat (dvd_refl 2)
  · have he : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h
    subst p
    norm_num at hd
  · have he : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h
    subst p
    norm_num at hd

theorem sqtk_constructed : IsSQTK CFSG.KnownSimple.IsConstructedCarrier H :=
  ⟨stronglyQuasithin, MainConverse.LinearThreeSections.sl2_isKGroup_constructed (ZMod 5)⟩

theorem sqtk : IsSQTK CFSG.KnownSimple.IsKnownSimple H := by
  refine ⟨stronglyQuasithin, ?_⟩
  intro S _ hS U f hf
  let := hS
  let : Finite S := Finite.of_surjective f hf
  exact ⟨inferInstance,inferInstance,
    (sqtk_constructed.isKGroup S hS U f hf).isKnownSimpleCarrier⟩

theorem nonsolvable : ¬Group.IsSolvable H := by
  let : Group.IsPerfect H :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod 5) (by norm_num)
  let : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by rw [card_group]; decide)
  exact Group.IsPerfect.not_isSolvable H

private theorem target_minimal (S : Sylow 2 Q) : ChapterB.IsMinimalParabolicOver S ⊤ := by
  apply (ChapterB.isMinimalParabolicOver_top_iff S).mpr
  have huniq := SpecialLinearGroup.sylow_hasUniqueMaximalOver (F := F) 2 S
  refine ⟨?_, ?_⟩
  · obtain ⟨B,hB,hu⟩ := huniq.2
    exact ⟨B,⟨hB.2.isCoatom,hB.1⟩,fun C hC => hu C ⟨hC.2,hC.1.covBy_top⟩⟩
  · exact SpecialLinearGroup.no_normal_sylow F 2 S

private theorem minimal_preimage {G A : Type*} [Group G] [Group A] [Finite G]
    (T : Sylow 2 G) (f : G →* A) (hf : Function.Surjective f)
    (hk : f.ker ≤ (T : Subgroup G))
    (hP : ChapterB.IsMinimalParabolicOver (T.mapSurjective hf) ⊤) :
    ChapterB.IsMinimalParabolicOver T ⊤ := by
  let B := ChapterB.minimalParabolicMax (T.mapSurjective hf) hP
  have hB := ChapterB.minimalParabolicMax_spec (T.mapSurjective hf) hP
  apply (ChapterB.isMinimalParabolicOver_top_iff T).mpr
  refine ⟨⟨B.comap f,⟨isCoatom_comap_of_surjective hf hB.1,
    map_le_iff_le_comap.mp hB.2⟩,?_⟩,?_⟩
  · intro C hC
    have hkC := hk.trans hC.2
    have hc : IsCoatom (C.map f) := by
      refine ⟨?_,?_⟩
      · intro he
        have hh := congrArg (Subgroup.comap f) he
        rw [comap_map_eq_self hkC,comap_top] at hh
        exact hC.1.ne_top hh
      · intro L hL
        have hlt : C < L.comap f := by
          apply lt_of_le_of_ne (map_le_iff_le_comap.mp hL.le)
          intro he
          have hh := congrArg (Subgroup.map f) he
          rw [map_comap_eq_self_of_surjective hf] at hh
          exact hL.ne hh
        have hh := congrArg (Subgroup.map f) (hC.1.2 _ hlt)
        simpa only [map_comap_eq_self_of_surjective hf,map_top_of_surjective f hf] using hh
    have he := ChapterB.minimalParabolicMax_unique (T.mapSurjective hf) hP hc
      (map_mono hC.2)
    simpa only [comap_map_eq_self hkC] using congrArg (Subgroup.comap f) he
  · intro hn
    let := hn
    exact ((ChapterB.isMinimalParabolicOver_top_iff _).mp hP).2
      (Subgroup.Normal.map hn f hf)

theorem minimal (T : Sylow 2 H) : ChapterB.IsMinimalParabolicOver T ⊤ :=
  minimal_preimage T projection projection_surjective
    (by rw [projection_ker]; exact center_twoGroup.le_sylow_of_normal T)
    (target_minimal _)

theorem twoCore_eq_center : pCore 2 H = center H := by
  have hker : IsPGroup 2 projection.ker := by rw [projection_ker]; exact center_twoGroup
  have he := projection.comap_pCore_of_ker_isPGroup projection_surjective hker
  rw [Atlas.RankOneFieldAutomorphisms.sl_twoCore_eq_bot, MonoidHom.comap_bot, projection_ker] at he
  exact he.symm

private instance target_simple : IsSimpleGroup Q := by
  let : IsSimpleGroup PSL(2,F) := ProjectiveSpecialLinearGroup.rank_two_simple
    (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
  exact (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).isSimpleGroup

instance core_normal (T : Sylow 2 H) :
    (ChapterB.minimalParabolicCore T (minimal T)).Normal := by
  change (ChapterB.minimalParabolicMax T (minimal T)).normalCore.Normal
  infer_instance

theorem core_eq_center (T : Sylow 2 H) :
    ChapterB.minimalParabolicCore T (minimal T) = center H := by
  let M := ChapterB.minimalParabolicMax T (minimal T)
  let J := ChapterB.minimalParabolicCore T (minimal T)
  have hk : projection.ker ≤ (T : Subgroup H) := by
    rw [projection_ker]
    exact center_twoGroup.le_sylow_of_normal T
  have hkM : projection.ker ≤ M := hk.trans (ChapterB.minimalParabolicMax_spec T (minimal T)).2
  have hm : M.map projection ≠ ⊤ := by
    intro he
    have hh := congrArg (Subgroup.comap projection) he
    rw [comap_map_eq_self hkM, comap_top] at hh
    exact (ChapterB.minimalParabolicMax_spec T (minimal T)).1.ne_top hh
  have hJ : (J.map projection).Normal :=
    Subgroup.Normal.map inferInstance projection projection_surjective
  have hj : J.map projection = ⊥ := by
    rcases hJ.eq_bot_or_eq_top with he | he
    · exact he
    · exact False.elim (hm (top_unique (he ▸ map_mono (normalCore_le M))))
  apply le_antisymm
  · rw [← projection_ker]
    exact (J.map_eq_bot_iff).mp hj
  · change center H ≤ M.normalCore
    exact normal_le_normalCore.mpr (projection_ker ▸ hkM)

def starEquivFour (T : Sylow 2 H) :
    ChapterB.minimalParabolicStarQuotient T (minimal T) ≃* PSL(2,F) :=
  (QuotientGroup.quotientMulEquivOfEq (core_eq_center T)).trans
    ProjectiveSpecialLinearGroup.five_equiv_four.some

theorem exists_borel_chart : ∃ T : Sylow 2 H,
    (ChapterB.minimalParabolicMax T (minimal T)).map projection =
      SpecialLinearGroup.rankOneBorel F := by
  obtain ⟨T,hT⟩ := Sylow.mapSurjective_surjective projection_surjective 2
    (SpecialLinearGroup.upperUnipotentSylow F 2)
  refine ⟨T,?_⟩
  let M := ChapterB.minimalParabolicMax T (minimal T)
  have hk : projection.ker ≤ (T : Subgroup H) := by
    rw [projection_ker]
    exact center_twoGroup.le_sylow_of_normal T
  have hm := ChapterB.minimalParabolicMax_map T (minimal T) projection projection_surjective hk
  have hc : IsCoatom (M.map projection) := by
    rw [hm]
    exact (ChapterB.minimalParabolicMax_spec _ _).1
  have hu : SpecialLinearGroup.upperUnipotent F ≤ M.map projection := by
    have ht := map_mono (f := projection) (ChapterB.minimalParabolicMax_spec T (minimal T)).2
    change (T.mapSurjective projection_surjective : Subgroup Q) ≤ M.map projection at ht
    rwa [hT] at ht
  have hle := SpecialLinearGroup.overgroup_le_rankOneBorel hu hc.ne_top
  have hb : SpecialLinearGroup.rankOneBorel F ≠ ⊤ := by
    intro he
    exact SpecialLinearGroup.upperUnipotent_not_normal F
      (normalizer_eq_top_iff.mp he)
  exact ((hc.covBy_top.eq_or_eq hle le_top).resolve_right hb).symm

theorem value : generationParameter H = 1 := generationParameter_sl2_odd (by decide)

/-- All original hypotheses of E.2.2 hold, but the generation parameter of
this central cover differs from the binary field exponent of its star model. -/
theorem source_hypotheses_and_discrepancy (T : Sylow 2 H) :
    IsSQTK CFSG.KnownSimple.IsKnownSimple H ∧
    ChapterB.IsMinimalParabolicOver T ⊤ ∧ ¬Group.IsSolvable H ∧
    ChapterB.minimalParabolicCore T (minimal T) = pCore 2 H ∧
    Nat.card (ChapterB.minimalParabolicCore T (minimal T)) = 2 ∧
    Nonempty (ChapterB.minimalParabolicStarQuotient T (minimal T) ≃* PSL(2,F)) ∧
    Nat.card F = 2 ^ 2 ∧ generationParameter H = 1 ∧ generationParameter H ≠ 2 := by
  refine ⟨sqtk,minimal T,nonsolvable,?_,?_,⟨starEquivFour T⟩,?_,value,?_⟩
  · rw [core_eq_center,twoCore_eq_center]
  · rw [core_eq_center,center_card]
  · exact GaloisField.card 2 2 (by decide)
  · rw [value]
    decide

/-- The rank assumption in the marked E.6 consumer excludes this particular
example. This does not establish a corrected numerical theorem on that domain. -/
theorem not_one_lt_parameter : ¬1 < generationParameter H := by rw [value]; decide

/-- The original source hypotheses and an actual Borel-marked binary quotient
do not suffice to identify the original generation parameter with its exponent.
This refutes only that numerical inference, not a full classification predicate. -/
theorem not_binary_borel_quotient_parameter_rule :
    ¬ (∀ (G : Type) [Group G] [Finite G], IsSQTK CFSG.KnownSimple.IsKnownSimple G →
      ∀ (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤),
      ¬Group.IsSolvable G → ∀ q : G →* Q, Function.Surjective q →
      q.ker = (ChapterB.minimalParabolicMax T hP).normalCore →
      (ChapterB.minimalParabolicMax T hP).map q = SpecialLinearGroup.rankOneBorel F →
      generationParameter G = 2) := by
  intro hrule
  obtain ⟨T,hT⟩ := exists_borel_chart
  have hk : projection.ker = (ChapterB.minimalParabolicMax T (minimal T)).normalCore := by
    rw [projection_ker]
    exact (core_eq_center T).symm
  have he := hrule H sqtk T (minimal T) nonsolvable projection projection_surjective hk hT
  rw [value] at he
  omega

end CFSG.Quasithin.ChapterE.CentralCoverAudit
