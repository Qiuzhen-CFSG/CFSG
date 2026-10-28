module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.CubicOrbit.Noncentral
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRadiusStructure
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.FaithfulRadius
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.RadiusTransfer

/-!
# Fixedness transfer to the whole original cubic radius

Each radius-two seed is centralized by its own two-core. If that core
escapes the starting core, the proved cubic normal-generation theorem puts
the actual perfect component in its normal closure, retaining the odd
extension kernel. Otherwise equal core orders give trivial seed movement.
The generic commutator transfer and the radius join then extend the moving
radius bound to the whole radius on the original graph.

The intentional private import reuses only the group-independent generator
and join lemmas within this reconstruction package. No natural replacement,
Sylow upgrade, small-image bound, or whole-core reconstruction is used.
The initial-action kernel need not be specified: the cubic-center
normal-generation theorem applies before that kernel case split.
Source: MS93 (4.2)(ii), p.882, and (5.12)(2), p.925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)

include h in
private theorem original_Q_card (a : Vertex Rg) (ha : color Rg a = false) :
    Nat.card (Q Rg a) = Nat.card (pCore 2 M) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color Rg ha
  have hh := Q_act Rg g (alpha Rg)
  simp only [alpha,act_mVertex,one_mul] at hh
  rw [hh,card_map_of_injective (MulAut.conj g⁻¹).injective]
  change Nat.card (Q Rg (alpha Rg)) = _
  rw [Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le,
    card_map_of_injective (embedM_injective Rg)]

include h in
private theorem fixedCore_comap_base :
    (fixedCore Rg (alpha Rg)).comap (embedM Rg) =
      pCore 2 M ⊓ centralizer (pResidual 2 M : Set M) := by
  ext x
  constructor
  · intro hx
    refine ⟨?_,?_⟩
    · have hh : x ∈ (Q Rg (alpha Rg)).comap (embedM Rg) := hx.1
      rwa [Q_alpha_comap Rg h.relative_radical.isPGroup
        h.relative_radical.twoCore_le] at hh
    · intro l hl
      apply embedM_injective Rg
      simpa only [map_mul] using hx.2 (embedM Rg l)
        (by rw [Ltilde_alpha]; exact mem_map_of_mem _ hl)
  · rintro ⟨hx,hc⟩
    refine ⟨?_,?_⟩
    · rw [Q_alpha Rg h.relative_radical.isPGroup
        h.relative_radical.twoCore_le]
      exact mem_map_of_mem _ hx
    · intro l hl
      rw [Ltilde_alpha] at hl
      obtain ⟨l,hl,rfl⟩ := hl
      simpa only [map_mul] using congrArg (embedM Rg) (hc l hl)

include h e hz in
private theorem radius_generator_core_fixed
    (hb : 2 < sourceDistance h)
    (hmove : ⁅Vcirc Rg (alpha Rg),Q Rg (alpha Rg)⁆ ≤
      fixedCore Rg (alpha Rg))
    (c : Vertex Rg) (hc : color Rg c = false)
    (hd : (cosetGraph Rg).dist c (alpha Rg) ≤ 2) :
    ⁅Z Rg c,Q Rg (alpha Rg)⁆ ≤
      fixedCore Rg (alpha Rg) := by
  let a := alpha Rg
  let f := embedM Rg
  have hQa : Q Rg a ≤ stabilizer Rg a := fun _ hx => hx.1
  have hQc : Q Rg c ≤ stabilizer Rg a :=
    Q_le_stabilizer_of_dist_le_two c a hc rfl hd
  have hQac : Q Rg a ≤ stabilizer Rg c :=
    Q_le_stabilizer_of_dist_le_two a c rfl hc (by rwa [SimpleGraph.dist_comm])
  have hAV : Z Rg c ≤ V Rg a := le_iSup_of_le c (le_iSup_of_le hd le_rfl)
  have hVQ := (sourceGeometry h).V_le_Q hb a rfl
  have hAS := hAV.trans (hVQ.trans hQa)
  have hQm : (pCore 2 M).map f = Q Rg a :=
    (Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le).symm
  have hLm : (pResidual 2 M).map f = Ltilde Rg a := (Ltilde_alpha Rg).symm
  have hr : f.range = stabilizer Rg a := (stabilizer_m_base Rg).symm
  let A := (Z Rg c).comap f
  let J := (Q Rg c).comap f
  let V₀ := (V Rg a).comap f
  let D := pCore 2 M ⊓ centralizer (pResidual 2 M : Set M)
  have hAm : A.map f = Z Rg c := map_comap_eq_self (hAS.trans_eq hr.symm)
  have hJm : J.map f = Q Rg c := map_comap_eq_self (hQc.trans_eq hr.symm)
  have hDm : D.map f = fixedCore Rg a := by
    dsimp only [D]
    rw [←fixedCore_comap_base (h := h) (L := L) (R := R)]
    exact map_comap_eq_self ((inf_le_left.trans hQa).trans_eq hr.symm)
  by_cases hle : Q Rg c ≤ Q Rg a
  · let := finite_stabilizer Rg a
    let : Finite (Q Rg a) := Finite.of_injective (inclusion hQa) (inclusion_injective hQa)
    have he : Q Rg c = Q Rg a := eq_of_le_of_card_ge hle (by
      rw [original_Q_card h c hc,original_Q_card h a rfl])
    rw [←he,Z_centralizes_Q Rg c hc]
    exact bot_le
  have hne : c ≠ a := by
    intro he
    exact hle (he ▸ le_rfl)
  have htwo : (cosetGraph Rg).dist a c = 2 := by
    obtain ⟨w,hw⟩ := (cosetGraph_connected Rg).exists_walk_length_eq_dist a c
    have hev : Even w.length := (walk_even_iff_color_eq Rg w).mpr hc.symm
    have hn : (cosetGraph Rg).dist a c ≠ 0 := fun hh =>
      hne ((cosetGraph_connected Rg).dist_eq_zero_iff.mp hh).symm
    rw [hw,Nat.even_iff] at hev
    change (cosetGraph Rg).dist c a ≤ 2 at hd
    rw [SimpleGraph.dist_comm] at hd
    omega
  obtain ⟨t,hat,hct⟩ := exists_common_neighbor_of_dist_two Rg a c htwo
  let T := (Q Rg t).comap f
  have hTa : Q Rg t ≤ stabilizer Rg a := fun _ hx => hx.2 _ (adjacent_symm Rg hat)
  have hTc : Q Rg t ≤ stabilizer Rg c := fun _ hx => hx.2 _ (adjacent_symm Rg hct)
  have hTm : T.map f = Q Rg t := map_comap_eq_self (hTa.trans_eq hr.symm)
  have hgen : T ⊔ pResidual 2 M = ⊤ := by
    apply (map_injective (embedM_injective Rg))
    rw [Subgroup.map_sup,hTm,hLm,←MonoidHom.range_eq_map,hr]
    exact (sup_comm _ _).trans (residual_edge_generation h rfl hat)
  have hQA : pCore 2 M ≤ normalizer A := by
    have hh := (comap_mono (f := f) (hQac.trans (Z_normalized Rg c))).trans
      (le_normalizer_comap f)
    rwa [Q_alpha_comap Rg h.relative_radical.isPGroup
      h.relative_radical.twoCore_le] at hh
  have hTA : T ≤ normalizer A :=
    (comap_mono (hTc.trans (Z_normalized Rg c))).trans (le_normalizer_comap f)
  have hVP : V₀ ≤ pCore 2 M := by
    have hh := comap_mono (f := f) hVQ
    rwa [Q_alpha_comap Rg h.relative_radical.isPGroup
      h.relative_radical.twoCore_le] at hh
  have htriple : ⁅⁅V₀,pResidual 2 M⁆,pCore 2 M⁆ ≤ D := by
    apply (map_le_map_iff_of_injective (embedM_injective Rg)).mp
    rw [map_commutator,map_commutator,radius_comap_map (h := h) hb,hLm,hQm,hDm]
    exact hmove
  have hAJ : ⁅A,J⁆ = ⊥ := by
    apply (map_injective (embedM_injective Rg))
    rw [map_commutator,hAm,hJm,Z_centralizes_Q Rg c hc,Subgroup.map_bot]
  have hJtwo : IsPGroup 2 J :=
    (Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le c hc).comap_of_injective
      f (embedM_injective Rg)
  have hJout : ¬ J ≤ pCore 2 M := by
    intro hj
    have hh := map_mono (f := f) hj
    exact hle (by rwa [hJm,hQm] at hh)
  have hclosure : pResidual 2 M ≤ normalClosure (J : Set M) := by
    rw [h.relative_residual]
    exact CubicAction.component_le_normal_of_escaping_two h e hz
      (normalClosure (J : Set M)) J hJtwo hJout le_normalClosure
  have hh := Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.RadiusTransfer.generator_transfer
    (pCore 2 M) (pResidual 2 M) V₀ (pCore 2 M) A J T
    pCore_isPGroup (isPPerfect_pResidual 2) hgen hVP le_rfl (comap_mono hAV)
    hQA hTA htriple hAJ hclosure
  have hm := map_mono (f := f) hh
  rwa [map_commutator,hAm,hQm,hDm] at hm

include h e hz in
/-- Fixedness of moving-radius core movement extends to the whole original
radius, without replacing the cubic action kernel by the two-core. -/
theorem cubic_radius_core_fixed_of_moving_core_fixed
    (hb : 2 < sourceDistance h)
    (hmove : ⁅Vcirc Rg (alpha Rg),Q Rg (alpha Rg)⁆ ≤
      fixedCore Rg (alpha Rg)) :
    ⁅V Rg (alpha Rg),Q Rg (alpha Rg)⁆ ≤
      fixedCore Rg (alpha Rg) := by
  let D := fixedCore Rg (alpha Rg)
  have hn : V Rg (alpha Rg) ≤ normalizer (D : Set (FreeAmalgam Rg)) :=
    ((sourceGeometry h).V_local _ rfl hb).trans (fixedCore_normalized Rg _)
  apply Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.RadiusTransfer.commutator_iSup_le_of_normalizes _ _ _ hn
  intro c
  apply Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.RadiusTransfer.commutator_iSup_le_of_normalizes
  · apply iSup_le
    intro hd
    exact (le_iSup_of_le c (le_iSup_of_le hd le_rfl) :
      Z Rg c ≤ V Rg (alpha Rg)).trans hn
  · intro hd
    by_cases hc : color Rg c = false
    · exact radius_generator_core_fixed h e hz hb hmove c hc hd
    · have hc' : color Rg c = true := Bool.eq_true_of_not_eq_false hc
      obtain ⟨w,hw⟩ := (cosetGraph_connected Rg).exists_walk_length_eq_dist c (alpha Rg)
      have hev : ¬ Even w.length := by
        rw [walk_even_iff_color_eq,hc']
        change ¬ true = false
        decide
      have hlen : w.length = 1 := by
        have hh := hw.trans_le hd
        rw [Nat.even_iff] at hev
        omega
      have hac := adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp (w.adj_of_length_eq_one hlen))
      have hZ : Z Rg c ≤ Z Rg (alpha Rg) := adjacent_Z_le Rg rfl hac
      exact (commutator_mono hZ le_rfl).trans
        ((Z_centralizes_Q Rg (alpha Rg) rfl).le.trans bot_le)

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
