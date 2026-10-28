module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Projection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion.FromCentralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Conjugate generation in the derived-image branch

An escaping relative normal closure maps onto the simple A₆ quotient.
Joining it with the edge radical consequently recovers the vertex group.
Edge transitivity transports this fact to every edge of the literal free
holomorph tree. This proves (2.3)(b) without a natural subgroup or an
SL₃(2) source record.

Source: MS93 (2.3)(b) and the first paragraph of (3.8), pp.857 and 877.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.CriticalCriterion
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

private theorem base_normal_closure_core_top
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6))
    (N : Subgroup (FreeAmalgam d.radical))
    (hN : N ≤ Mbar d.radical) (hNorm : Mbar d.radical ≤ normalizer (N : Set (FreeAmalgam d.radical)))
    (hne : ¬ N ≤ (pCore 2 d.overgroup).map (embedM d.radical)) :
    N ⊔ (pCore 2 d.overgroup).map (embedM d.radical) = Mbar d.radical := by
  let A : Subgroup d.overgroup := N.comap (embedM d.radical)
  let : A.Normal := by
    constructor
    intro x hx m
    show embedM d.radical (m*x*m⁻¹) ∈ N
    simpa only [map_mul,map_inv] using
      le_normalizer_iff.mp hNorm (embedM d.radical m) ⟨m,rfl⟩ (embedM d.radical x) hx
  let q : d.overgroup →* alternatingGroup (Fin 6) :=
    (projection h e hz hn d).codRestrict _ (fun m => himage ▸ ⟨m,rfl⟩)
  have hq : Function.Surjective q := by
    intro y
    have hy : (y : Equiv.Perm (Fin 6)) ∈ (projection h e hz hn d).range := by rw [himage]; exact y.property
    obtain ⟨m,hm⟩ := hy
    exact ⟨m,Subtype.ext hm⟩
  have hk : q.ker = pCore 2 d.overgroup := by
    rw [←projection_kernel h e hz hn d]
    ext m
    exact Subtype.ext_iff
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : (A.map q).Normal := Normal.map inferInstance q hq
  have htop : A.map q = ⊤ := by
    rcases (inferInstance : (A.map q).Normal).eq_bot_or_eq_top with hz | ht
    · have hA : A ≤ pCore 2 d.overgroup := by
        rw [←hk]
        exact (Subgroup.map_eq_bot_iff A).mp hz
      apply False.elim
      apply hne
      have hm := map_mono (f := embedM d.radical) hA
      simpa only [A,map_comap_eq,inf_eq_right.mpr (show N ≤ (embedM d.radical).range from hN)] using hm
    · exact ht
  have hAQ : A ⊔ pCore 2 d.overgroup = ⊤ := by
    have hh := congrArg (Subgroup.comap q) htop
    simpa only [comap_map_eq,hk,comap_top] using hh
  have hm := congrArg (Subgroup.map (embedM d.radical)) hAQ
  change N ⊔ (pCore 2 d.overgroup).map (embedM d.radical) = (embedM d.radical).range
  simpa only [Subgroup.map_sup,A,map_comap_eq,inf_eq_right.mpr (show N ≤ (embedM d.radical).range from hN),
    ←MonoidHom.range_eq_map] using hm

/-- A6 simplicity gives the printed normal-closure generation on every edge. -/
theorem generation
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6)) :
    CriticalCriterion.Generation d.radical := by
  apply Generation.of_edge d.radical (alpha d.radical) (beta d.radical) rfl (base_adjacent d.radical)
  intro x hx hout
  let N := conjugatesIn (zpowers x) (Mbar d.radical)
  have hxR : x ∈ d.radical.map (embedM d.radical) := by simpa only [Q_beta] using hx
  have hNM : N ≤ Mbar d.radical := conjugatesIn_le _ _
    ((zpowers_le.mpr hxR).trans (map_le_range _ _))
  have hxN : x ∈ N := by
    apply le_iSup (fun g : Mbar d.radical => rightConjugate (zpowers x) g) (1 : Mbar d.radical)
    exact ⟨x,mem_zpowers x,by simp⟩
  have htop := base_normal_closure_core_top h e hz hn d himage N hNM
    (conjugatesIn_normalized _ _) (fun hh => hout (by
      rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
      exact hh hxN))
  have hQR : (pCore 2 d.overgroup).map (embedM d.radical) ≤ d.radical.map (embedM d.radical) := map_mono (replacement_core_le_radical h d)
  rw [show stabilizer d.radical (alpha d.radical) = Mbar d.radical from stabilizer_m_base d.radical]
  change N ⊔ Q d.radical (beta d.radical) = Mbar d.radical
  rw [Q_beta]
  apply le_antisymm (sup_le hNM (map_le_range _ _))
  rw [←htop]
  exact sup_le_sup_left hQR N


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
