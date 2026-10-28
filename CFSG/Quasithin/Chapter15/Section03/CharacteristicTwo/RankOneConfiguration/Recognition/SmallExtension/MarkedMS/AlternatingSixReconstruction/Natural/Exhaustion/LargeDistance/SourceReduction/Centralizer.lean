module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.CriticalPairs

/-!
# The exact local centralizer in the derived-image branch

The centralizer of the graph Z-layer contains the two-core. Simplicity of
the actual A₆ quotient makes it either the two-core or the whole group.
The latter would make the nonzero omega-center of the replacement radical
normal in the replacement group, contradicting the inherited MS3 condition.
Conjugation transports the equality to every vertex and edge. No splitting
of the moved cover is needed.

Source: MS93 (2.2), (2.3)(1), and (3.8), pp.856--858 and 877.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

/-- The exact local centralizer in the derived-image branch. Its proof uses
simplicity and MS3 on the original replacement radical. -/
theorem localZ_centralizer
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6)) :
    centralizer (localZ d.radical : Set d.overgroup) = pCore 2 d.overgroup := by
  let q : d.overgroup →* alternatingGroup (Fin 6) :=
    (projection h e hz hn d).codRestrict _ (fun m => himage ▸ ⟨m,rfl⟩)
  have hq : Function.Surjective q := by
    intro y
    have hy : (y : Equiv.Perm (Fin 6)) ∈ (projection h e hz hn d).range := by
      rw [himage]
      exact y.property
    obtain ⟨m,hm⟩ := hy
    exact ⟨m,Subtype.ext hm⟩
  have hk : q.ker = pCore 2 d.overgroup := by
    rw [←projection_kernel h e hz hn d]
    ext m
    exact Subtype.ext_iff
  have hQ : pCore 2 d.overgroup ≤ centralizer (localZ d.radical : Set d.overgroup) := by
    intro x hx z hz
    apply embedM_injective d.radical
    simp only [map_mul]
    have hc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical (alpha d.radical) rfl))
    exact hc (by
      rw [Q_alpha d.radical (replacement_radical_isPGroup h d)
        (replacement_core_le_radical h d)]
      exact mem_map_of_mem _ hx) (embedM d.radical z) hz
  let := localZ_normal (R := d.radical)
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let A := centralizer (localZ d.radical : Set d.overgroup)
  have hnorm : (A.map q).Normal := (inferInstance : A.Normal).map _ hq
  rcases hnorm.eq_bot_or_eq_top with hbot | htop
  · exact le_antisymm (by simpa only [hk] using (Subgroup.map_eq_bot_iff _).mp hbot) hQ
  · have hAtop : A = ⊤ := by
      have hh := congrArg (fun B => B.comap q) htop
      have hQA : pCore 2 d.overgroup ≤ A := hQ
      simpa only [comap_map_eq, hk, comap_top, sup_eq_left.mpr hQA] using hh
    let D : Subgroup d.radical :=
      (omega₁ (center d.radical) (p := 2)).map (center d.radical).subtype
    let : (omega₁ (center d.radical) (p := 2)).Characteristic := omega₁_characteristic _
    have hDnorm : (D.map d.radical.subtype).Normal := by
      constructor
      intro x hx m
      have hxZ : x ∈ localZ d.radical := omegaCenter_le_localZ hx
      have hm : m ∈ A := hAtop ▸ mem_top m
      have hcomm := hm x hxZ
      have heq : m * x * m⁻¹ = x := by
        rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rwa [heq]
    have hDbot := (replacement_characteristic h d).eq_bot_of_normal D hDnorm
    let : Nontrivial d.radical := (nontrivial_iff_ne_bot d.radical).mpr
      (replacement_radical_ne_bot h d)
    exact (omega_center_ne_bot (replacement_radical_isPGroup h d) hDbot).elim

/-- The marked A₆ image gives Cα = Qα without assuming a natural subgroup. -/
theorem C_alpha
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6)) :
    C d.radical (alpha d.radical) = Q d.radical (alpha d.radical) := by
  apply le_antisymm
  · rintro x ⟨hx, hc⟩
    have hxM : x ∈ Mbar d.radical := (stabilizer_m_base d.radical) ▸ hx
    obtain ⟨m, rfl⟩ := hxM
    have hm : m ∈ centralizer (localZ d.radical : Set d.overgroup) := by
      intro z hz
      apply embedM_injective d.radical
      simpa only [map_mul] using hc (embedM d.radical z) hz
    rw [localZ_centralizer h e hz hn d himage] at hm
    rw [Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)]
    exact mem_map_of_mem _ hm
  · intro x hx
    exact ⟨hx.1, le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical (alpha d.radical) rfl)) hx⟩

/-- Transport of the exact centralizer on the actual free-amalgam vertices. -/
theorem C_eq_Q
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false) :
    C d.radical a = Q d.radical a := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color d.radical ha
  have hh := C_act (R := d.radical) g (alpha d.radical)
  have hq := Q_act d.radical g (alpha d.radical)
  simp only [alpha, act_mVertex, one_mul] at hh hq
  have hbase := C_alpha h e hz hn d himage
  change C d.radical (mVertex d.radical 1) = Q d.radical (mVertex d.radical 1) at hbase
  rw [hh, hbase, hq]

/-- The source-(2.2) centralizer condition follows in the derived-image branch. -/
theorem edgeCentralizerCondition
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6)) :
    EdgeCentralizerCondition d.radical := by
  intro a t ha hat
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    cases hcol : color d.radical t <;> simp_all
  apply le_antisymm
  · rintro x ⟨hx, hc⟩
    rw [← C_eq_Q h e hz hn d himage a ha]
    exact ⟨hx.2 a (adjacent_symm d.radical hat), hc⟩
  · intro x hx
    refine ⟨Q_le_adjacent_h d.radical ht hat hx, ?_⟩
    exact le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha)) hx

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
