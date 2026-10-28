module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeCommonFixer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePaths

/-!
# Strict backward shifts in the original nonsylow replacement

The strict small-image shift now has no trapped alternative. If it uses
the conjugated critical walk, act by the inverse of that same cubic on
the entire backward walk. Composing its neighbor transporter with the
inverse cubic produces a backward critical walk of the original path,
with its first edge and every shared vertex preserved.

Combine this with the established large-image shift and transport through
the original free-amalgam action to every component vertex. The resulting
consumer needs only distance greater than four, the original MS2(a)
radical being nonsylow, and the literal Baumann slice index greater than
two. It discharges both critical-image branches and constructs all maps
on the actual minimum characteristic replacement. Both central covers
and their attachments remain allowed.

Source: Meierfrankenfeld--Stellmacher (1993), (5.7), printed p.919, with the
simultaneous common-fixer selection of (5.6)(b). Existence of the required
strict slices, terminal contradictions, original Sylow branches and the
distance-four exclusions remain with the large-distance assembly owner.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
local notation "S" => Equiv.Perm (Fin 6)

include e hz hn in
/-- The strict slice at a prescribed backward neighbor produces a backward
critical shift of the original walk, in both critical-image branches. -/
theorem nonsylow_strict_backward_path_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hindex : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ v : CriticalPath d.radical (replacementGeometry h d) (act d.radical g delta)
            (p.walk.getVert (p.walk.length-2)),
          v.walk.getVert 1=t ∧
          ∀ i ≤ p.walk.length-2, v.walk.getVert (i+2)=p.walk.getVert i := by
  have hb : 2 < replacementDistance h d := by omega
  have strict (g : FreeAmalgam d.radical)
      (hg : g ∈ stabilizer d.radical (alpha d.radical)) :
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (act d.radical g delta)) := by
    have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        hb (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hindex
  by_cases hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))
  · have hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
      intro hh
      have he := relIndex_eq_one.mpr hh
      omega
    obtain ⟨t,hat,_,g,hg,hgt,v,hvt,hover,_⟩ :=
      nonsylow_large_image_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn)
        hb hns p hlarge hdelta hel
    exact ⟨t,hat,g,hg,hgt,strict g hg,v,hvt,hover⟩
  · obtain ⟨t,hat,g,hg,hgt,_,_,x,hx,_,_,q,hq,_,_,halt⟩ :=
      nonsylow_strict_small_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn)
        hb4 hns p (Nat.lt_of_not_ge hlarge) hdelta hindex
    rcases halt with ⟨v,hvt,hover⟩ | ⟨v,hvt,hover⟩
    · exact ⟨t,hat,g,hg,hgt,strict g hg,v,hvt,hover⟩
    · let y := g*x⁻¹
      have hy : y ∈ stabilizer d.radical (alpha d.radical) :=
        mul_mem hg (inv_mem (Ltilde_le_stabilizer _ hx))
      have hxfix : act d.radical x⁻¹ (alpha d.radical) = alpha d.radical :=
        (stabilizer d.radical (alpha d.radical)).inv_mem (Ltilde_le_stabilizer _ hx)
      have hat' : Adjacent d.radical (alpha d.radical) (act d.radical x⁻¹ t) := by
        rw [←hxfix]
        exact (adjacent_act_iff d.radical x⁻¹ _ _).mpr hat
      have hyt : act d.radical y (p.walk.getVert 1) = act d.radical x⁻¹ t := by
        rw [show y=g*x⁻¹ from rfl,act_mul,hgt]
      refine ⟨act d.radical x⁻¹ t,hat',y,hy,hyt,strict y hy,?_⟩
      have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
      have hend : act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2)) =
          p.walk.getVert (p.walk.length-2) := by
        rw [hlen,hq,←act_mul,mul_inv_cancel,act_one]
      have hstart : act d.radical x⁻¹ (act d.radical g delta) = act d.radical y delta :=
        (act_mul d.radical g x⁻¹ delta).symm
      have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical x⁻¹ (act d.radical g delta))
          (act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2))),
          w.walk.getVert 1=act d.radical x⁻¹ t ∧
          ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2)=p.walk.getVert i := by
        refine ⟨v.act x⁻¹,?_,?_⟩
        · simp only [CriticalPath.act,actWalk_getVert,hvt]
        · intro i hi
          have hiq : i ≤ q.walk.length-2 := hlen.symm ▸ hi
          simp only [CriticalPath.act,actWalk_getVert,hover i hiq,hq,
            ←act_mul,mul_inv_cancel,act_one]
      rwa [hstart,hend] at hex

include e hz hn in
/-- The strict backward shift at every original component vertex, retaining
the prescribed neighbor's actual stabilizer conjugator and the full overlap. -/
theorem nonsylow_strict_backward_path_at_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hindex : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical a t ∧
      ∃ g ∈ stabilizer d.radical a,
        act d.radical g (p.walk.getVert 1) = t ∧
        2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ v : CriticalPath d.radical (replacementGeometry h d) (act d.radical g delta)
            (p.walk.getVert (p.walk.length-2)),
          v.walk.getVert 1=t ∧
          ∀ i ≤ p.walk.length-2, v.walk.getVert (i+2)=p.walk.getVert i := by
  have hb : 2 < replacementDistance h d := by omega
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical j⁻¹ a = alpha d.radical := by
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have base := nonsylow_strict_backward_path_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hns
    (a' := act d.radical j⁻¹ a') (delta := act d.radical j⁻¹ delta)
  rw [←hbase] at base
  have hdelta0 : Adjacent d.radical (act d.radical j⁻¹ delta)
      ((p.act j⁻¹).walk.getVert 1) := by
    simpa only [CriticalPath.act,actWalk_getVert] using
      (adjacent_act_iff d.radical j⁻¹ _ _).mpr hdelta
  have hindex0 : 2 < (B d.radical (act d.radical j⁻¹ a)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (act d.radical j⁻¹ delta)) := by
    rw [Escape.PairingControl.FirstPairing.B_act hb j⁻¹ a p.start_color,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hindex
  obtain ⟨t,hat,k,hk,hkt,_,v,hvt,hover⟩ := base (p.act j⁻¹) hdelta0 hindex0
  have hcancel (z : Vertex d.radical) : act d.radical j (act d.radical j⁻¹ z) = z := by
    rw [←act_mul,inv_mul_cancel,act_one]
  let y := j⁻¹*k*j
  have hact (z : Vertex d.radical) : act d.radical j (act d.radical k (act d.radical j⁻¹ z)) =
      act d.radical y z := by simp only [←act_mul,y,mul_assoc]
  have hy : y ∈ stabilizer d.radical a := by
    change act d.radical y a = a
    rw [←hact]
    rw [show act d.radical k (act d.radical j⁻¹ a)=act d.radical j⁻¹ a from hk,hcancel]
  have hB : (B d.radical a ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj y⁻¹).toMonoidHom = B d.radical a ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb a p.start_color ((stabilizer d.radical a).inv_mem hy))
  have hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical y delta)) := by
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective]
    exact hindex
  refine ⟨act d.radical j t,?_,y,hy,?_,hstrict,?_⟩
  · simpa only [hcancel] using (adjacent_act_iff d.radical j _ _).mpr hat
  · have he := congrArg (act d.radical j) hkt
    simpa only [CriticalPath.act,actWalk_getVert,hact] using he
  · have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical j (act d.radical k (act d.radical j⁻¹ delta)))
        (act d.radical j ((p.act j⁻¹).walk.getVert ((p.act j⁻¹).walk.length-2))),
        w.walk.getVert 1=act d.radical j t ∧
        ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2)=p.walk.getVert i := by
      refine ⟨v.act j,?_,?_⟩
      · simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act d.radical j) hvt
      · intro i hi
        have he := congrArg (act d.radical j) (hover i (by
          simpa only [CriticalPath.act,actWalk_length] using hi))
        simpa only [CriticalPath.act,actWalk_getVert,hcancel] using he
    have hend : act d.radical j ((p.act j⁻¹).walk.getVert ((p.act j⁻¹).walk.length-2)) =
        p.walk.getVert (p.walk.length-2) := by
      simp only [CriticalPath.act,actWalk_length,actWalk_getVert,hcancel]
    rwa [hact,hend] at hex

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
