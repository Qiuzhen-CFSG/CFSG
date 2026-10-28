module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.NaturalPair
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.PreliminaryGeometry

/-!
# Original geometric consequences of the critical pair

The F.7 below-track commutation theorem is transported to the literal
Section 13.8 graph and original ambient conjugation maps. It discharges
the only extra action input of the existing long-path abelian-span theorem.
Thus a nonabelian UL forces length three, and the actual terminal edge
places A₁ in an H-conjugate of V. The final application constructs the pair
from NaturalSetup and the two genuine preceding source results.

Source: Aschbacher--Smith, F.9.14(1--2), 13.8.4(3--4), and the
nonabelian-span branch in 13.8.33, printed pp.323,947,966--967.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open CriticalGeometry
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]

theorem f9_conjugates_commute_below (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (a b : G0 D.L (D.T:Subgroup G) D.H)
    (hd : (CriticalGeometry.graph D.L (D.T:Subgroup G) D.H).dist
      (a•CriticalGeometry.base _ _ _ false) (b•CriticalGeometry.base _ _ _ false) <
        criticalDistance D.L (D.T:Subgroup G) D.H D.V) :
    ⁅D.V.map (MulAut.conj (a:G)).toMonoidHom,D.V.map (MulAut.conj (b:G)).toMonoidHom⁆=⊥ := by
  have hf : cosetFamily D.L (D.T:Subgroup G) D.H=ChapterF.Section07.Geometry.family D.LT D.H := by
    funext i
    cases i <;> rfl
  rw [f9_criticalDistance_eq D h] at hd
  change (Subgroup.CosetGeometry.RankTwo.graph (cosetFamily D.L (D.T:Subgroup G) D.H)).dist
    (a•CosetGeometry.base _ false) (b•CosetGeometry.base _ false)<h.b at hd
  let a' : (D.LT⊔D.H : Subgroup G) := ⟨a.val,a.property⟩
  let b' : (D.LT⊔D.H : Subgroup G) := ⟨b.val,b.property⟩
  have heDist := congrArg (fun F : Bool → Subgroup (D.LT⊔D.H : Subgroup G) =>
    (Subgroup.CosetGeometry.RankTwo.graph F).dist
      (a' • CosetGeometry.base F false) (b' • CosetGeometry.base F false)) hf
  have hd' : (ChapterF.Section07.Geometry.graph D.LT D.H).dist
      (a' • ChapterF.Section07.Geometry.base D.LT D.H false)
      (b' • ChapterF.Section07.Geometry.base D.LT D.H false) < h.b := by
    rw [←heDist]
    exact hd
  have hc := ChapterF.Section07.CriticalPairs.firstModules_commute_below_track
    (ChapterF.Section09.Setup.Hypothesis.family (D:=D)) h.f7Setup h.f7V_ne_bot
    (a:=a'•CosetGeometry.base _ false) (v:=b'•CosetGeometry.base _ false) rfl rfl hd'
  rw [ChapterF.Section07.CriticalPairs.firstModule_translate_base _ _ h.f7Setup.seed_normalized,
    ChapterF.Section07.CriticalPairs.firstModule_translate_base _ _ h.f7Setup.seed_normalized] at hc
  have hc' := congrArg (fun A:Subgroup (D.LT⊔D.H : Subgroup G)=> A.map (D.LT⊔D.H).subtype) hc
  rw [map_commutator,Subgroup.map_bot] at hc'
  have hm (g:(D.LT⊔D.H : Subgroup G)) :
      (h.f7Setup.seed.map (MulAut.conj g).toMonoidHom).map (D.LT⊔D.H).subtype=
        D.V.map (MulAut.conj (g:G)).toMonoidHom := by
    rw [map_map]
    have he : (D.LT⊔D.H).subtype.comp (MulAut.conj g).toMonoidHom=
      (MulAut.conj (g:G)).toMonoidHom.comp (D.LT⊔D.H).subtype := by ext; rfl
    rw [he,←map_map,h.f7Seed_map]
  rwa [hm a',hm b'] at hc'

theorem f9_UL_abelian_of_length_gt_three (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (c:CriticalPair D.L (D.T:Subgroup G) D.H D.V) (hb:3<c.path.length) :
    IsMulCommutative (Source.UL D.L D.H D.Vplus) := by
  apply c.UL_abelian_of_length_gt_three D.Vplus h.plus_le hb
  intro a b _ hd
  exact f9_conjugates_commute_below D h a b hd

theorem f9_length_three_of_nonabelian_span (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (c:CriticalPair D.L (D.T:Subgroup G) D.H D.V) (hb:3≤c.path.length)
    (hn:¬IsMulCommutative (Source.UL D.L D.H D.Vplus)) : c.path.length=3 := by
  have hnot : ¬3<c.path.length := fun hh=>hn (f9_UL_abelian_of_length_gt_three D h c hh)
  omega

theorem f9_Aone_le_conjugate_of_length_three (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (c:CriticalPair D.L (D.T:Subgroup G) D.H D.V) (hb:c.path.length=3) :
    ∃a:D.H,c.Aone D.V₁≤D.V.conjBy (a:G) :=
  c.Aone_le_conjugate_of_length_three D.V₁ (h.point_lt.le.trans h.plus_le)
    ((normal_subgroupOf_iff_le_normalizer h.V_le_LT).mp h.reduced.normal) hb

/-- The actual nonabelian branch starts with a constructed length-three pair,
including the original central-line placement, with no geometry premise. -/
theorem NaturalSetup.exists_nonabelian_criticalPair
    {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
    (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hspan:IsMulCommutative (conjugateSpanBy V G₁))
    (hF9:(Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hn:¬IsMulCommutative (Source.UL L H V₃)) :
    ∃c:CriticalPair L (T:Subgroup G) H V,
      c.path.length=3 ∧ ∃a:H,c.Aone V₁≤V.conjBy (a:G) := by
  obtain ⟨c,hb,_⟩:=d.exists_criticalPair hspan hF9
  have hc := f9_length_three_of_nonabelian_span _ hF9 c hb hn
  exact ⟨c,hc,f9_Aone_le_conjugate_of_length_three _ hF9 c hc⟩
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
