module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightMovers
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightGenerating
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowCompatible

/-!
# Paired generating edges for image eight at distance four

The mixed and even four-group movers supply one edge and a single residual
transporter. That edge generates the starting stabilizer with each of the
two transported full endpoint seeds, while the same transporter belongs to
the join of the two actual small movers. The private model certificate is
shared with the beyond-four argument; only the explicit non-elementary
image-eight hypotheses and distance above two enter this construction.

The equal- and unequal-mover consumers use these literal generating edges
in the backward critical-path selection of MS93 (5.7)--(5.8), printed
pp.919--920, and hence in the initial selection of (5.12), p.924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightGenerating
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- Choose one edge kernel generating with each of the two endpoint seeds,
while the same residual transporter belongs to the paired movers. -/
theorem paired_generating_selection_knownSimple
    (hne : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d) (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4) :
    ∃ g ∈ stabilizer d.radical (alpha d.radical),
      ∃ x ∈ Ltilde d.radical (alpha d.radical),
        x^3 ∈ Q d.radical (alpha d.radical) ∧
        let t := act d.radical g (beta d.radical)
        let J := EightEdgeComparison.edgeMover (d := d) (alpha d.radical) t
        Adjacent d.radical (alpha d.radical) t ∧
          J ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) =
            stabilizer d.radical (alpha d.radical) ∧
          x ∈ J ⊔ J.map (MulAut.conj x).toMonoidHom ∧
          Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
          Q d.radical t ⊔ Z d.radical (act d.radical x z) =
            stabilizer d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let J₀ := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  obtain ⟨u,hN,_,_,hJimage,_,_,_,_⟩ := EightMovers.radical_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb
  have hE : Nat.card (d.radical.map s.projection) = 8 := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    exact hcard
  have hne' : ¬ IsElementaryAbelian 2 (d.radical.map s.projection) := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    exact hne
  have hmodel' : IsConjugateTo (J₀.map s.projection) plus ∨
      IsConjugateTo (J₀.map s.projection) (evenPart 6) := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hkJ : s.projection.ker ≤ J₀ := by
    rw [s.projection_kernel]
    let := replacementMoved_normal h d
    exact SmallMover.kernel_le_join _ _ _ 4 (by decide) (replacement_core_le_radical h d)
      (by rw [←moved_centralizer s]; exact le_centralizer_iff.mpr le_rfl)
  obtain ⟨a,ha,hswap⟩ := small_critical_image_swap s hc p hsmall
  let A := (Z d.radical z).comap (embedM d.radical)
  obtain ⟨g,y,hy,hy3,htop,hpair,hleft,hright⟩ := SectionFive.EightGenerating.compatible_lifts s.projection s.surjective
    d.radical J₀ (replacementComponent d) A s.component_image hkJ
    (sSup_le fun _ hB => hB.1.1) u ((map_mono d.radical.le_normalizer).trans_eq hN)
    hE hne' hJimage hmodel' a ha hswap
  let J₁ := J₀.map (MulAut.conj g).toMonoidHom
  let A₁ := A.map (MulAut.conj y).toMonoidHom
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hU : (replacementMoved d).map (MulAut.conj g).toMonoidHom = replacementMoved d := by
    let := replacementMoved_normal h d
    exact mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  let f := (embedM d.radical g)⁻¹
  let x := (embedM d.radical y)⁻¹
  let t := act d.radical f (beta d.radical)
  let J := EightEdgeComparison.edgeMover (d := d) (alpha d.radical) t
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    change f ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have ht : Q d.radical t = (d.radical.map (MulAut.conj g).toMonoidHom).map (embedM d.radical) := by
    rw [Q_act,Q_beta,SylowCompatible.image_conjugate]
    simp only [f,inv_inv]
  have hJm : J₁.map (embedM d.radical) = J := by
    change ((SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4).map
      (MulAut.conj g).toMonoidHom).map (embedM d.radical) = J
    rw [SmallMover.join_map _ (MulAut.conj g).injective,hU,hQ,
      SmallMover.join_map _ (embedM_injective d.radical),←hc.U_eq_moved,
      ←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d),←ht]
  have hxL : x ∈ Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d]
    exact mem_map_of_mem _ ((replacementComponent d).inv_mem hy)
  have hAm : A.map (embedM d.radical) = Z d.radical z :=
    map_comap_eq_self ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
        (stabilizer_m_base d.radical))
  have hA₁m : A₁.map (embedM d.radical) = Z d.radical (act d.radical x z) := by
    rw [SylowCompatible.image_conjugate,hAm,Z_act]
    simp only [x,inv_inv]
  have hrange : (embedM d.radical).range = stabilizer d.radical (alpha d.radical) :=
    (stabilizer_m_base d.radical).symm
  change y⁻¹ ∈ J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom at hpair
  refine ⟨f,hf,x,hxL,?_,?_,?_,?_,?_,?_⟩
  · rw [s.projection_kernel] at hy3
    rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    have hx3 : x^3=embedM d.radical ((y^3)⁻¹) := by simp only [x,inv_pow,map_inv,map_pow]
    rw [hx3]
    exact mem_map_of_mem _ ((pCore 2 d.overgroup).inv_mem hy3)
  · have hfix : act d.radical f (alpha d.radical)=alpha d.radical := hf
    rw [←hfix]
    exact (adjacent_act_iff d.radical f _ _).mpr (base_adjacent d.radical)
  · have hh := congrArg (Subgroup.map (embedM d.radical)) htop
    rwa [Subgroup.map_sup,Subgroup.map_sup,hJm,hAm,hA₁m,←MonoidHom.range_eq_map,
      hrange] at hh
  · have hh := mem_map_of_mem (embedM d.radical) hpair
    rwa [Subgroup.map_sup,SylowCompatible.image_conjugate (embedM d.radical) J₁ y⁻¹,
      map_inv,hJm] at hh
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hleft
    rwa [Subgroup.map_sup,←ht,hAm,←MonoidHom.range_eq_map,hrange] at hh
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hright
    rwa [Subgroup.map_sup,←ht,hA₁m,←MonoidHom.range_eq_map,hrange] at hh

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightGenerating
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
