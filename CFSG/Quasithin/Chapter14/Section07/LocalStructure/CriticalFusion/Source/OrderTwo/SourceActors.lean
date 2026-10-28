module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.MarkedPartitions.Seed
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.SourceCompletion.SeedAction
/-!
# Local actors on the original critical chart

The critical image lies in the original point-parabolic two-core. In the
marked SL₂(4) quotient this forces its chart conjugator to normalize the
upper root group. A nonidentity diagonal element therefore lifts through
the same original L₁. The natural seed is fixed by the original radical.
Thus both fields of LocalActors are constructed, including after the
upper-root re-marking, without an actor or module premise.

Source: Aschbacher–Smith 14.3.3(6), 14.7.66 and 14.7.69,
printed pp.974, 1070–1073.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation Chapter12.Section08
open Representation.SL2FourNatural Matrix.SpecialLinearGroup
open Rechoice.LocalGeometry.Preparation
open Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data.CriticalChart
variable {d : Data T L V F W} {hc : d.SectionCentralizer}
  {c : CriticalPath (L := L) F} (b : d.CriticalChart hc c)

theorem localActors_of_marked_source (earlier : c.EarlierImages)
    (hmark : UpperMarking d) (hborel : CompatibleBorel d) : b.LocalActors := by
  constructor
  · intro r hr v
    exact Rechoice.SourceCompletion.seed_fixed d r hr
      ⟨v, Data.V_le_U F v.property⟩ v.property
  · let A := upperUnipotent SL2FourNatural.F
    have hle : A.map (MulAut.conj b.conjugator).toMonoidHom ≤ A := by
      have hh : (A.map (MulAut.conj b.conjugator).toMonoidHom).map
          (alternatingActor d.naturalQuotient) ≤ A.map (alternatingActor d.naturalQuotient) := by
        rw [map_map, ←b.image]
        exact (map_mono (comap_mono earlier.placement)).trans_eq hmark
      intro x hx
      obtain ⟨y,hy,he⟩ := hh (mem_map_of_mem (alternatingActor d.naturalQuotient) hx)
      exact d.alternatingActor_injective he ▸ hy
    have he : A.map (MulAut.conj b.conjugator).toMonoidHom = A :=
      eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj b.conjugator).injective])
    have hg : b.conjugator ∈ rankOneBorel SL2FourNatural.F :=
      mem_normalizer_iff_map_conj_eq.mpr he
    obtain ⟨a,ha,ha1⟩ : ∃ a : SL2FourNatural.F, a ≠ 0 ∧ a ≠ 1 := by decide +kernel
    have hx : b.conjugator * diag2 a ha * b.conjugator⁻¹ ∈ rankOneBorel SL2FourNatural.F :=
      mul_mem (mul_mem hg (diag_mem_rankOneBorel a ha)) (inv_mem hg)
    have hm : alternatingActor d.naturalQuotient
        (b.conjugator * diag2 a ha * b.conjugator⁻¹) ∈ borel d.naturalQuotient :=
      mem_map.mpr ⟨_,hx,rfl⟩
    rw [←hborel.left_image] at hm
    obtain ⟨l,hl,he⟩ := hm
    exact ⟨l,hl,a,ha,ha1,he⟩

end Data.CriticalChart

theorem source_criticalChart_localActors (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hc : (upperRemark d structural).SectionCentralizer)
    (c : CriticalPath (L := L) F) (earlier : c.EarlierImages)
    (b : (upperRemark d structural).CriticalChart hc c) : b.LocalActors :=
  b.localActors_of_marked_source earlier
    (upperRemark_upperMarking d structural) (upperRemark_compatibleBorel d structural)
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
