module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.LocalGeometry.Sylow
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.LocalGeometry.Generation
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.LocalGeometry.Perfect

/-!
# Assembling the natural geometry from its end-node orbit

The common marked flag now supplies every clause of the parabolic geometry
except the orbit of the two ends under T. In particular perfection concerns
the original residual join, and generation is the literal product with
C_M(V). The orbit remains a source obligation on the same parabolic triple;
it is not inferred from its abstract quotient types.

Source: Aschbacher--Smith, 15.1.29, printed pp.1103--1104.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.Section05To06
open CFSG.Quasithin.Chapter15.Section03
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {t : G}

/-- On the selected natural flag, the only remaining geometry premise is
the action of T on the actual two end-node residuals. -/
theorem geometry_of_end_orbit (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource)
    (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t)
    (horbit : ∀ x ∈ (T : Subgroup G),
      a.parabolics.Y2.map (MulAut.conj x).toMonoidHom = a.parabolics.Y2 ∨
        a.parabolics.Y2.map (MulAut.conj x).toMonoidHom = a.parabolics.Y3) :
    NaturalParabolicGeometry a.parabolics := by
  let s := hs.1.nineSource_of_natural_moved_module hM hu h t ht htS hnat
  exact {
    parabolics_le := a.parabolics_le
    sylow_le := a.sylow_le
    first_le := a.first_le_selected hG hM hJ hu h hfull hs ht htS hnat
    first_core := a.first_core hG hM hu h hs ht htS hnat
    second_supplement := a.second_supplement hs.1
    second_join := a.second_join hG hM hu h hs ht htS hnat
    adjacent_not_sylow := a.adjacent_not_sylow s hM h
    remote_sylow := a.remote_sylow hG hM hu h hs ht htS hnat
    end_orbit := horbit
    perfect := a.pair_perfect
    moving := a.first_moves_movingPlane hG hM hu h hs ht htS hnat
    product := a.first_product hG hM hJ hu h hfull hs ht htS hnat }
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag
