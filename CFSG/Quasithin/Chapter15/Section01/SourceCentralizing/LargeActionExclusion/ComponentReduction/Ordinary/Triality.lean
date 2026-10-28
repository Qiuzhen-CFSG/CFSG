module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction
public import Theory.SpecificGroups.Triality.ElementarySylowFixers

/-!
# The ordinary triality branch on the exchanged source component

The intrinsic Sylow-fixer bound proves the omega-center bound in the literal
normalizer action. The marked ordinary source already gives normalization by
the original central involutions. The separate triality cubic-residual theorem
then transfers residual escape to the actual intersection M ∩ L, proving the
centralizer equality in 15.1.22(4). Fixed-plane movement contradicts it for
both exchanged plane sizes. No outer two-group assertion is used.

Source: Aschbacher--Smith 15.1.22(**),(4), 15.1.25(1),(3), and 15.1.26,
printed pp.1099,1102.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Original 15.1.22's equality for the genuine triality quotient, retaining
the central cover and the same marked component and cubic residual. -/
theorem ExchangedSource.ordinary_triality_centralizer {d : CaseIComponentData T M Mc V}
    (s : d.ExchangedSource) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (j : (d.L ⧸ pCore 2 d.L) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) :
    d.S ⊓ centralizer (((primeToResidual 3 (M ⊓ d.L : Subgroup G)).map
      (M ⊓ d.L).subtype) : Set G) = d.S ⊓ centralizer (d.L : Set G) := by
  let := s.quasisimple
  let := h.elementary
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hM.1.2)
    simpa only [map_subgroupOf_eq_of_le h.le_selected, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hM.1.2] using map_mono (f := M.subtype) hh
  have o := s.ordinary hL
  apply d.ordinary_residual_centralizer_of_model hM.1.2 hu hL
    o.center_eq o.center_two o.central_normalizes s.component_sylow
    ((d.Z1_le_fixed.trans inf_le_left).trans hVT) j
    (fun P A hA hfix => @Triality.Standard.binary_two_elementary_sylow_fixer_card_le_two
      P A hA hfix)
  have hY := (d.source_triality_cubic_component hG h j).2
  rw [← hY]
  exact s.cubic_escape

/-- Neither exchanged source row can have an ordinary triality component. -/
theorem ExchangedSource.not_ordinary_triality {d : CaseIComponentData T M Mc V}
    (s : d.ExchangedSource) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) :
    ¬ Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) := by
  rintro ⟨j⟩
  exact s.triality_no_equal_centralizers hG hM.1.2 h j
    (s.ordinary_triality_centralizer hG hM hu h hL j)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
