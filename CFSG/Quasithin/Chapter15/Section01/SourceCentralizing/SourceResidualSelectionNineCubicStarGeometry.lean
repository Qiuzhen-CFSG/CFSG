module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineCubicMarkedGeometry
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableStarCore
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# The original Nine line acts nontrivially inside the star module

The original fixed four-group E is the join of the marked line Z1 and
the central seed Z. The marked line centralizes L. Since L escapes
M_Z = C_G(E), its fixed subgroup on E is exactly Z1, and its nonzero
displacement on E is its displacement on the original central seed Z.

The actual C.2.7 input places E and its L-conjugate span inside the full
star module. This does not identify that span with the whole star module
or the intrinsic commutator core.

Source: Aschbacher--Smith C.2.7, p.146, and 15.1.17--20,
printed pp.1093--1095.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The marked line is the full fixed part of E, and the original remaining
line accounts for all of its nontrivial component displacement. -/
theorem marked_four_star_geometry (d : CaseIComponentData T M Mc V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (E Z : Subgroup G) [IsElementaryAbelian 2 E]
    (hfour : Nat.card E = 4) (hZ1 : Nat.card d.Z1 = 2)
    (hgen : d.Z1 ⊔ Z = E) (hMZ : d.MZ = centralizer (E : Set G)) :
    E ≤ (starV d.L d.Q1).map (d.L ⊔ d.Q1 : Subgroup G).subtype ∧
      conjugateSpanBy E d.L ≤
        (starV d.L d.Q1).map (d.L ⊔ d.Q1 : Subgroup G).subtype ∧
      E ⊓ centralizer (d.L : Set G) = d.Z1 ∧
      ⁅d.L,E⁆ = ⁅d.L,Z⁆ ∧ ⁅d.L,Z⁆ ≠ ⊥ := by
  obtain ⟨hEV,hspan,hmove⟩ := d.marked_core_star_geometry hi E hMZ
  have hZ1E : d.Z1 ≤ E := le_sup_left.trans_eq hgen
  have hZE : Z ≤ E := le_sup_right.trans_eq hgen
  have hZ1C : d.Z1 ≤ centralizer (d.L : Set G) :=
    le_centralizer_iff.mp d.L_component.1
  have hlow : d.Z1 ≤ E ⊓ centralizer (d.L : Set G) := le_inf hZ1E hZ1C
  have hfix : E ⊓ centralizer (d.L : Set G) = d.Z1 := by
    have hcardlow : 2 ≤ Nat.card (E ⊓ centralizer (d.L : Set G) : Subgroup G) := by
      rw [←hZ1]
      exact card_le_of_le hlow
    have hcardhigh : Nat.card (E ⊓ centralizer (d.L : Set G) : Subgroup G) ≤ 4 :=
      (card_le_of_le inf_le_left).trans_eq hfour
    have hdiv : Nat.card (E ⊓ centralizer (d.L : Set G) : Subgroup G) ∣ 4 :=
      hfour ▸ card_dvd_of_le inf_le_left
    have hne4 : Nat.card (E ⊓ centralizer (d.L : Set G) : Subgroup G) ≠ 4 := by
      intro he
      have hfull : E ⊓ centralizer (d.L : Set G) = E :=
        eq_of_le_of_card_ge inf_le_left (by rw [hfour,he])
      exact hmove (commutator_eq_bot_iff_le_centralizer.mpr
        (hfull ▸ (inf_le_right : E ⊓ centralizer (d.L : Set G) ≤ centralizer (d.L : Set G))))
    have hne3 : Nat.card (E ⊓ centralizer (d.L : Set G) : Subgroup G) ≠ 3 := by
      intro he
      rw [he] at hdiv
      norm_num at hdiv
    exact (eq_of_le_of_card_ge hlow (by rw [hZ1]; omega)).symm
  have hEQ : E ≤ d.Q1 := fun a ha =>
    ((mem_omegaOneCenterAmbient_iff _ _).mp
      (d.le_omegaCenter_radical_of_marked_centralizer E hMZ ha)).1
  have hcomm : ⁅d.L,E⁆ = ⁅d.L,Z⁆ :=
    (commutator_eq_of_centralizing_sup hgen hZ1C
      ((hZE.trans hEQ).trans hi.normalizes)).symm
  refine ⟨hEV,hspan,hfix,hcomm,?_⟩
  intro hb
  apply hmove
  rw [commutator_comm,hcomm,hb]

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The same actual Nine component moves the original central seed inside
the full star module, and fixes exactly the original marked line in E. -/
theorem PreparedChosenModule.nine_marked_star_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hstrict : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict <
        ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)
    (d : CaseIComponentData T M Mc V) (hr : d.row = .four)
    (g : d.ExchangedPlaneGeometry)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L) :
    thompsonFixed T V ≤ (starV d.L d.Q1).map (d.L ⊔ d.Q1 : Subgroup G).subtype ∧
      conjugateSpanBy (thompsonFixed T V) d.L ≤
        (starV d.L d.Q1).map (d.L ⊔ d.Q1 : Subgroup G).subtype ∧
      thompsonFixed T V ⊓ centralizer (d.L : Set G) = d.Z1 ∧
      ⁅d.L,thompsonFixed T V⁆ = ⁅d.L,centralInvolutions T⁆ ∧
      ⁅d.L,centralInvolutions T⁆ ≠ ⊥ := by
  obtain ⟨_,_,hgen,hMZ,_⟩ := h.nine_marked_core_geometry
    hG T hempty hM hmany hJ hu hne hfull h9 hstrict d hr g
  have hfour := (h.nine_fixed_card_of_strict_thompson_image
    hG T hempty hM hmany hJ h9 hstrict).2
  have hZ1 : Nat.card d.Z1 = 2 := by
    rcases g.sizes with hs | hs
    · exact hs.2.1
    · cases hr.symm.trans hs.1
  let := h.elementary
  let : IsElementaryAbelian 2 (thompsonFixed T V) := IsElementaryAbelian.of_le inf_le_left
  exact d.marked_four_star_geometry hi _ _ hfour hZ1 hgen hMZ

end CFSG.Quasithin.Chapter15.Section01
