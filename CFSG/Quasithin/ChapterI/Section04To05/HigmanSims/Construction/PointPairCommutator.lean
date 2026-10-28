module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SeedPointTypes
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreLifts

/-!
# The commutator of lifts in distinct original HS point cores

If two point-core elements centralize each other's marked seed points,
their commutator lies in both literal point cores. The two square maps
take values in distinct involution lines, so this commutator squares to one.
This removes the order-four commutator obstruction in the dual-plane lift
construction, directly from HS1--HS2.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

omit [Finite G] in
private theorem commutator_mem_core (H : Subgroup G) (a b : G)
    (ha : a ∈ H.pCoreIn 2) (hb : b ∈ H) : ⁅a, b⁆ ∈ H.pCoreIn 2 := by
  obtain ⟨aH, haH, rfl⟩ := ha
  have hh : ⁅aH, (⟨b, hb⟩ : H)⁆ ∈ pCore 2 H :=
    commutator_le_left (pCore 2 H) ⊤
      (commutator_mem_commutator haH (mem_top _))
  exact ⟨⁅aH, (⟨b, hb⟩ : H)⁆, hh, rfl⟩

omit [Finite G] in
/-- Mutual point centralization places the commutator in both actual point cores. -/
theorem point_core_pair_commutator_mem (u v a b : G)
    (ha : a ∈ (involutionCentralizer u).pCoreIn 2)
    (hb : b ∈ (involutionCentralizer v).pCoreIn 2)
    (hav : a ∈ involutionCentralizer v) (hbu : b ∈ involutionCentralizer u) :
    ⁅a, b⁆ ∈ (involutionCentralizer u).pCoreIn 2 ⊓
      (involutionCentralizer v).pCoreIn 2 := by
  refine ⟨commutator_mem_core _ a b ha hbu, ?_⟩
  have hh := ((involutionCentralizer v).pCoreIn 2).inv_mem
    (commutator_mem_core _ b a hb hav)
  rw [commutatorElement_inv] at hh
  exact hh

private theorem involution_line_mem {u c : G} (hu : orderOf u = 2)
    (hc : c ∈ zpowers u) : c = 1 ∨ c = u := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hu] at hc
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hc
  have hn2 : n < 2 := Finset.mem_range.mp hn
  interval_cases n <;> simp

/-- Lifts in distinct seed-point cores have square-one commutator whenever
they centralize each other's marked seed points. -/
theorem TypeAt.point_core_pair_commutator_square (h : TypeAt z V)
    (u v : G) (hu : u ∈ V) (hv : v ∈ V) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u ≠ v) (a b : G)
    (ha : a ∈ (involutionCentralizer u).pCoreIn 2)
    (hb : b ∈ (involutionCentralizer v).pCoreIn 2)
    (hav : a ∈ involutionCentralizer v) (hbu : b ∈ involutionCentralizer u) :
    ⁅a, b⁆ ^ 2 = 1 := by
  have htypeu := h.at_seed_point u hu hu1
  have htypev := h.at_seed_point v hv hv1
  have hm := point_core_pair_commutator_mem u v a b ha hb hav hbu
  have hsu := htypeu.centralizer_core_square_mem ⁅a, b⁆ hm.1
  have hsv := htypev.centralizer_core_square_mem ⁅a, b⁆ hm.2
  rcases involution_line_mem htypeu.involution hsu with hs | hs
  · exact hs
  rcases involution_line_mem htypev.involution hsv with ht | ht
  · exact ht
  exact (huv (hs.symm.trans ht)).elim

end CFSG.Quasithin.HigmanSims
