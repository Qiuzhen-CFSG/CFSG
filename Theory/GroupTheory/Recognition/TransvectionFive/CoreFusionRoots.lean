module
public import Theory.GroupTheory.Recognition.TransvectionFive.CoreFusionSeparation
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.CoreFusion.Transport
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceAction
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceAction
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneCoordinates

/-!
# The two noncentral root orbits in the marked point core

Every automorphism of the row group fixing the marked point is realized by
its full centralizer. Binary two-point transitivity therefore gives the
noncentral row orbit; the opposite marking gives the column orbit. The
proved mixed-orbit exclusion and the actual core normal form place every
point conjugate in one of these roots. Nonweak closure now forces at least
one full root group into the point class, without using simplicity.

This is Aschbacher, *Sporadic Groups* (1994), 39.1(5), 39.4–39.5,
pp.213–214. The original root subgroups and point are retained throughout.
The internal action import reuses its checked two-point transport without
changing that module's public boundary. The one-root alternative is handled
in the following source reduction and ultimately by the dimension-four
assembly owner.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.CoreFusion
open UniquenessLinear PlaneTensor
variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

include F in
private theorem point_ne_one : z ≠ 1 := by
  intro he
  have ho := F.point_orderOf
  simp [he] at ho

/-- The full point centralizer is transitive on the noncentral row roots. -/
theorem row_orbit (a b : G) (ha : a ∈ F.row) (hb : b ∈ F.row)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (haz : a ≠ z) (hbz : b ≠ z) :
    ∃ c : Subgroup.centralizer ({z} : Set G), (c : G)*a*(c : G)⁻¹ = b := by
  let p : F.row := ⟨z,point_mem_row F⟩
  let x : F.row := ⟨a,ha⟩
  let y : F.row := ⟨b,hb⟩
  have hp : p ≠ 1 := fun he => point_ne_one F (congrArg Subtype.val he)
  obtain ⟨f,hp',hf⟩ := row_aut_pair F p x p y hp
    (fun he => ha1 (congrArg Subtype.val he)) hp
    (fun he => hb1 (congrArg Subtype.val he))
    (fun he => haz (congrArg Subtype.val he).symm)
    (fun he => hbz (congrArg Subtype.val he).symm)
  obtain ⟨c,hc⟩ := exists_point_centralizer_row_action F f hp'
  exact ⟨c,(hc x).trans (congrArg Subtype.val hf)⟩

/-- The opposite marking gives the same orbit statement on the original column. -/
theorem column_orbit (a b : G) (ha : a ∈ F.column) (hb : b ∈ F.column)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (haz : a ≠ z) (hbz : b ≠ z) :
    ∃ c : Subgroup.centralizer ({z} : Set G), (c : G)*a*(c : G)⁻¹ = b := by
  apply row_orbit (oppositeMarking F) a b
  · simpa only [oppositeMarking_row] using ha
  · simpa only [oppositeMarking_row] using hb
  · exact ha1
  · exact hb1
  · exact haz
  · exact hbz

/-- Code 32 is the literal column root I+E₁₄ under the original marking. -/
theorem element32_mem_column : element F 32 ∈ F.column := by
  apply (F.mem_pullback_iff Model.column
    ⟨element F 32,F.pullback_le _ (element_mem F 32)⟩).mpr
  rw [element_model]
  have he : modelElement (decode 32) = root (by decide : (1 : Fin 5) < 4) := by
    apply Subtype.ext
    rw [modelElement_matrix]
    simp [decode,val,root,Matrix.SpecialLinearGroup.transvection_coe]
  change modelElement (decode 32) ∈ Model.column
  rw [he]
  exact subset_closure ⟨1,by decide,rfl⟩

theorem element32_ne_point : element F 32 ≠ z := by
  intro he
  have hh := element_injective F (he.trans (element_point F).symm)
  exact (by decide : (32 : PlaneCensus.Code) ≠ 4) hh

private theorem element_ne_one {x : PlaneCensus.Code} (hx : x ≠ 0) : element F x ≠ 1 := by
  intro he
  exact hx (element_injective F (he.trans (element_zero F).symm))

/-- Fusion of one noncentral row root is equivalent to fusion of every
nonidentity member of the original row subgroup. -/
theorem row_fusion_iff : IsConj z (element F 1) ↔
    ∀ a ∈ F.row, a ≠ 1 → IsConj z a := by
  constructor
  · intro h a ha ha1
    by_cases haz : a = z
    · rw [haz]
    obtain ⟨c,hc⟩ := row_orbit F (element F 1) a (element_one_mem_row F) ha
      (element_ne_one F (by decide)) ha1 (element_one_ne_point F) haz
    exact h.trans (isConj_iff.mpr ⟨(c:G),hc⟩)
  · intro h
    exact h _ (element_one_mem_row F) (element_ne_one F (by decide))

/-- The same characterization for the literal column subgroup. -/
theorem column_fusion_iff : IsConj z (element F 32) ↔
    ∀ a ∈ F.column, a ≠ 1 → IsConj z a := by
  constructor
  · intro h a ha ha1
    by_cases haz : a = z
    · rw [haz]
    obtain ⟨c,hc⟩ := column_orbit F (element F 32) a (element32_mem_column F) ha
      (element_ne_one F (by decide)) ha1 (element32_ne_point F) haz
    exact h.trans (isConj_iff.mpr ⟨(c:G),hc⟩)
  · intro h
    exact h _ (element32_mem_column F) (element_ne_one F (by decide))

variable [Finite G]

/-- Source 39.4 for every element of the actual point two-core: a point
conjugate lies in one of the two original root groups. -/
theorem core_conjugate_mem_roots (q : G)
    (hq : q ∈ (Subgroup.centralizer ({z} : Set G)).pCoreIn 2)
    (hf : IsConj z q) : q ∈ F.row ∨ q ∈ F.column := by
  by_contra h
  push Not at h
  have ho : orderOf q = 2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hf
    have he : MulAut.conj g z = q := hg
    rw [← he,MulEquiv.orderOf_eq,F.point_orderOf]
  obtain ⟨c,hc⟩ := UniquenessMathieu.SourceNormalizer.core_involution_conjugate
    F q hq ho h.1 h.2
  exact not_conjugate_core33 F (hf.trans (isConj_iff.mpr ⟨(c:G),hc⟩))

/-- Source 39.5: nonweak closure in the actual two-core fuses at least one
of the two noncentral root orbits to the distinguished point. -/
theorem root_fusion_disjunction (hcore : PointCoreFusion z) :
    IsConj z (element F 1) ∨ IsConj z (element F 32) := by
  obtain ⟨g,hq,hqz⟩ := hcore
  let q := g*z*g⁻¹
  have hf : IsConj z q := isConj_iff.mpr ⟨g,rfl⟩
  have hq1 : q ≠ 1 := fun he => point_ne_one F (isConj_one_left.mp (he ▸ hf))
  rcases core_conjugate_mem_roots F q hq hf with hr | hc
  · obtain ⟨c,he⟩ := row_orbit F q (element F 1) hr (element_one_mem_row F)
      hq1 (element_ne_one F (by decide)) hqz (element_one_ne_point F)
    exact Or.inl (hf.trans (isConj_iff.mpr ⟨(c:G),he⟩))
  · obtain ⟨c,he⟩ := column_orbit F q (element F 32) hc (element32_mem_column F)
      hq1 (element_ne_one F (by decide)) hqz (element32_ne_point F)
    exact Or.inr (hf.trans (isConj_iff.mpr ⟨(c:G),he⟩))

end Theory.GroupTheory.TransvectionFive.CoreFusion
