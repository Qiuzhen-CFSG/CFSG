module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneRThreeClassCoordinates

/-!
# Elations fixing the raw base flag lie in the original Borel image

An elation fixing an incident point-line pair has that point as its center
or that line as its axis. This follows from the fixed-point theorem and its
dual, followed by uniqueness of the line through two points. Lift a raw
neighbor to the tree to move each such flag from the original base flag by
an element of the corresponding original endpoint. The full flag-elation
comparison then gives a representative in that endpoint's two-core, which
lies in the whole original Borel.

All equalities concern the literal apartment quotient map. No equality of
arbitrary class stabilizers with endpoint images, kernel-orbit lifting, or
marked BN quotient is assumed. The actual path roots must still be shown
to act as elations before applying this to the source root signs.
Source: DGS, *Groups and Graphs* (1985), (3.7), p.80, in the centerless r=3
branch of (10.5), p.156.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam Configuration
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange

private theorem elation_fixed_flag {H P M : Type*} [Group H] [Membership P M]
    [MulAction H P] [MulAction H M] [IsCollineationAction H P M]
    [Finite P] [Finite M] [ProjectivePlane P M]
    {g : H} {C p : P} {l m : M} (he : IsElation g C l)
    (hpm : p ∈ m) (hp : g • p = p) (hm : g • m = m) : C = p ∨ l = m := by
  have hpl : p ∈ l := by
    by_contra hh
    exact he.smul_ne_of_not_mem_axis hh hp
  have hCm : C ∈ m := by
    let : MulAction H (Configuration.Dual P) := inferInstanceAs (MulAction H P)
    let : MulAction H (Configuration.Dual M) := inferInstanceAs (MulAction H M)
    let : IsCollineationAction H (Configuration.Dual M) (Configuration.Dual P) :=
      ⟨fun g m p => IsCollineationAction.smul_mem_smul_iff (H := H) (P := P) (L := M) g p m⟩
    have hd : IsElation (P := Configuration.Dual M) (L := Configuration.Dual P) g l C :=
      ⟨he.incident, he.fixes_center_lines, he.fixes_axis_points, he.moves.symm⟩
    by_contra hh
    exact hd.smul_ne_of_not_mem_axis (P := Configuration.Dual M) (L := Configuration.Dual P)
      (p := m) hh hm
  exact Nondegenerate.eq_or_eq he.incident hpl hCm hpm

namespace ReducedCartan
universe uF
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {h : HypothesisF11 L S} {c : CompatibleCartans L (reducedSylow L S)}
variable (ds : ∀ j : Bool, FullCartanReflectionProfile.{uF} h c j)
local notation "A" => reducedAmalgam L S
local notation "X" => RankTwoAmalgam.Universal (reducedAmalgam L S)
local notation "U" => fullCartanUniversalCore (L := L) (S := S)
local notation "Pt" => fullCartanClassPoint ds
local notation "Ln" => fullCartanClassLine ds
local notation "axis" => fullCartanClassAxis ds
local notation "center" => fullCartanClassCenter ds
local notation "T" => cartanApartment A (apartmentGroup c (fullCartanPathRoots ds))
local notation "n" => fullCartanPathLength ds
local notation "r" => sourceRelation A T n
local notation "q" => quotientMap A T n
local notation "ψ" => fullCartanClassCollineation ds
variable (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4)

include hr in
/-- Original endpoint elements move to every raw neighbor, by the proved local cover. -/
theorem fullCartanClass_neighbor_transitive (i : Bool) (v : fullCartanClassFiber ds (!i))
    (hv : (fullCartanClassGraph ds).Adj (fullCartanClassBase ds i).val v.val) :
    ∃ a ∈ Universal.cosetFamily A i, a • fullCartanClassBase ds (!i) = v := by
  obtain ⟨u, hu, hvu⟩ := classGraph_neighbor_lift
    (fullCartan_source_neighbor_lifting_of_r_three ds hr) hv
  obtain ⟨a, ha, hau⟩ := RankTwo.neighbor_base_rep (Universal.cosetFamily A) i hu
  have haBase : a • base (Universal.cosetFamily A) (!i) = u := by
    change a • RankTwo.mkVertex (Universal.cosetFamily A) (!i) 1 = u
    simpa only [RankTwo.smul_mkVertex, mul_one] using hau
  exact ⟨a, ha, Subtype.ext ((congrArg (Quotient.mk r) haBase).trans hvu)⟩

include hr in
theorem fullCartanClass_conjugated_flagElations_mem_borel (i : Bool) (a : X)
    (ha : a ∈ Universal.cosetFamily A i) (g : X)
    (hg : ψ g ∈ TranslationPlane.flagElations (a • center) (a • axis)) :
    q g ∈ (originalMiddle A).map q := by
  have hconj : ψ a * ψ (a⁻¹*g*a) * (ψ a)⁻¹ = ψ g := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  have hh : ψ (a⁻¹*g*a) ∈ TranslationPlane.flagElations center axis := by
    apply (TranslationPlane.flagElations_conjugate_mem_iff center axis (ψ a) (ψ (a⁻¹*g*a))).mp
    rw [hconj]
    exact hg
  obtain ⟨z, hz, he⟩ := fullCartanClass_flagElations_lift ds hr (a⁻¹*g*a) hh
  have hzU : z ∈ U i := by cases i; exact hz.2; exact hz.1
  have hn : a ∈ normalizer (U i : Set X) :=
    normalizer_le_normalizer_characteristic_image (Universal.cosetFamily A i)
      (pCore 2 (Universal.cosetFamily A i)) ((Universal.cosetFamily A i).le_normalizer ha)
  have haz : a*z*a⁻¹ ∈ U i := (mem_normalizer_iff.mp hn z).mp hzU
  refine ⟨a*z*a⁻¹, universal_endpoint_core_le_middle h i haz, ?_⟩
  calc
    q (a*z*a⁻¹) = q a * q z * (q a)⁻¹ := by rw [map_mul, map_mul, map_inv]
    _ = q a * q (a⁻¹*g*a) * (q a)⁻¹ := by rw [he]
    _ = q g := by rw [map_mul, map_mul, map_inv]; group

include hr in
/-- The same quotient image of every elation fixing the raw base flag lies in the original Borel. -/
theorem fullCartanClass_elation_mem_borel (g : X) {C : Pt} {l : Ln}
    (he : IsElation g C l) (hp : g • center = center) (hl : g • axis = axis) :
    q g ∈ (originalMiddle A).map q := by
  let := fullCartanClassPlane ds hr
  rcases elation_fixed_flag he (fullCartanClass_incident ds hr) hp hl with hC | hL
  · subst C
    obtain ⟨a, ha, hal⟩ := fullCartanClass_neighbor_transitive ds hr false l he.incident
    change a • axis = l at hal
    apply fullCartanClass_conjugated_flagElations_mem_borel ds hr false a ha g
    rw [fullCartanClassBase_fixed ds false ha, hal]
    exact ⟨he.fixes_axis_points, he.fixes_center_lines⟩
  · subst l
    obtain ⟨a, ha, haC⟩ := fullCartanClass_neighbor_transitive ds hr true C he.incident.symm
    change a • center = C at haC
    apply fullCartanClass_conjugated_flagElations_mem_borel ds hr true a ha g
    rw [fullCartanClassBase_fixed ds true ha, haC]
    exact ⟨he.fixes_axis_points, he.fixes_center_lines⟩

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
