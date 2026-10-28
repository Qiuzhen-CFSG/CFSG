module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryMarkedProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.SourceCommutingOne

/-!
# The marked binary unitary profile for the actual mixed pair

The original A₅/S₃ quotient isomorphisms determine field orders four and
two on the literal reduced graph actors. The source orientation theorem
translates an arbitrary directed commuting critical edge to the base edge
without reversing criticality. Transporting both actor markings through
the original completion inclusion constructs the full U₄ profile, including
its exact core kernels and both elementary Sylow quotients.

The profile feeds the native U₄(2) presentation comparison on both reduced
endpoints and the entire Borel. The actual Chapter 14 marked quotient,
splitness and rotation order four remain explicit inputs; the original
Sylow extension and unconditional source classification are not asserted.
Source: DGS, Groups and Graphs (1985), (11.7), pp.174--175, and Theorem D,
p.224; Aschbacher--Smith F.1.12(I), pp.262--264.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo Reduction MixedDGS
open Theory.GroupTheory.RankTwoAmalgam OriginalExtension SuzukiContainment
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {G : Type*} [Group G] [Finite G] {K U S : Subgroup G}
local notation "F" => reducedFamily ![K,U] S
local notation "G₀" => Reduction.G₀ ![K,U] S

/-- The actual mixed markings construct the complete binary U₄ profile. -/
theorem mixed_commuting_one_marked_profile (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {a beta : Vertex F} (hc : IsCriticalPair F a beta)
    (hb : DGS85.b F = 1) (hcomm : ⁅Z F a,Z F beta⁆ = ⊥) :
    Nonempty (Assembly.UnitaryFourSource.Profile ![K,U] (reducedSylow ![K,U] S)
      (GaloisField 2 2) (ZMod 2) false) := by
  obtain ⟨hc',hcomm'⟩ := commuting_one_base_critical h eK eU hc hb hcomm
  let ea := (graphLocalGroup F (base F false)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let eb := (graphLocalGroup F (base F true)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let qa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let qb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  exact original_elementary_marked_profile_of_linear h hc' hb hcomm' (m := 1) (by decide)
    (by simpa using GaloisField.card 2 2 (by decide))
    (by norm_num [Nat.card_zmod])
    (qa.symm.trans (graph_linear_four h eK (base F false) rfl).some)
    (qb.symm.trans (graph_linear_two h eU (base F true) rfl).some)

/-- The literal mixed profile supplies the marked U₄(2) comparison at the fixed degree one. -/
theorem mixed_commuting_one_reduced_comparison (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {a beta : Vertex F} (hc : IsCriticalPair F a beta)
    (hb : DGS85.b F = 1) (hcomm : ⁅Z F a,Z F beta⁆ = ⊥)
    {X : Type*} [Group X] {endpoints : Fin 2 → Subgroup X}
    (quot : MarkedQuotient endpoints)
    (e : Iso (reducedAmalgam ![K,U] S) quot.standardAmalgam)
    (split : SplitData quot.tits) (hrot : rotationOrder quot = 4) :
    Nonempty (Iso (reducedAmalgam ![K,U] S) (UnitaryFourNative.amalgam 1 (by decide) false)) := by
  obtain ⟨profile⟩ := mixed_commuting_one_marked_profile h eK eU hc hb hcomm
  exact ⟨Assembly.UnitaryFourSource.reducedComparison h quot e split hrot false profile 1
    (by norm_num [Nat.card_zmod])⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
