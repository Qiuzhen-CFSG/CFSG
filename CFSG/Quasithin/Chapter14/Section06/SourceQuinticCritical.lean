module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.IndexFiveStructure
public import CFSG.Quasithin.Chapter14.Section06.SourceQuadraticBound
public import CFSG.Quasithin.ChapterF.Section09.CriticalEndpoints

/-!
# Original quintic critical endpoints

The original plane-source hypotheses construct F.9 on the literal pair
X=YT and H, with Vplus=V. They place the actual closure U in O₂(H) and
make intersecting conjugates of V commute. The proved F.7/F.9 geometry
therefore gives an odd critical distance at least three and a normalized
endpoint. Its one conjugator is retained on H, U and the original central
point; the noncentral action is on the same marked quotient.

The index-five closure theorem gives the elementary U of order32or64.
This supplies the critical configuration for the asymmetric marked
amalgam recognition. No radius bound, endpoint, action or model witness
is an extra hypothesis.

Source: Aschbacher--Smith14.6.12(2), pp.1030--1031, referring to14.2.21,
p.988; F.9.10--13, pp.321--322, for the critical endpoint geometry.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

/-- The literal F.9 source track has odd radius at least three and an
actual normalized critical endpoint, without any geometric premise. -/
theorem source_rankTwo_critical_track_bounds
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G)) :
    let E : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let h : E.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH
    3 ≤ h.b ∧ Odd h.b ∧ Nonempty h.CriticalEndpoint := by
  dsimp only
  let E : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let h : E.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH
  have hcore : E.V ≤ E.QH := (le_conjugateSpanBy _ _).trans h.UH_le_QH
  have hc := source_rankTwo_intersecting_conjugates_commute hG T hempty hM hu hmany hcard e hab
  have hb := h.b_bounds_of_intersecting_conjugates_commute hcore hc
  exact ⟨hb.1,hb.2,h.criticalEndpoint_nonempty hcore hc⟩

/-- The source quintic branch supplies one actual conjugator on every
endpoint label, including the noncentral action on the marked central quotient. -/
theorem source_quintic_critical_conjugate
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let V := localModule T M
    let U := conjugateSpanBy V H
    IsElementaryAbelian 2 U ∧ (Nat.card U = 32 ∨ Nat.card U = 64) ∧
      ∃ g : G, g ∈ (sourceResidual M Mc ⊔ (T : Subgroup G)) ⊔ H ∧
        U.map (MulAut.conj g).toMonoidHom ≤ H ∧
        U ≤ H.map (MulAut.conj g).toMonoidHom ∧
        ⁅U,U.map (MulAut.conj g).toMonoidHom⁆ ≤
          U ⊓ U.map (MulAut.conj g).toMonoidHom ∧
        ¬ ⁅U.map (MulAut.conj g).toMonoidHom,V⁆ ≤
          (centralInvolutions T).map (MulAut.conj g).toMonoidHom := by
  let E : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let h : E.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH.1
  obtain ⟨hb,_,⟨i⟩⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hu hmany hcard e hab H hH.1
  obtain ⟨hU,hcardU⟩ := Section02.SolvableAmalgam.source_index_five_closure_structure
    hG T hempty hM hu hmany hcard e H hH.1 hi
  exact ⟨hU,hcardU,i.representative,(i : ChapterF.Section09.Setup.Hypothesis.G₀ (D := E)).property,
    i.large_le hb,i.reverse_le hb,i.commutator hb,i.noncentral⟩

end CFSG.Quasithin.Chapter14.Section06
