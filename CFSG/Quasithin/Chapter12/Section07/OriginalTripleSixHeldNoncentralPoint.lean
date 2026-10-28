module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldPointTI
public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion
import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# The original ordinary point is disjoint from every Sylow center

The literal point centralizer contains its ordinary component, so it cannot
have characteristic two. Thus it contains no full ambient Sylow two-subgroup.
Actual scalar transitivity transports this to every nonidentity point element:
the whole field point meets the center of every ambient Sylow trivially.

Source: Aschbacher--Smith12.7.7, printed p.841, the non-2-centrality step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual escaping point centralizer contains no ambient Sylow
subgroup, by its ordinary component and the original even-characteristic hypothesis. -/
theorem original_tripleSix_held_point_not_twoCentral
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (D : ChosenModule T K U) (t : U) (ht : t ≠ 1)
    (hB : let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      IsComponent H ((conjugateSpanBy Lt H).subgroupOf H))
    (S : Sylow 2 G) : ¬ (S : Subgroup G) ≤ centralizer ({(t : G)} : Set G) := by
  intro hS
  let := D.elementary
  have ht2 : orderOf (t : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (t : G) t.property)
    (fun he => ht (Subtype.ext he))
  have hc := Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le
    S (h.simpleQTKE.evenCharacteristic S) (isTwoLocal_involution_centralizer ht2) hS)
  exact not_isComponent_of_twoCore hc _ hB

/-- Every element of the original field point is noncentral in every
ambient Sylow, except for the identity. The scalar witnesses are actual elements of X. -/
theorem original_tripleSix_held_point_inf_sylow_center_eq_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (hB : let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      IsComponent H ((conjugateSpanBy Lt H).subgroupOf H))
    (S : Sylow 2 G) : tripleSixPoint D a t ⊓ centerIn (S : Subgroup G) = ⊥ := by
  apply le_bot_iff.mp
  intro v hv
  by_contra hv1
  have ht1 : (t : G) ≠ 1 := fun he => ht (Subtype.ext he)
  obtain ⟨x,_,hx⟩ := (tripleSixScalarResidual_point_transitive D a t).2
    t (tripleSixPoint_properties D a t ht).1 ht1 v hv.1 hv1
  let b := MulAut.conj x⁻¹
  let R := S.mapSurjective (f := b.toMonoidHom) b.surjective
  apply original_tripleSix_held_point_not_twoCentral h D t ht hB R
  rintro y ⟨s,hs,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have hcomm : s*v=v*s := hv.2.2 s hs
  change (x⁻¹*s*(x⁻¹)⁻¹)*(t:G)=(t:G)*(x⁻¹*s*(x⁻¹)⁻¹)
  rw [inv_inv]
  calc
    (x⁻¹*s*x)*(t:G) = x⁻¹*(s*(x*(t:G)*x⁻¹))*x := by group
    _ = x⁻¹*((x*(t:G)*x⁻¹)*s)*x := by rw [hx,hcomm]
    _ = (t:G)*(x⁻¹*s*x) := by group

end CFSG.Quasithin.Chapter12.Section07
