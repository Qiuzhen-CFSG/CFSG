module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.Setup
public import Theory.GroupTheory.CharacteristicNormalizerRestriction

/-!
# Pushing up from a core in a relative Sylow join

Let X be a normal two-perfect subgroup of M ≤ H, let S be Sylow in M,
and put R = O₂(XS). If R is nontrivial and C(H,R) lies in M, then R is
radical in H and Sylow in its normal closure under M. This constructs the
literal C.2.3 setup without requiring S to be Sylow in H.

The proof is the relative form of A.4.2(7): A.4.2(5) makes R a maximal
X-signalizer in M. Its normalizer in H lies in M, so its normalizer's
core cannot enlarge R. The normal section centralizer in M contains the
M-normal closure of R, and A.4.2(4) supplies the required Sylow condition.
The application to original 13.1.12 is in Elimination.SourceControl.

Source: Aschbacher--Smith, A.4.2(4--7), printed p.57, and C.2.3, p.144.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalExclusions
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

/-- Construct C.2.3 from the literal local Sylow join and relative
characteristic-normalizer control, including its M-normal closure. -/
theorem pushingUp_setup_of_normal_sylow_core {κ : GroupClass} {H M X S R : Subgroup G}
    (hH : IsSQTK κ H) (hMH : M ≤ H) (hXM : X ≤ M)
    (hMX : M ≤ normalizer (X : Set G)) (hXP : IsPPerfect 2 X)
    (hS : IsSylowIn 2 S M) (he : R = (X ⊔ S).pCoreIn 2) (hne : R ≠ ⊥)
    (hcontrol : (R.subgroupOf H).characteristicNormalizerClosure ≤ M.subgroupOf H) :
    PushingUpSetup κ H R M := by
  have hRM : R ≤ M := he ▸ (pCoreIn_le 2 _).trans
    (sup_le hXM (isSylowIn_iff.mp hS).2.1)
  have hRH := hRM.trans hMH
  have hrne : R.subgroupOf H ≠ ⊥ := by
    intro hb
    apply hne
    simpa only [map_subgroupOf_eq_of_le hRH, Subgroup.map_bot] using
      congrArg (map H.subtype) hb
  have hNM : H ⊓ normalizer (R : Set G) ≤ M := by
    intro x hx
    have hxN : (⟨x,hx.1⟩ : H) ∈ normalizer (R.subgroupOf H : Set H) := by
      rw [← subgroupOf_normalizer_eq hRH]
      exact hx.2
    exact hcontrol (normalizer_le_characteristicNormalizerClosure_self _ hrne hxN)
  obtain ⟨P,hP⟩ := hS
  have hmax := normal_sylow_core_isMaximal X M hXM hMX hXP P
  rw [hP,← he] at hmax
  have hm := (isMaximalTwoSignalizer_iff _ _ _).mp hmax
  have hrad : IsPRadical 2 (R.subgroupOf H) := by
    let N := H ⊓ normalizer (R : Set G)
    have hXN : X ≤ N := le_inf (hXM.trans hMH) hm.1.normalizes
    have hRN : R ≤ N := le_inf hRH le_normalizer
    have hRB : R ≤ N.pCoreIn 2 := le_pCoreIn_of_normalizes hm.1.isPGroup hRN inf_le_right
    have hBN : X ≤ normalizer (N.pCoreIn 2 : Set G) := hXN.trans
      (N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N)))
    have hBR : N.pCoreIn 2 ≤ R := hm.2 _
      ((isTwoSignalizer_iff _ _ _).mpr
        ⟨(pCoreIn_le 2 N).trans hNM,isPGroup_pCoreIn 2 N,hBN⟩) hRB
    have hc : N.pCoreIn 2 = R := le_antisymm hBR hRB
    refine ⟨hrne,?_⟩
    apply map_injective H.subtype_injective
    change ((normalizer (R.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = _
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
      ← subgroupOf_normalizer_eq hRH,subgroupOf_map_subtype]
    simpa only [inf_comm,map_subgroupOf_eq_of_le hRH] using hc
  refine ⟨hH,hRH,hMH,hrad,hcontrol,?_⟩
  have hn : (X.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hMX
  have hsyl : IsSylowIn 2 R (twoSectionCentralizer X M) :=
    (maximal_signalizer_iff_sylow X M R hXM hn.isSubnormal hXP).mp hmax
  have hRC := signalizer_le_twoSectionCentralizer X M R hXM hn.isSubnormal hXP hm.1
  apply hsyl.restrict
  · have hr := map_mono (f := M.subtype) (le_normalClosure (H := R.subgroupOf M))
    simpa only [map_subgroupOf_eq_of_le hRM] using hr
  · let C := twoSectionCentralizer X M
    let _ : (C.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer
      (twoSectionCentralizer_normalized X M hMX)
    exact map_le_iff_le_comap.mpr
      (normalClosure_le_normal (N := C.subgroupOf M) (fun _ hr => hRC hr))

end CFSG.Quasithin.Chapter1.RadicalExclusions
