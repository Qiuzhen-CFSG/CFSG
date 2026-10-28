module
public import Theory.GroupTheory.ElementaryEightParabolicRecognition
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.ConjugateSpanOrder
public import Stellmacher.OmegaOneCenterMap

/-!
# A full elementary-eight automizer generates from the Sylow center

An elementary eight normalized by a Sylow two-subgroup meets that Sylow's
center nontrivially. Every nonidentity element is conjugate to that central
involution when the normalizer induces the full automorphism group. Hence
the eight lies in the normalizer span of the Sylow's central involutions.

This supplies the actual local-module containment needed to apply
Aschbacher--Smith 14.1.6 to the Omega extension in 15.1.11, printed p.1089.
-/

public section
open Subgroup Stellmacher
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem elementaryEight_le_sylowCenter_normalizer_span (T : Sylow 2 G) (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (hET : E ≤ T) (hTN : (T : Subgroup G) ≤ normalizer (E : Set G))
    (hfull : Function.Surjective E.normalizerMonoidHom) :
    E ≤ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (normalizer (E : Set G)) := by
  let N := E.subgroupOf (T : Subgroup G)
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hET).mpr hTN
  have hN : Nat.card N = 8 := (Nat.card_congr (subgroupOfEquivOfLe hET).toEquiv).trans hE
  let : Nontrivial N := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  obtain ⟨z,hz,hzc⟩ := exists_nontrivial_center_mem_normal (p := 2) N
  let ze : E := ⟨((z : T) : G), z.property⟩
  have hze : ze ≠ 1 := by
    intro h
    exact hz (Subtype.ext (Subtype.ext (congrArg (fun a : E => (a : G)) h)))
  have hzZ : (ze : G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨(z : T).property, ?_, ?_⟩
    · exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (ze : G) ze.property
    · intro t ht
      exact congrArg (fun a : T => (a : G)) (mem_center_iff.mp hzc ⟨t,ht⟩)
  intro x hx
  by_cases hxe : x = 1
  · exact hxe ▸ one_mem _
  obtain ⟨a,ha⟩ := ElementaryEightParabolic.automorphism_transitive ze (⟨x,hx⟩ : E)
    hze (by exact fun h => hxe (congrArg Subtype.val h))
  obtain ⟨g,rfl⟩ := hfull a
  exact subset_closure ⟨g, g.property, ze, hzZ, congrArg Subtype.val ha⟩

end Subgroup
