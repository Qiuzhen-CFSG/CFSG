module

public import Theory.GroupTheory.QuaternionSwapModel.MarkedSylow.UniqueSixteen
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SecondParabolic.Overlap
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Automorphisms
public import Theory.Mathieu.M23.QuasithinGeometry.ElementarySylow.Checks
public import Theory.Mathieu.M23.Properties.ElementarySylowFixers

/-!
# Distinguishing the outer Mathieu Sylow from M₂₂ and M₂₃

The marked Aut(M₁₂) Sylow has a unique elementary subgroup of order 16.
The two checked elementary sixteens in M₂₃ are distinct. M₂₂ embeds
with odd index in M₂₃ and hence has the same Sylow type. This distinguishes
the actual Sylow groups without a subgroup classification assumption.
Source: Aschbacher–Smith F.6.18(13), H.14.2(1), and 14.2.21.
-/

public section
open Subgroup
namespace Sporadic.Mathieu
open Theory.GroupTheory

theorem aut_m12_sylow_unique_elementary_sixteen :
    ∃! E : Subgroup M12ExceptionalExtension.overlap,
      IsElementaryAbelian 2 E ∧ Nat.card E = 16 :=
  (M12ExceptionalExtension.SecondCoordinates.geometry
    M12ExceptionalExtension.innerModel).existsUnique_elementary_sixteen

namespace M23Geometry.ElementarySylow
open FusionCertificate

theorem candidate_zero_ne_one : candidate 0 ≠ candidate 1 := by
  intro he
  let x : M23 := ⟨perm (candidateIndex 0 1), rawSubgroup_le (perm_mem _)⟩
  have hx : x ∈ candidate 0 := ⟨1,rfl⟩
  rw [he] at hx
  obtain ⟨i, hi⟩ := hx
  have hj : candidateIndex 1 i = candidateIndex 0 1 := perm_injective hi
  have hn : ∀ i : Fin 16, candidateIndex 1 i ≠ candidateIndex 0 1 := by decide +kernel
  exact hn i hj

theorem not_unique_elementary_sixteen :
    ¬ ∃! E : Subgroup subgroup, IsElementaryAbelian 2 E ∧ Nat.card E = 16 := by
  rintro ⟨E,_,hu⟩
  have hc (b : Fin 2) : Nat.card ((candidate b).subgroupOf subgroup) = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe (candidate_le_sylow b)).toEquiv).trans (candidate_card b)
  have he (b : Fin 2) : IsElementaryAbelian 2 ((candidate b).subgroupOf subgroup) := by
    let := candidate_elementary b
    exact IsElementaryAbelian.subgroupOf (candidate_le_sylow b)
  have hh := (hu _ ⟨he 0,hc 0⟩).trans (hu _ ⟨he 1,hc 1⟩).symm
  apply candidate_zero_ne_one
  have hm := congrArg (Subgroup.map subgroup.subtype) hh
  simpa only [subgroupOf_map_subtype, inf_of_le_left (candidate_le_sylow _)] using hm
end M23Geometry.ElementarySylow
end Sporadic.Mathieu

namespace Sporadic.Mathieu
open Theory.GroupTheory

theorem m23_sylow_not_unique_elementary_sixteen (P : Sylow 2 M23) :
    ¬ ∃! E : Subgroup P, IsElementaryAbelian 2 E ∧ Nat.card E = 16 := by
  intro h
  exact M23Geometry.ElementarySylow.not_unique_elementary_sixteen
    (existsUnique_elementary_subgroup_of_equiv
      (P.equiv M23Geometry.FusionCertificate.sylow) h)

theorem m22_sylow_not_unique_elementary_sixteen (P : Sylow 2 M22) :
    ¬ ∃! E : Subgroup P, IsElementaryAbelian 2 E ∧ Nat.card E = 16 := by
  intro h
  let f : M22 →* M23 :=
    (MulAction.stabilizer M23 (9 : Fin 23)).subtype.comp
      m23EquivM22PointStabilizer.toMonoidHom
  have hf : Function.Injective f :=
    Subtype.val_injective.comp m23EquivM22PointStabilizer.injective
  let U : Subgroup M23 := (P : Subgroup M22).map f
  obtain ⟨T, hUT⟩ := (P.isPGroup'.map f).exists_le_sylow
  have hU : Nat.card U = 128 := by
    rw [card_map_of_injective hf]
    exact (Nat.card_congr (P.equiv M22EvenGeometry.sylow).toEquiv).trans
      M22EvenGeometry.sylow_card
  have hT : Nat.card T = 128 := by
    rw [T.card_eq_multiplicity, m23_order]
    decide +kernel
  have he : U = (T : Subgroup M23) :=
    eq_of_le_of_card_ge hUT (by rw [hU]; exact hT.le)
  let e : P ≃* T := ((P : Subgroup M22).equivMapOfInjective f hf).trans
    (MulEquiv.subgroupCongr he)
  exact m23_sylow_not_unique_elementary_sixteen T
    (existsUnique_elementary_subgroup_of_equiv e h)
end Sporadic.Mathieu
