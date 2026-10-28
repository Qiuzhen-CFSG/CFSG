module

public import Theory.Mathieu.M24.ValueBoundParabolics

/-!
# Transporting a native M₂₄ generating triple

Sylow conjugacy aligns the marked Sylow subgroup with the image of an
arbitrary ambient Sylow subgroup under a specified group isomorphism.
Transport the three overgroups through that conjugation and isomorphism.
The construction preserves generation and properness, and transports the
intrinsic two-core quotients through the actual subgroup equivalences.

The native generating triple remains an explicit input. Its order and
containment suffice for the already proved S₃ quotient calculation.
Source: Aschbacher–Smith E.4.3(2), printed pp. 241–242 (PDF pp. 252–253).
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M24ValueBoundParabolics
open M24LocalGeometry.SylowNormalizer
variable {G : Type*} [Group G] [Finite G]

/-- A native generating triple supplies proper overgroups of any specified
Sylow subgroup in an isomorphic copy, with actual intrinsic S₃ quotients. -/
theorem transport_native_triple (e : G ≃* M24) (T : Sylow 2 G)
    (P : Fin 3 → Subgroup M24) (hle : ∀ i, candidate ≤ P i)
    (hcard : ∀ i, Nat.card (P i) = 3072) (hgen : ⨆ i, P i = ⊤) :
    ∃ R : Fin 3 → Subgroup G, (∀ i, (T : Subgroup G) ≤ R i) ∧
      (⨆ i, R i) = ⊤ ∧ (∀ i, R i < ⊤) ∧
      (∀ i, Nonempty ((R i ⧸ pCore 2 (R i)) ≃* Equiv.Perm (Fin 3))) := by
  have hs : Nat.card candidate = 2 ^ (Nat.card M24).factorization 2 := by
    rw [candidate_card, m24_order]
    decide +kernel
  let S : Sylow 2 M24 := Sylow.ofCard candidate hs
  have hS : (S : Subgroup M24) = candidate := Sylow.coe_ofCard candidate hs
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M24 S (T.mapSurjective (f := e.toMonoidHom) e.surjective)
  let d : M24 ≃* G := (MulAut.conj g).trans e.symm
  have he : candidate.map d.toMonoidHom = (T : Subgroup G) := by
    have h := congrArg Sylow.toSubgroup hg
    change (S : Subgroup M24).map (MulAut.conj g).toMonoidHom =
      (T : Subgroup G).map e.toMonoidHom at h
    rw [hS] at h
    have hh := congrArg (Subgroup.map e.symm.toMonoidHom) h
    have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      ext x
      exact e.symm_apply_apply x
    have hd : d.toMonoidHom = e.symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
      ext x
      exact MulEquiv.trans_apply (MulAut.conj g) e.symm x
    rw [hd]
    simpa only [Subgroup.map_map, hid, Subgroup.map_id] using hh

  let R (i : Fin 3) := (P i).map d.toMonoidHom
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← he]
    exact Subgroup.map_mono (hle i)
  · change (⨆ i, (P i).map d.toMonoidHom) = ⊤
    rw [← Subgroup.map_iSup, hgen, Subgroup.map_top_of_surjective _ d.surjective]
  · intro i
    apply lt_of_le_of_ne le_top
    intro hr
    have hn := M24ValueBoundParabolics.candidate_overgroup_lt_top (P i) (hcard i)
    apply hn.ne
    apply Subgroup.map_injective (f := d.toMonoidHom) d.injective
    rw [Subgroup.map_top_of_surjective _ d.surjective]
    exact hr
  · intro i
    let b : R i ≃* P i := (d.subgroupMap (P i)).symm
    let q : (R i ⧸ pCore 2 (R i)) ≃* (P i ⧸ pCore 2 (P i)) :=
      QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
    exact ⟨q.trans (M24ValueBoundParabolics.candidate_overgroup_quotient
      (P i) (hle i) (hcard i)).some⟩
end Sporadic.Mathieu.M24ValueBoundParabolics
