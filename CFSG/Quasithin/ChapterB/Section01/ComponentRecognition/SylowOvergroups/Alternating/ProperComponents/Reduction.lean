module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.OvergroupReduction
public import Mathlib.GroupTheory.GroupAction.Jordan

/-!
# Permutation reductions for the proper alternating Sylow overgroups

A Sylow two-subgroup of Aₘ contains a double transposition: place the
explicit permutation (0 1)(2 3) in some Sylow subgroup and conjugate that
subgroup to the given one. Conjugation preserves the four-point support.
Jordan's three-cycle theorem shows that a proper primitive subgroup of Aₘ
contains no three-cycle. Both statements use the natural action and the
literal nested subgroup carriers.

The primitive recognition and nonprimitive recognition statements below
are explicit remaining inputs, not asserted classifications. The primitive
adapter supplies both permutation facts to its recognition input. The
nonprimitive input still requires the orbit and block-system argument,
including the restriction that a PSL₃(2) component occurs only at m = 7.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.1.13,
printed p.74 (PDF p.85), final paragraph. The Jordan theorem is the
three-cycle case of Wielandt, *Finite Permutation Groups*, Theorem 13.3,
as proved in Mathlib. No SQTK or FF hypothesis is added.
-/

public section
open Subgroup Equiv MulAction Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

/-- Jordan's three-cycle theorem excludes a three-cycle in a proper primitive overgroup. -/
theorem alternating_proper_primitive_no_threeCycle {m : ℕ}
    (X : Subgroup (alternatingGroup (Fin m)))
    (hX : X ≠ ⊤) (hp : IsPreprimitive X (Fin m)) (x : X) :
    ¬ x.val.val.IsThreeCycle := by
  intro hx
  apply hX
  rw [eq_top_iff, ← Subgroup.map_subtype_le_map_subtype,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let φ := (alternatingGroup (Fin m)).subtype.subgroupMap X
  let f : Fin m →ₑ[φ] Fin m := { toFun := id, map_smul' _ _ := rfl }
  have hp' : IsPreprimitive (X.map (alternatingGroup (Fin m)).subtype) (Fin m) := by
    exact (isPreprimitive_congr (f := f)
      ((alternatingGroup (Fin m)).subtype.subgroupMap_surjective X)
      Function.bijective_id).mp hp
  exact Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hp' hx
    (mem_map_of_mem _ x.property)

/-- Every Sylow two-subgroup contains an involution moving exactly four letters. -/
theorem alternating_sylow_exists_double_transposition {m : ℕ} (hm : 4 ≤ m)
    (S : Sylow 2 (alternatingGroup (Fin m))) :
    ∃ t : S, t ^ 2 = 1 ∧ t.val.val.support.card = 4 := by
  let a : Fin m := ⟨0, by omega⟩
  let b : Fin m := ⟨1, by omega⟩
  let c : Fin m := ⟨2, by omega⟩
  let d : Fin m := ⟨3, by omega⟩
  have hab : a ≠ b := by simp [a, b]
  have hcd : c ≠ d := by simp [c, d]
  have hd : (swap a b).Disjoint (swap c d) :=
    Perm.disjoint_swap_swap (by simp [a, b, c, d])
  let t : alternatingGroup (Fin m) := ⟨swap a b * swap c d, by
    simp [Perm.mem_alternatingGroup, hab, hcd]⟩
  have ht : t ^ 2 = 1 := by
    apply Subtype.ext
    change (swap a b * swap c d) ^ 2 = 1
    rw [hd.commute.mul_pow]
    simp [pow_two]
  have hsupp : t.val.support.card = 4 := by
    change (swap a b * swap c d).support.card = 4
    rw [hd.card_support_mul, Perm.card_support_swap hab, Perm.card_support_swap hcd]
  have htP : IsPGroup 2 (zpowers t) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one ht
  obtain ⟨Q, hQ⟩ := htP.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_smul_eq (alternatingGroup (Fin m)) Q S
  let u : ↥(g • Q : Sylow 2 (alternatingGroup (Fin m))) :=
    Q.equivSMul g ⟨t, hQ (mem_zpowers t)⟩
  have hu : (u : alternatingGroup (Fin m)) = g * t * g⁻¹ := rfl
  have huS : (u : alternatingGroup (Fin m)) ∈ S := hg ▸ u.property
  refine ⟨⟨u, huS⟩, ?_, ?_⟩
  · apply Subtype.ext
    change (u : alternatingGroup (Fin m)) ^ 2 = 1
    rw [hu, ← MulAut.conj_apply, ← map_pow, ht, map_one]
  · change (u : alternatingGroup (Fin m)).val.support.card = 4
    rw [hu]
    exact Perm.card_support_conj.trans hsupp

/-- The remaining primitive recognition, with the proved permutation inputs
made available to its producer. This definition makes no classification assertion. -/
@[expose] def AlternatingPrimitiveComponentRecognition (m : ℕ) : Prop :=
  ∀ (S : Sylow 2 (alternatingGroup (Fin m)))
    (X : Subgroup (alternatingGroup (Fin m))), (S : Subgroup _) ≤ X → X ≠ ⊤ →
    IsPreprimitive X (Fin m) →
    (∀ x : X, ¬ x.val.val.IsThreeCycle) →
    (∃ t : X, t ^ 2 = 1 ∧ t.val.val.support.card = 4) →
    ∀ D : Subgroup X, IsComponent X D → AlternatingSubgroupModels m D

/-- The remaining intransitive and imprimitive recognition in the natural action.
The source's actual component models and exceptional degree are retained. -/
@[expose] def AlternatingNonprimitiveComponentRecognition (m : ℕ) : Prop :=
  ∀ (S : Sylow 2 (alternatingGroup (Fin m)))
    (X : Subgroup (alternatingGroup (Fin m))), (S : Subgroup _) ≤ X → X ≠ ⊤ →
    ¬ IsPreprimitive X (Fin m) →
    ∀ D : Subgroup X, IsComponent X D → AlternatingSubgroupModels m D

/-- Supply the double transposition and the absence of three-cycles to the
primitive recognition input for the exact Sylow overgroup in B.1.13. -/
theorem alternating_primitive_component_models_of_recognition {m : ℕ} (hm : 6 ≤ m)
    (hrecognition : AlternatingPrimitiveComponentRecognition m)
    (S : Sylow 2 (alternatingGroup (Fin m)))
    (X : Subgroup (alternatingGroup (Fin m))) (hS : (S : Subgroup _) ≤ X)
    (hX : X ≠ ⊤) (hp : IsPreprimitive X (Fin m))
    (D : Subgroup X) (hD : IsComponent X D) : AlternatingSubgroupModels m D := by
  obtain ⟨t, ht, hsupp⟩ := alternating_sylow_exists_double_transposition (by omega : 4 ≤ m) S
  exact hrecognition S X hS hX hp (alternating_proper_primitive_no_threeCycle X hX hp)
    ⟨⟨t, hS t.property⟩,
      Subtype.ext (congrArg (fun u : S => (u : alternatingGroup (Fin m))) ht), hsupp⟩ D hD

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
