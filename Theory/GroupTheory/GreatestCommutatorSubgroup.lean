module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.Fintype.Powerset

/-!
# Maximal commutator subgroups

The two exact commutator conditions preceding Stellmacher (9.1), relation
(9), are closed under subgroup joins. Consequently a nonempty family has
a greatest member in a finite group. Every automorphism preserving the
three parameters preserves that greatest member. In particular the
simultaneous normalizer normalizes it. An explicit member supplies nonemptiness; applications construct that
member from their own hypotheses. This is the intrinsic finite-lattice
argument preceding relation (9) in Stellmacher (9.1), journal p.47 of
`refs/files/stellmacher-n-group.pdf`.
-/

open scoped commutatorElement

namespace Subgroup

private theorem sup_commutator_le
    {G : Type*} [Group G] (Q Z U W : Subgroup G)
    (hQZ : Q ≤ Subgroup.normalizer Z)
    (hUQ : U ≤ Q) (hWQ : W ≤ Q)
    (hU : ⁅U, Q⁆ ≤ Z) (hW : ⁅W, Q⁆ ≤ Z) : ⁅U ⊔ W, Q⁆ ≤ Z := by
  let C : Subgroup G :=
    { carrier := {element | element ∈ Q ∧ ∀ other ∈ Q, ⁅element, other⁆ ∈ Z}
      one_mem' := ⟨Q.one_mem, by simp⟩
      mul_mem' := by
        rintro first second ⟨hfirst, hfirstcomm⟩ ⟨hsecond, hsecondcomm⟩
        refine ⟨Q.mul_mem hfirst hsecond, ?_⟩
        intro other hother
        rw [commutatorElement_mul_left_eq_conj_mul]
        exact Z.mul_mem
          (Subgroup.le_normalizer_iff.mp hQZ first hfirst _ (hsecondcomm other hother))
          (hfirstcomm other hother)
      inv_mem' := by
        rintro element ⟨helement, hcomm⟩
        refine ⟨Q.inv_mem helement, ?_⟩
        intro other hother
        rw [commutatorElement_inv_left]
        have hinv : ⁅other, element⁆ ∈ Z := by
          rw [← commutatorElement_inv]
          exact Z.inv_mem (hcomm other hother)
        simpa only [inv_inv] using
          Subgroup.le_normalizer_iff.mp hQZ element⁻¹ (Q.inv_mem helement) _ hinv }
  have hUC : U ≤ C := fun element helement =>
    ⟨hUQ helement, Subgroup.commutator_le.mp hU element helement⟩
  have hWC : W ≤ C := fun element helement =>
    ⟨hWQ helement, Subgroup.commutator_le.mp hW element helement⟩
  exact Subgroup.commutator_le.mpr fun element helement =>
    ((sup_le hUC hWC) helement).2

private theorem sup_full_commutator
    {G : Type*} [Group G] (E U W : Subgroup G)
    (hU : ⁅U, E⁆ = U) (hW : ⁅W, E⁆ = W) : ⁅U ⊔ W, E⁆ = U ⊔ W := by
  apply le_antisymm
  · rw [Subgroup.commutator_comm]
    apply Subgroup.le_normalizer_iff_commutator_le_right.mp
    apply (le_inf ?_ ?_).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup U W)
    · rw [← hU]
      exact Subgroup.normalizer_commutator_ge_right U E
    · rw [← hW]
      exact Subgroup.normalizer_commutator_ge_right W E
  · exact sup_le (hU.symm.le.trans (Subgroup.commutator_mono le_sup_left le_rfl))
      (hW.symm.le.trans (Subgroup.commutator_mono le_sup_right le_rfl))

/-- A nonempty family defined by two exact commutator conditions has a greatest member. -/
public theorem exists_greatest_commutator_subgroup
    {G : Type*} [Group G] [Finite G] (Q Z E : Subgroup G)
    (hQZ : Q ≤ Subgroup.normalizer Z)
    (seed : Subgroup G) (hseedQ : seed ≤ Q)
    (hseedQcomm : ⁅seed, Q⁆ = Z) (hseedEcomm : ⁅seed, E⁆ = seed) :
    ∃ U : Subgroup G,
      U ≤ Q ∧ ⁅U, Q⁆ = Z ∧ ⁅U, E⁆ = U ∧
      (∀ W : Subgroup G, W ≤ Q → ⁅W, Q⁆ = Z → ⁅W, E⁆ = W → W ≤ U) := by
  let _ : Finite (Subgroup G) :=
    Finite.of_injective (fun U : Subgroup G => (U : Set G)) SetLike.coe_injective
  let family : Set (Subgroup G) := {U | U ≤ Q ∧ ⁅U, Q⁆ = Z ∧ ⁅U, E⁆ = U}
  obtain ⟨U, hU, hmax⟩ := (Set.toFinite family).exists_maximal
    ⟨seed, hseedQ, hseedQcomm, hseedEcomm⟩
  refine ⟨U, hU.1, hU.2.1, hU.2.2, ?_⟩
  intro W hWQ hWQcomm hWEcomm
  have hsup : U ⊔ W ∈ family := by
    refine ⟨sup_le hU.1 hWQ, le_antisymm ?_ ?_, sup_full_commutator E U W hU.2.2 hWEcomm⟩
    · exact sup_commutator_le Q Z U W hQZ hU.1 hWQ hU.2.1.le hWQcomm.le
    · exact hU.2.1.symm.le.trans (Subgroup.commutator_mono le_sup_left le_rfl)
  exact le_sup_right.trans (hmax hsup le_sup_left)

/-- Simultaneous normalizers of the parameters normalize the greatest member. -/
public theorem greatest_commutator_subgroup_normalized
    {G : Type*} [Group G] (Q Z E U T : Subgroup G)
    (hUQ : U ≤ Q) (hUQcomm : ⁅U, Q⁆ = Z) (hUEcomm : ⁅U, E⁆ = U)
    (hgreatest : ∀ W : Subgroup G, W ≤ Q → ⁅W, Q⁆ = Z → ⁅W, E⁆ = W → W ≤ U)
    (hTQ : T ≤ Subgroup.normalizer Q) (hTZ : T ≤ Subgroup.normalizer Z)
    (hTE : T ≤ Subgroup.normalizer E) : T ≤ Subgroup.normalizer U := by
  apply Subgroup.le_normalizer_iff.mpr
  intro actor hactor element helement
  let conjugation := (MulAut.conj actor).toMonoidHom
  have hQ : Q.map conjugation = Q := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTQ hactor)
  have hZ : Z.map conjugation = Z := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTZ hactor)
  have hE : E.map conjugation = E := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTE hactor)
  have hmap : U.map conjugation ≤ U := by
    apply hgreatest
    · exact hQ ▸ Subgroup.map_mono hUQ
    · rw [← hQ, ← Subgroup.map_commutator, hUQcomm, hZ]
    · rw [← hE, ← Subgroup.map_commutator, hUEcomm]
  exact hmap (Subgroup.mem_map_of_mem conjugation helement)


end Subgroup
