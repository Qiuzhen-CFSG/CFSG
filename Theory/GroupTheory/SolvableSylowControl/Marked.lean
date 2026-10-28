module

public import Theory.GroupTheory.SolvableSylowControl

/-!
# Solvable Sylow control from a concrete marking

It suffices to place solvable overgroups of one chosen Sylow subgroup in
its concrete normalizer. Sylow conjugacy then gives control for every
supplied Sylow, and adjusts any model equivalence to preserve that Sylow.
The Borel in this interface is supplied separately from its normalizer
equation, allowing callers to retain matrix or root definitions.

Source: Sylow conjugacy, as used in Aschbacher–Smith, proof of 13.6.6,
printed p.927.
-/

public section
namespace Theory.GroupTheory.SolvableSylowControl
open Subgroup
variable {p : ℕ} [Fact p.Prime] {G M : Type*} [Group G] [Group M]

/-- Align a supplied Sylow with the concrete root Sylow by adjusting the
actual model equivalence by an inner automorphism. -/
theorem exists_aligned_equiv [Finite G] [Finite M]
    (e : G ≃* M) (S : Sylow p G) (Q : Sylow p M) :
    ∃ (g : M) (e' : G ≃* M), e' = e.trans (MulAut.conj g) ∧
      (S : Subgroup G).map e'.toMonoidHom = Q := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) Q
  refine ⟨g, e.trans (MulAut.conj g), rfl, ?_⟩
  have hm := congrArg Sylow.toSubgroup hg
  change ((S : Subgroup G).map e.toMonoidHom).map
    (MulAut.conj g).toMonoidHom = Q at hm
  change (S : Subgroup G).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = Q
  rw [← Subgroup.map_map]
  exact hm

/-- Standard-root placement gives control of every supplied Sylow. -/
theorem of_standard [Finite G] (Q : Sylow p G) (B : Subgroup G)
    (hB : normalizer (Q : Set G) = B)
    (hplace : ∀ A : Subgroup G, Group.IsSolvable A → (Q : Subgroup G) ≤ A → A ≤ B) :
    SolvableSylowControl p G := by
  intro S A hA hSA
  obtain ⟨g, e, _, he⟩ := exists_aligned_equiv (MulEquiv.refl G) S Q
  let : Group.IsSolvable A := hA
  have hs : Group.IsSolvable (A.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective A)
  have hn := hplace (A.map e.toMonoidHom) hs (he ▸ map_mono hSA)
  rw [← hB] at hn
  change A.map e.toMonoidHom ≤ normalizer ((Q : Subgroup G) : Set G) at hn
  rw [← he, ← map_equiv_normalizer_eq] at hn
  exact (map_le_map_iff_of_injective e.injective).mp hn

omit [Fact p.Prime] in
/-- For a nonsolvable group, uniqueness of proper Sylow overgroups suffices.
No simplicity or subgroup classification is hidden in this deduction. -/
theorem of_proper_overgroups (hG : ¬ Group.IsSolvable G)
    (hproper : ∀ (S : Sylow p G) (A : Subgroup G),
      (S : Subgroup G) ≤ A → A < ⊤ → A ≤ normalizer (S : Set G)) :
    SolvableSylowControl p G := by
  intro S A hA hSA
  apply hproper S A hSA
  apply lt_top_iff_ne_top.mpr
  intro he
  let : Group.IsSolvable A := hA
  apply hG
  exact Group.isSolvable_of_surjective (f := A.subtype)
    (fun x => ⟨⟨x, he ▸ mem_top x⟩, rfl⟩)

end Theory.GroupTheory.SolvableSylowControl
