module
public import Theory.GroupTheory.ComponentLocalOrbitSolvable
public import Theory.GroupTheory.SolvableSylowControl
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# Solvable extensions by component Borels

A solvable subgroup containing an ambient Sylow normalizes the Sylow
intersection with every component it stabilizes, provided the component
has intrinsic solvable Sylow control. It therefore preserves the component
Borel. Conjugate Borels in distinct components commute; their orbit is
solvable and normalized by the original solvable subgroup. Their join
is the required solvable extension, even when components are exchanged.

Source: Aschbacher--Smith, proof of 14.6.14, printed pp.1032--1033.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A solvable actor can replace the prime-group actor in the Borel orbit argument. -/
theorem IsComponent.local_adjoin_isSolvable_of_solvable
    {L B H : Subgroup G} (hL : IsComponent G L) (hBL : B ≤ L)
    (hinv : H ⊓ normalizer (L : Set G) ≤ normalizer (B : Set G))
    (hB : Group.IsSolvable B) (hH : Group.IsSolvable H) :
    Group.IsSolvable (B ⊔ H : Subgroup G) := by
  have hD : Group.IsSolvable (componentOrbit B H) := by
    apply isSolvable_iSup_of_normalizes
    · intro h
      let := hB
      exact Group.isSolvable_of_surjective
        ((MulAut.conj (h : G)).toMonoidHom.subgroupMap_surjective B)
    · intro a b
      exact hL.local_conjugates_normalize hBL hinv b a
  rw [← componentOrbit_sup B H]
  let := hD
  let := hH
  exact Group.isSolvable_sup_of_normalizes _ _ (le_normalizer_componentOrbit B H)

/-- The literal component Sylow normalizer has solvable join with the original overgroup. -/
theorem IsComponent.solvable_borel_extension
    (T : Sylow 2 G) (H L : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hH : Group.IsSolvable H) (hL : IsComponent G L)
    (hc : SolvableSylowControl 2 L)
    (hs : ∀ P : Sylow 2 L, Group.IsSolvable (normalizer (P : Set L))) :
    ∃ P : Sylow 2 L,
      (P : Subgroup L) = (T : Subgroup G).subgroupOf L ∧
      Group.IsSolvable ((normalizer (P : Set L)).map L.subtype ⊔ H : Subgroup G) := by
  obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_subnormal L hL.1
  let U := (P : Subgroup L).map L.subtype
  let B := (normalizer (P : Set L)).map L.subtype
  let A := H ⊓ normalizer (L : Set G)
  have hUL : U ≤ L := map_subtype_le _
  have hUT : U ≤ (T : Subgroup G) := by
    rw [show U = ((T : Subgroup G).subgroupOf L).map L.subtype from congrArg (map L.subtype) hP,
      subgroupOf_map_subtype]
    exact inf_le_left
  have hUA : U ≤ A := le_inf (hUT.trans hTH) (hUL.trans L.le_normalizer)
  let := hH
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective (show A ≤ H from inf_le_left))
  have hAU : A ≤ normalizer (U : Set G) := hc.normalizes_sylow L A P inf_le_right hUA
  have hB : B = L ⊓ normalizer (U : Set G) := by
    have hu : U.subgroupOf L = (P : Subgroup L) :=
      comap_map_eq_self_of_injective L.subtype_injective _
    rw [show B = (normalizer (U.subgroupOf L : Set L)).map L.subtype by rw [hu]; rfl,
      ← subgroupOf_normalizer_eq hUL, subgroupOf_map_subtype, inf_comm]
  have hinv : A ≤ normalizer (B : Set G) := by
    rw [hB]
    exact (le_inf (show A ≤ normalizer (L : Set G) from inf_le_right)
      (hAU.trans (normalizer (U : Set G)).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  let := hs P
  have hBs : Group.IsSolvable B :=
    Group.isSolvable_of_surjective (L.subtype.subgroupMap_surjective _)
  exact ⟨P,hP,hL.local_adjoin_isSolvable_of_solvable (map_subtype_le _) hinv hBs hH⟩
end Theory.GroupTheory
