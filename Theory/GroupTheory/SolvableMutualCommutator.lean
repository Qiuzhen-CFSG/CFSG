module
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.SubgroupTransport
/-!
# Solvable joins from a solvable mutual commutator

Two solvable subgroups generate a solvable group when their mutual
commutator is solvable. The commutator is normal in their join; modulo it
the two images commute. Solvability then lifts through the normal kernel.
The map criterion records the same extension argument for a general
homomorphism with solvable kernel.

Source application: Aschbacher--Smith, 10.2.9, printed p.753, for the two
exchanged original component point centralizers.
-/

public section
open Subgroup
variable {G : Type*} [Group G]
theorem Group.isSolvable_sup_of_commutator_le_normal
    (A B N : Subgroup G) [N.Normal]
    [Group.IsSolvable A] [Group.IsSolvable B] [Group.IsSolvable N]
    (hc : ⁅A,B⁆ ≤ N) : Group.IsSolvable (A ⊔ B : Subgroup G) := by
  let q := QuotientGroup.mk' N
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  let : Group.IsSolvable (A.map q) := Group.isSolvable_of_surjective (q.subgroupMap_surjective A)
  let : Group.IsSolvable (B.map q) := Group.isSolvable_of_surjective (q.subgroupMap_surjective B)
  have hcomm : ⁅A.map q,B.map q⁆ = ⊥ := by
    rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hc
  have hn : B.map q ≤ normalizer (A.map q : Set (G ⧸ N)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
      (centralizer_le_normalizer _)
  let : Group.IsSolvable (A.map q ⊔ B.map q : Subgroup (G ⧸ N)) :=
    Group.isSolvable_sup_of_normalizes _ _ hn
  have : Group.IsSolvable ((A ⊔ B).map q) := by rw [Subgroup.map_sup]; infer_instance
  let : Group.IsSolvable (((A ⊔ B).map q).comap q) :=
    isSolvable_comap_of_solvable_ker q _
  exact Group.isSolvable_of_isSolvable_injective
    (f := inclusion (le_comap_map (f := q) (H := A ⊔ B))) (inclusion_injective _)

/-- Solvable factors generate a solvable group when their mutual commutator is solvable. -/
theorem Group.isSolvable_sup_of_solvable_commutator (A B : Subgroup G)
    [Group.IsSolvable A] [Group.IsSolvable B] [Group.IsSolvable (⁅A,B⁆ : Subgroup G)] :
    Group.IsSolvable (A ⊔ B : Subgroup G) := by
  let H := A ⊔ B
  let N := ⁅A,B⁆.subgroupOf H
  let : Group.IsSolvable (A.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show A ≤ H from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show A ≤ H from le_sup_left)).injective
  let : Group.IsSolvable (B.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show B ≤ H from le_sup_right)).toMonoidHom)
      (subgroupOfEquivOfLe (show B ≤ H from le_sup_right)).injective
  let : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (commutator_le_sup A B)).toMonoidHom)
      (subgroupOfEquivOfLe (commutator_le_sup A B)).injective
  have hc : ⁅A.subgroupOf H,B.subgroupOf H⁆ ≤ N := by
    rw [← Theory.GroupTheory.SubgroupTransport.subgroupOf_commutator A B le_sup_left le_sup_right]
  have hs := Group.isSolvable_sup_of_commutator_le_normal (A.subgroupOf H)
    (B.subgroupOf H) N hc
  rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self] at hs
  let := hs
  exact Group.isSolvable_of_surjective (f := (topEquiv (G := H)).toMonoidHom)
    (topEquiv (G := H)).surjective

/-- Solvability is preserved and reflected by a map with solvable kernel. -/
theorem Group.isSolvable_map_iff_of_solvable_ker {K : Type*} [Group K]
    (f : G →* K) [Group.IsSolvable f.ker] (A : Subgroup G) :
    Group.IsSolvable (A.map f) ↔ Group.IsSolvable A := by
  constructor
  · intro hs
    let := hs
    let : Group.IsSolvable ((A.map f).comap f) := isSolvable_comap_of_solvable_ker f _
    exact Group.isSolvable_of_isSolvable_injective
      (f := inclusion (le_comap_map (f := f) A)) (inclusion_injective _)
  · intro hs
    let := hs
    exact Group.isSolvable_of_surjective (f.subgroupMap_surjective A)
