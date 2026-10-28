module

public import Theory.GroupTheory.SimpleSectionSolvableLayers

/-!
# Constructing solvable layers from a representation

A homomorphism with solvable kernel gives the required normal layers by
taking the whole source as the inner normal subgroup and the representation
kernel as its solvable radical. The first isomorphism theorem supplies the
faithful map from the actual quotient. This construction also applies after
restricting the source along an injective homomorphism.

These elementary constructions are used for the block representations of
parabolic subgroups; they assume no subgroup classification.
-/

namespace Theory.GroupTheory

private theorem ker_comp_isSolvable
    {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) [Group.IsSolvable f.ker] (j : K →* G)
    (hj : Function.Injective j) : Group.IsSolvable (f.comp j).ker := by
  let k : (f.comp j).ker →* f.ker :=
    (j.comp (f.comp j).ker.subtype).codRestrict f.ker (fun x => x.property)
  apply Group.isSolvable_of_isSolvable_injective (f := k)
  intro x y h
  apply Subtype.ext
  apply hj
  exact congrArg (fun z : f.ker => (z : G)) h

/-- A representation with solvable kernel constructs both normal layers and
the faithful homomorphism from their quotient. -/
public theorem SolvableLayersEmbedding.of_solvable_ker
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) [Group.IsSolvable f.ker] : SolvableLayersEmbedding G H := by
  let N : Subgroup G := ⊤
  let k := f.comp N.subtype
  let : Group.IsSolvable k.ker := ker_comp_isSolvable f N.subtype N.subtype_injective
  let : Subsingleton (G ⧸ N) := QuotientGroup.subsingleton_quotient_top
  exact ⟨N, inferInstance, inferInstance, k.ker, inferInstance, inferInstance,
    QuotientGroup.kerLift k, QuotientGroup.kerLift_injective k⟩

/-- A solvable group has trivial remaining quotient. -/
public theorem SolvableLayersEmbedding.of_solvable
    (G H : Type*) [Group G] [Group H] [Group.IsSolvable G] :
    SolvableLayersEmbedding G H :=
  .of_solvable_ker (1 : G →* H)

/-- Restrict a representation with solvable kernel to an injective source. -/
public theorem SolvableLayersEmbedding.of_solvable_ker_comp_injective
    {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) [Group.IsSolvable f.ker] (j : K →* G)
    (hj : Function.Injective j) : SolvableLayersEmbedding K H := by
  let := ker_comp_isSolvable f j hj
  exact .of_solvable_ker (f.comp j)

end Theory.GroupTheory
