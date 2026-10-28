module
public import Theory.GroupTheory.PerfectSylowPreservingAction
public import Theory.GroupTheory.SylowOuterSolvability
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# The two solvable kernels in Sylow restriction

The stabilizer of a Sylow two-subgroup in the automorphism group surjects
onto the outer group. Its kernel is an image of the Sylow normalizer and
is therefore solvable. Restriction to the Sylow subgroup has solvable
kernel whenever its pointwise fixer is solvable. Both maps retain the
literal Sylow subgroup, so they can be composed with its invariant sections.

Source: the Sylow and solvable-extension arguments used in
Aschbacher--Smith 4.4.10--11, with the two-Schreier input I.3.1.
-/

public section
open Subgroup
open scoped Pointwise
namespace MulAut
variable {G : Type*} [Group G] [Finite G]

/-- The original Sylow stabilizer maps to the outer automorphism group. -/
def sylowOuterMap (P : Sylow 2 G) :
    MulAction.stabilizer (MulAut G) (P : Subgroup G) →* Outer G :=
  (QuotientGroup.mk' (innerSubgroup G)).comp
    (MulAction.stabilizer (MulAut G) (P : Subgroup G)).subtype

/-- Inner conjugation moves the image Sylow back to the chosen one. -/
theorem sylowOuterMap_surjective (P : Sylow 2 G) :
    Function.Surjective (sylowOuterMap P) := by
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (innerSubgroup G) x
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G (a • P) P
  have hm : MulAut.conj g * a ∈ MulAction.stabilizer (MulAut G) (P : Subgroup G) := by
    change (MulAut.conj g * a) • (P : Subgroup G) = (P : Subgroup G)
    rw [mul_smul]
    exact congrArg Sylow.toSubgroup hg
  refine ⟨⟨MulAut.conj g * a,hm⟩,?_⟩
  change QuotientGroup.mk' (innerSubgroup G) (MulAut.conj g * a) = _
  have hi : QuotientGroup.mk' (innerSubgroup G) (MulAut.conj g) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
  rw [map_mul,hi,one_mul]

/-- The kernel is the image of the actual, solvable Sylow normalizer. -/
theorem sylowOuterMap_ker_isSolvable (P : Sylow 2 G) :
    Group.IsSolvable (sylowOuterMap P).ker := by
  let N := normalizer (P : Set G)
  let : Group.IsSolvable N := P.normalizer_isSolvable_two
  let f : N →* (sylowOuterMap P).ker := {
    toFun := fun g => ⟨⟨MulAut.conj g,mem_normalizer_iff_map_conj_eq.mp g.property⟩,
      (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩⟩
    map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one MulAut.conj
    map_mul' := by intro a b; apply Subtype.ext; apply Subtype.ext; exact map_mul (MulAut.conj : G →* MulAut G) (a : G) (b : G) }
  apply Group.isSolvable_of_surjective (f := f)
  intro a
  obtain ⟨g,hg⟩ := (QuotientGroup.eq_one_iff _).mp a.property
  have hn : g ∈ N := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change MulAut.conj g • (P : Subgroup G) = (P : Subgroup G)
    rw [hg]
    exact a.val.property
  exact ⟨⟨g,hn⟩,Subtype.ext (Subtype.ext hg)⟩

/-- Restrict the actual Sylow stabilizer to the Sylow group. -/
def sylowRestriction (P : Sylow 2 G) :
    MulAction.stabilizer (MulAut G) (P : Subgroup G) →* MulAut P where
  toFun a := (a.val.subgroupMap (P : Subgroup G)).trans
    (MulEquiv.subgroupCongr a.property)
  map_one' := by ext x; rfl
  map_mul' := by intro a b; ext x; rfl

omit [Finite G] in
/-- The restriction kernel embeds in the pointwise Sylow fixer. -/
theorem sylowRestriction_ker_isSolvable (P : Sylow 2 G)
    [Group.IsSolvable (fixingSubgroup (MulAut G) (P : Set G))] :
    Group.IsSolvable (sylowRestriction P).ker := by
  let H := MulAction.stabilizer (MulAut G) (P : Subgroup G)
  let F := fixingSubgroup (MulAut G) (P : Set G)
  let r := sylowRestriction P
  let i : r.ker →* F :=
    (H.subtype.comp r.ker.subtype).codRestrict F (by
      intro a
      apply (mem_fixingSubgroup_iff (MulAut G)).mpr
      intro x hx
      exact congrArg (fun b : MulAut P => ((b ⟨x,hx⟩ : P) : G)) a.property)
  exact Group.isSolvable_of_isSolvable_injective (f := i)
    (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : F => (z : MulAut G)) h)))
end MulAut
