module
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.PCoreNormalizerAction
public import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# Solvable actors on simple local core quotients

A solvable subgroup of Aut(C) normalized by Inn(C) is trivial when C is
centerless, simple and perfect: otherwise its commutator contains Inn(C).
Restriction to a preserved subgroup and its characteristic prime-core quotient
transfers this criterion without changing the quotient map.

The symplectic parabolic comparison in original Aschbacher--Smith 14.6.15,
printed p.1035, applies this to the actual local SL₂ quotient.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace MulAut
variable {C : Type*} [Group C]

/-- A solvable automorphism subgroup normalized by every inner automorphism
of a centerless nonabelian simple group is trivial. -/
theorem solvable_eq_bot_of_inner_normalizes [IsSimpleGroup C] [Group.IsPerfect C]
    (hz : center C = ⊥) (A : Subgroup (MulAut C)) [Group.IsSolvable A]
    (hn : innerSubgroup C ≤ normalizer (A : Set (MulAut C))) : A = ⊥ := by
  let I := innerSubgroup C
  let e : C ≃* I := MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hz)
  let : IsSimpleGroup I := e.symm.isSimpleGroup
  let : Group.IsPerfect I := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  by_contra ha
  have he : I = ⁅I,A⁆ := SimpleSocle.commutator_eq I
    (centralizer_innerSubgroup_eq_bot hz) A ha
  have hIA : I ≤ A := he.le.trans (le_normalizer_iff_commutator_le_right.mp hn)
  exact Group.IsPerfect.not_isSolvable I
    (Group.isSolvable_of_isSolvable_injective (inclusion_injective hIA))

variable {X : Type*} [Group X]

/-- Restriction to the subgroup fixed by an automorphism. -/
def subgroupStabilizerAction (L : Subgroup X) :
    MulAction.stabilizer (MulAut X) L →* MulAut L where
  toFun a := (a.val.subgroupMap L).trans (MulEquiv.subgroupCongr a.property)
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

/-- The action on the literal characteristic prime-core quotient. -/
def subgroupStabilizerCoreAction (p : ℕ) (L : Subgroup X) :
    MulAction.stabilizer (MulAut X) L →* MulAut (L ⧸ pCore p L) :=
  (quotientAut (pCore p L)).comp (subgroupStabilizerAction L)

/-- Inner automorphisms of L preserve L. -/
theorem inner_le_subgroupStabilizer (L : Subgroup X) :
    L.map (MulAut.conj : X →* MulAut X) ≤ MulAction.stabilizer (MulAut X) L := by
  rintro _ ⟨x,hx,rfl⟩
  exact mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer hx)

/-- Inner automorphisms of the original subgroup give every inner quotient actor. -/
theorem subgroupStabilizerCoreAction_inner (p : ℕ) (L : Subgroup X) :
    ((L.map (MulAut.conj : X →* MulAut X)).subgroupOf
      (MulAction.stabilizer (MulAut X) L)).map (subgroupStabilizerCoreAction p L) =
        innerSubgroup (L ⧸ pCore p L) := by
  have he (x : L) : subgroupStabilizerCoreAction p L
      ⟨MulAut.conj (x : X),inner_le_subgroupStabilizer L (mem_map_of_mem _ x.property)⟩ =
        MulAut.conj (QuotientGroup.mk' (pCore p L) x) := by
    apply MulEquiv.ext
    intro y
    obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (pCore p L) y
    rw [subgroupStabilizerCoreAction,MonoidHom.comp_apply,quotientAut_apply_mk]
    change QuotientGroup.mk' (pCore p L) (x*z*x⁻¹) = _
    simp only [map_mul,map_inv,MulAut.conj_apply]
  apply le_antisymm
  · rintro _ ⟨a,⟨x,hx,hxa⟩,rfl⟩
    have hae : a = ⟨MulAut.conj x,inner_le_subgroupStabilizer L (mem_map_of_mem _ hx)⟩ :=
      Subtype.ext hxa.symm
    rw [hae,he ⟨x,hx⟩]
    exact ⟨_,rfl⟩
  · rintro _ ⟨y,rfl⟩
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore p L) y
    exact ⟨⟨MulAut.conj (x : X),inner_le_subgroupStabilizer L
      (mem_map_of_mem _ x.property)⟩,mem_map_of_mem _ x.property,he x⟩

/-- Solvable actors normalized by the whole local group fix its centerless
simple perfect core quotient. -/
theorem solvable_subgroupStabilizerCoreAction_eq_one
    (p : ℕ) (L : Subgroup X)
    [IsSimpleGroup (L ⧸ pCore p L)] [Group.IsPerfect (L ⧸ pCore p L)]
    (hz : center (L ⧸ pCore p L) = ⊥)
    (A : Subgroup (MulAut X)) [Group.IsSolvable A]
    (hA : A ≤ MulAction.stabilizer (MulAut X) L)
    (hN : L.map (MulAut.conj : X →* MulAut X) ≤ normalizer (A : Set (MulAut X)))
    (a : MulAction.stabilizer (MulAut X) L) (ha : a.val ∈ A) :
    subgroupStabilizerCoreAction p L a = 1 := by
  let D := MulAction.stabilizer (MulAut X) L
  let B := A.subgroupOf D
  let f := subgroupStabilizerCoreAction p L
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hA).toMonoidHom) (subgroupOfEquivOfLe hA).injective
  let : Group.IsSolvable (B.map f) := Group.isSolvable_of_surjective (f.subgroupMap_surjective B)
  have hn : innerSubgroup (L ⧸ pCore p L) ≤ normalizer (B.map f : Set _) := by
    rw [←subgroupStabilizerCoreAction_inner p L]
    apply (map_mono ?_).trans (le_normalizer_map f)
    exact (comap_mono hN).trans (le_normalizer_comap D.subtype)
  have hb := solvable_eq_bot_of_inner_normalizes hz (B.map f) hn
  have hh := mem_map_of_mem f (show a ∈ B from ha)
  rwa [hb,mem_bot] at hh
end MulAut
