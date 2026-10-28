module
public import Theory.Representation.NoncyclicDegreeThree
public import Theory.SpecificGroups.SL2.SylowInnerFixer
public import Theory.SpecificGroups.SL2.OddCoreAndRank
public import Theory.GroupTheory.SylowNormalIntersection
/-!
# Cyclic centers of nonabelian odd-characteristic degree-three two-groups

A noncyclic abelian determinant-one subgroup in degree three has abelian
centralizer. Applying this to the center of a nonabelian two-subgroup forces
that center to be cyclic. The original faithful matrix embedding is retained.
Source: the classical model normalizer calculation in C.5.12, printed p.163.
-/
public section
open Subgroup Matrix
open scoped MatrixGroups IsMulCommutative
namespace Theory.SpecificGroups.Classical.SylowMarkedSL2
variable {G F : Type*} [Group G] [Finite G] [Field F]
theorem center_isCyclic_of_nonabelian_two_subgroup
    (j : G →* GL (Fin 3) F) (hj : Function.Injective j)
    (hdet : ∀ g, GeneralLinearGroup.det (j g) = 1) (h2 : (2 : F) ≠ 0)
    (T : Subgroup G) (hT : IsPGroup 2 T) (hn : ¬ IsMulCommutative T) :
    IsCyclic (center T) := by
  classical
  by_contra hc
  let f := j.comp (T.subtype.comp (center T).subtype)
  have hf : Function.Injective f := hj.comp (T.subtype_injective.comp (center T).subtype_injective)
  let A := f.range
  let e : center T ≃* A := MonoidHom.ofInjective hf
  let : Finite A := Finite.of_surjective e e.surjective
  let : IsMulCommutative A := IsMulCommutative.of_comm (fun x y => by
    apply e.symm.injective
    simp only [map_mul,mul_comm])
  have hnc : ¬ IsCyclic A := fun ha => hc (e.isCyclic.mpr ha)
  obtain ⟨n,hncard⟩ := (hT.to_subgroup (center T)).exists_card_eq
  have hcard : Nat.card A = 2 ^ n := (Nat.card_congr e.symm.toEquiv).trans hncard
  let : IsMulCommutative (centralizer (A : Set (GL (Fin 3) F))) :=
    Representation.generalLinear_centralizer_isMulCommutative_of_noncyclic_det_one A
      (by rw [hcard,Nat.cast_pow,Nat.cast_ofNat]; exact pow_ne_zero n h2) hnc
      (by rintro ⟨a,⟨z,rfl⟩⟩; exact hdet z.val.val)
  let k : T →* centralizer (A : Set (GL (Fin 3) F)) :=
    (j.comp T.subtype).codRestrict _ (fun t => by
      apply mem_centralizer_iff.mpr
      rintro _ ⟨z,rfl⟩
      change j z.val.val * j t.val = j t.val * j z.val.val
      rw [← map_mul,← map_mul]
      exact congrArg (fun v : T => j v.val) ((mem_center_iff.mp z.property t).symm))
  apply hn
  apply IsMulCommutative.of_comm
  intro x y
  apply T.subtype_injective
  apply hj
  have he := congrArg Subtype.val (mul_comm (k x) (k y))
  change j x.val * j y.val = j y.val * j x.val at he
  change j (x.val * y.val) = j (y.val * x.val)
  rw [map_mul,map_mul]
  exact he
end Theory.SpecificGroups.Classical.SylowMarkedSL2
