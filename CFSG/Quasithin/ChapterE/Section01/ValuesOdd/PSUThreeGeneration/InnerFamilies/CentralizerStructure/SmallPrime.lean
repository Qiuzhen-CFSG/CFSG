module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerActors
public import CFSG.Quasithin.Defs
public import Theory.SpecificGroups.SU3.TernaryInvolutionCentralizer
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The solvable parameter in the inner PSU₃ centralizer argument

For L ≅ PSU₃(3), the intrinsic involution centralizer is solvable by the
concrete GU₂ calculation. Since G = LT has two-group quotient by L, the
ambient centralizer has solvable kernel and quotient. This includes every
allowed ambient extension, without a choice of outer automorphism.

Source: Aschbacher--Smith, A.3.21(a), p.55, and E.1.14(7), p.214.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration

/-- Transfer the concrete solvable centralizer through the supplied PSU₃ model. -/
theorem isPSU_three_involution_centralizer_solvable {G : Type*} [Group G]
    (hmodel : ClassicalGroup.IsPSU G 3 3)
    (z : G) (hz : orderOf z = 2) : Group.IsSolvable (centralizer ({z} : Set G)) := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  let : Group.IsSolvable (centralizer ({e z} : Set _)) :=
    Matrix.SU3.TernaryCentralizer.involution_centralizer_solvable J hcard hconj
      (e z) ((e.orderOf_eq z).trans hz)
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Matrix.SU3.InnerThreeRank.centralizerEquiv e z).toMonoidHom)
    (Matrix.SU3.InnerThreeRank.centralizerEquiv e z).injective

/-- All ambient two-extensions retain the solvable involution centralizer at p = 3. -/
theorem inner_centralizer_solvable_of_prime_three {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (hLT : L ⊔ (T : Subgroup G) = ⊤)
    (hmodel : ClassicalGroup.IsPSU L 3 3)
    (z : G) (hzL : z ∈ L) (hz : orderOf z = 2) :
    Group.IsSolvable (centralizer ({z} : Set G)) := by
  have hq := isPGroup_quotient_of_sup_eq_top L T T.isPGroup' hLT
  let : Group.IsNilpotent (G ⧸ L) := hq.isNilpotent
  let C := centralizer ({z} : Set G)
  let f := (QuotientGroup.mk' L).comp C.subtype
  let w : L := ⟨z, hzL⟩
  have hw : orderOf w = 2 := (orderOf_submonoid w).symm.trans hz
  let : Group.IsSolvable (centralizer ({w} : Set L)) := isPSU_three_involution_centralizer_solvable hmodel w hw
  let j : f.ker →* centralizer ({w} : Set L) :=
    { toFun := fun x => ⟨⟨x.val.val, (QuotientGroup.eq_one_iff _).mp x.property⟩,
        mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun a => (a.val : G)) h))
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hj
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [f.ker.range_subtype])

/-- The actual large-family consumer in the small-prime branch. -/
theorem exists_inner_centralizer_le_of_prime_three {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] {T : Sylow 2 G}
    (hLT : L ⊔ (T : Subgroup G) = ⊤) (hmodel : ClassicalGroup.IsPSU L 3 3)
    (d : LargeFamilyObstruction T)
    (hi : ∃ A ∈ d.family, A ≤ (T : Subgroup G) ∧ A ≠ ⊥ ∧ A ≤ L) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ L ∧ z ∈ (T : Subgroup G) ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      centralizer ({z} : Set G) ≤ d.overgroup := by
  apply exists_inner_centralizer_le_of_local_structure L Nat.prime_three (by decide) hmodel d hi
  intro A hA hAT hne hAL z hz hzL hTz hzA
  exact Or.inl (inner_centralizer_solvable_of_prime_three L T hLT hmodel z hzL hz)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
