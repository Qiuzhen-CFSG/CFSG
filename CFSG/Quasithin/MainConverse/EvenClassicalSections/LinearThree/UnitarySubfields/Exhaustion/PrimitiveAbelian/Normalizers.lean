module

public import Theory.Representation.EndFieldRep
public import Theory.Representation.AbelianWeightNormalizerSolvable
public import Theory.Representation.RankThreeNonabelianAutomizer

/-!
# Solvable degree-three matrix normalizers

Schur's lemma and the finite division ring theorem make the centralizer of
an irreducible matrix subgroup cyclic. For an abelian subgroup in degree
three, the character-weight action makes its automizer solvable. For a
nonabelian three-subgroup in characteristic two, the existing absolute
irreducibility and automizer theorems give the same conclusion. In either
case the normalizer is an extension of solvable groups.

These are the normalizer inputs for the Singer and central extraspecial-three
cases in GLS3, Theorem 6.5.3, `refs/KGroup/GLS3/chapter6.tex`. The nonabelian
automizer proof uses Aschbacher–Smith A.3.21(c), printed pp.55–56.
-/

open Matrix

namespace CFSG.Quasithin.MainConverse.UnitaryThreeSections.Exhaustion.PrimitiveAbelian

variable {F : Type} [Field F]

private noncomputable def centralizerToIntertwiner (n : ℕ) (Q : Subgroup (GL (Fin n) F)) :
    Subgroup.centralizer (Q : Set (GL (Fin n) F)) →*
      Representation.IntertwiningMap
        ((Representation.generalLinearNatural n).comp Q.subtype)
        ((Representation.generalLinearNatural n).comp Q.subtype) where
  toFun x := {
    toLinearMap := Representation.generalLinearNatural n x.val
    isIntertwining' q := by
      have h := congrArg (Representation.generalLinearNatural (F := F) n)
        (Subgroup.mem_centralizer_iff.mp x.property q.val q.property)
      simpa only [map_mul, MonoidHom.comp_apply, Subgroup.subtype_apply,
        Module.End.mul_eq_comp] using h.symm }
  map_one' := by
    ext v i
    apply congrFun
    exact congrArg (fun f : Module.End F (Fin n → F) => f v)
      (map_one (Representation.generalLinearNatural n))
  map_mul' x y := by
    ext v i
    apply congrFun
    exact congrArg (fun f : Module.End F (Fin n → F) => f v)
      (map_mul (Representation.generalLinearNatural n) x.val y.val)

private theorem centralizerToIntertwiner_injective (n : ℕ) (Q : Subgroup (GL (Fin n) F)) :
    Function.Injective (centralizerToIntertwiner n Q) := by
  intro x y h
  apply Subtype.ext
  apply Representation.generalLinearNatural_injective n
  exact congrArg Representation.IntertwiningMap.toLinearMap h

/-- Schur and the finite division ring theorem make the matrix centralizer of
an irreducible subgroup cyclic. -/
public theorem centralizer_isCyclic_of_irreducible [Finite F]
    (n : ℕ) (Q : Subgroup (GL (Fin n) F))
    [Representation.IsIrreducible ((Representation.generalLinearNatural n).comp Q.subtype)] :
    IsCyclic (Subgroup.centralizer (Q : Set (GL (Fin n) F))) := by
  let rho := (Representation.generalLinearNatural (F := F) n).comp Q.subtype
  let f := ((Representation.IntertwiningMap.equivAlgEnd (ρ := rho)).toMonoidHom.comp
    (centralizerToIntertwiner n Q)).toHomUnits
  apply isCyclic_of_injective f
  intro x y h
  apply centralizerToIntertwiner_injective n Q
  apply (Representation.IntertwiningMap.equivAlgEnd (ρ := rho)).injective
  exact congrArg Units.val h

/-- The abelian irreducible case of the degree-three normalizer argument. -/
public theorem abelian_normalizer_isSolvable_of_irreducible [Finite F]
    (Q : Subgroup (GL (Fin 3) F)) [IsMulCommutative Q]
    [Representation.IsIrreducible ((Representation.generalLinearNatural 3).comp Q.subtype)]
    (horder : (Nat.card Q : F) ≠ 0) : Group.IsSolvable (Subgroup.normalizer (Q : Set (GL (Fin 3) F))) := by
  let : IsCyclic (Subgroup.centralizer (Q : Set (GL (Fin 3) F))) :=
    centralizer_isCyclic_of_irreducible 3 Q
  exact Representation.generalLinear_normalizer_isSolvable_of_abelian_centralizer
    3 (by decide) Q horder

/-- A nonabelian three-subgroup of GL₃ in characteristic two has solvable
normalizer. Absolute irreducibility gives a cyclic centralizer; the induced
automizer is solvable by its orbit on abelian index-three subgroups. -/
public theorem threeGroup_normalizer_isSolvable [Finite F] [CharP F 2]
    (Q : Subgroup (GL (Fin 3) F)) (hQ : IsPGroup 3 Q)
    (hnonab : ¬ IsMulCommutative Q) : Group.IsSolvable (Subgroup.normalizer (Q : Set (GL (Fin 3) F))) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let hirr : Representation.IsAbsolutelyIrreducible
      ((Representation.generalLinearNatural 3).comp Q.subtype) :=
    Representation.generalLinearNatural_three_isAbsolutelyIrreducible_of_isPGroup
      (p := 2) (by decide : Odd 3) (by decide) Q hQ hnonab
  let : Representation.IsIrreducible
      ((Representation.generalLinearNatural 3).comp Q.subtype) :=
    hirr.irreducible_of_isAbsolutelyIrreducible
  let : IsCyclic (Subgroup.centralizer (Q : Set (GL (Fin 3) F))) :=
    centralizer_isCyclic_of_irreducible 3 Q
  let : Group.IsSolvable Q.normalizerMonoidHom.range :=
    Representation.RankThreeNonabelianAutomizer.automizer_isSolvable
      (p := 2) (by decide : Odd 3) (by decide) Q hQ hnonab
  let f := Q.normalizerMonoidHom.rangeRestrict
  let : Group.IsSolvable f.ker := by
    have hk : f.ker = (Subgroup.centralizer (Q : Set (GL (Fin 3) F))).subgroupOf
        (Subgroup.normalizer (Q : Set (GL (Fin 3) F))) := by
      rw [MonoidHom.ker_rangeRestrict, Q.normalizerMonoidHom_ker]
    rw [hk]
    let : IsMulCommutative ((Subgroup.centralizer (Q : Set (GL (Fin 3) F))).subgroupOf
        (Subgroup.normalizer (Q : Set (GL (Fin 3) F)))) :=
      Subgroup.subgroupOf_isMulCommutative _ _
    exact Group.isSolvable_of_comm mul_comm'
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f
    (by rw [Subgroup.range_subtype])

end CFSG.Quasithin.MainConverse.UnitaryThreeSections.Exhaustion.PrimitiveAbelian
