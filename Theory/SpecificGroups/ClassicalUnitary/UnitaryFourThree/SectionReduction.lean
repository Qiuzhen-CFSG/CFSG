module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Mathlib.GroupTheory.Solvable
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Data.SetLike.Fintype

/-!
# Full preimages and irreducible overgroups in the field-nine unitary model

The projection of SU onto its image in PGL has an abelian scalar kernel.
Restricting onto the full inverse image of a subgroup retains precisely that
kernel. Pulling back a normal subgroup inside the projective subgroup gives an
actual equivalence of quotients, with no assumption of ambient normality.

An invariant subspace for an overgroup is invariant for the subgroup. Thus a
proper irreducible projective subgroup lies in a maximal irreducible subgroup.
This reduction includes imprimitive groups and groups that are not absolutely
irreducible: only invariant subspaces over the defining field are tested.

Sources: the unitary and scalar-quotient conventions in GLS3, §2.7
(`refs/KGroup/GLS3/chapter2.tex`); the proper-section obligation in
Aschbacher–Smith, Theorem 0.1.2(4), printed p.4 of `refs/quasithin.pdf`.
No exhaustive subgroup classification is asserted here.
-/

open Matrix BenderSuzuki.MatrixGroups

public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

/-- The full SU inverse image, including all projective scalars. -/
@[expose] def fullPreimage {n : ℕ} (U : Subgroup (Carrier n)) :
    Subgroup (form n).specialSubgroup := U.comap (project n)

@[expose] def preimageProjection {n : ℕ} (U : Subgroup (Carrier n)) : fullPreimage U →* U :=
  (project n).subgroupComap U

theorem preimageProjection_surjective {n : ℕ} (U : Subgroup (Carrier n)) :
    Function.Surjective (preimageProjection U) :=
  (project n).subgroupComap_surjective_of_surjective U (project_surjective n)

theorem project_kernel_isSolvable (n : ℕ) : Group.IsSolvable (project n).ker := by
  let f : (project n).ker →* Subgroup.center (GL (Fin n) FiniteField.Nine) :=
    { toFun := fun x => ⟨x.val.val, by
        have hx : ProjGenLinGroup.mk x.val.val = 1 :=
          congrArg Subtype.val x.property
        exact (QuotientGroup.eq_one_iff _).mp hx⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let : Group.IsSolvable (Subgroup.center (GL (Fin n) FiniteField.Nine)) :=
    Group.isSolvable_of_comm fun _ _ => IsMulCommutative.is_comm.comm _ _
  apply Group.isSolvable_of_isSolvable_injective (f := f)
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : Subgroup.center (GL (Fin n) FiniteField.Nine) => z.val) h

/-- Restriction onto a projective subgroup loses none of the scalar kernel. -/
def preimageKernelEquiv {n : ℕ} (U : Subgroup (Carrier n)) :
    (preimageProjection U).ker ≃* (project n).ker where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val, by
    change project n x.val ∈ U
    rw [show project n x.val = 1 from x.property]
    exact U.one_mem⟩, Subtype.ext x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem preimageProjection_kernel_isSolvable {n : ℕ} (U : Subgroup (Carrier n)) :
    Group.IsSolvable (preimageProjection U).ker := by
  let := project_kernel_isSolvable n
  exact Group.isSolvable_of_isSolvable_injective
    (f := (preimageKernelEquiv U).toMonoidHom) (preimageKernelEquiv U).injective

/-- Normality is inside U, and the full inverse image of N is retained. -/
def preimageQuotientEquiv {n : ℕ} (U : Subgroup (Carrier n))
    (N : Subgroup U) [N.Normal] :
    (fullPreimage U ⧸ N.comap (preimageProjection U)) ≃* (U ⧸ N) := by
  let f := (QuotientGroup.mk' N).comp (preimageProjection U)
  have hk : f.ker = N.comap (preimageProjection U) := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((QuotientGroup.mk'_surjective N).comp (preimageProjection_surjective U)))

theorem isReducible_of_le {U V : Subgroup (Carrier 4)}
    (hUV : U ≤ V) (hV : IsReducible V) : IsReducible U := by
  obtain ⟨W, hW0, hW1, hW⟩ := hV
  exact ⟨W, hW0, hW1, fun g hg => hW g (hUV hg)⟩

theorem exists_irreducible_coatom (U : Subgroup (Carrier 4))
    (hU : U ≠ ⊤) (hred : ¬ IsReducible U) :
    ∃ M : Subgroup (Carrier 4), IsCoatom M ∧ U ≤ M ∧ ¬ IsReducible M := by
  obtain ⟨M, hM, hUM⟩ := (eq_top_or_exists_le_coatom U).resolve_left hU
  exact ⟨M, hM, hUM, fun h => hred (isReducible_of_le hUM h)⟩

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
