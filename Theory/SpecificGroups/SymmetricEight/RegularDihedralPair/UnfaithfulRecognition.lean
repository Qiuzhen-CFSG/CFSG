module

public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.PairRecognition

/-!
# Recognition through an eight-point action with kernel

The actual Sylow subgroup maps onto the marked regular dihedral subgroup.
Equality of the local quotient kernels identifies both actual local images
with S4. The common kernel lies in both locals, so their images are distinct
and generation of the action range lifts to generation of the original group.
-/

public noncomputable section
open Equiv Subgroup
open scoped MatrixGroups
namespace Theory.SpecificGroups.SymmetricEight.RegularDihedralPair

private def localImageEquiv
    {G : Type*} [Group G] (f : G →* P8) (A : Subgroup G)
    (q : A →* Perm (Fin 4)) (hq : Function.Surjective q)
    (hk : q.ker = (f.comp A.subtype).ker) : A.map f ≃* Perm (Fin 4) := by
  have he : (f.subgroupMap A).ker = q.ker := by
    rw [hk]
    ext x
    exact Subtype.ext_iff
  exact (QuotientGroup.quotientKerEquivOfSurjective (f.subgroupMap A)
    (f.subgroupMap_surjective A)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq he).trans
        (QuotientGroup.quotientKerEquivOfSurjective q hq))

/-- The actual local S4 quotient maps and marked Sylow image recognize the
whole action quotient and prove generation in the original group. -/
theorem unfaithful_representation_pair_recognition
    {G : Type*} [Group G] [Finite G]
    (f : G →* P8) (S : Sylow 2 G)
    (hS : (S : Subgroup G).map f = twoGroup)
    (hker : f.ker ≤ (S : Subgroup G))
    (A B : Subgroup G) (hSA : (S : Subgroup G) ≤ A) (hSB : (S : Subgroup G) ≤ B)
    (qA : A →* Perm (Fin 4)) (hqA : Function.Surjective qA)
    (hkA : qA.ker = (f.comp A.subtype).ker)
    (qB : B →* Perm (Fin 4)) (hqB : Function.Surjective qB)
    (hkB : qB.ker = (f.comp B.subtype).ker)
    (hne : A ≠ B) :
    A ⊔ B = ⊤ ∧ Nonempty ((G ⧸ f.ker) ≃* PSL(3, ZMod 2)) := by
  let T : Sylow 2 f.range := S.mapSurjective f.rangeRestrict_surjective
  have hT : (T : Subgroup f.range).map f.range.subtype = twoGroup := by
    change ((S : Subgroup G).map f.rangeRestrict).map f.range.subtype = twoGroup
    rw [map_map]
    exact hS
  have hne' : A.map f ≠ B.map f := fun he =>
    hne (map_injective_of_ker_le f (hker.trans hSA) (hker.trans hSB) he)
  obtain ⟨hgen,⟨e⟩⟩ := sylow_pair_recognition f.range T hT
    (A.map f) (B.map f) (map_le_range _ _) (map_le_range _ _)
    (hS ▸ map_mono hSA) (hS ▸ map_mono hSB)
    (localImageEquiv f A qA hqA hkA) (localImageEquiv f B qB hqB hkB) hne'
  refine ⟨?_,⟨(QuotientGroup.quotientKerEquivRange f).trans e⟩⟩
  apply map_injective_of_ker_le f ((hker.trans hSA).trans le_sup_left) le_top
  rw [Subgroup.map_sup,← hgen]
  exact MonoidHom.range_eq_map f

end Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
