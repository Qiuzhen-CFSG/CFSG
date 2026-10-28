module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry.Transport
public import Theory.GroupTheory.WreathTwoSylowModel

/-!
# The definite-plane stabilizer of the natural orthogonal Sylow action

A vector supported in a single plane proves that its setwise stabilizer is
exactly the kernel of the wreath-product projection onto the two coordinate
permutations. This gives index two in the full actor. Surjectivity of the image
of a Sylow subgroup under that projection gives index two in every Sylow actor.
The existing equivalence of the actual Sylow subgroup with the dihedral group
of order eight then gives order four for the plane-stabilizer image.

Transport through the compatible action proves `[T : N_T(V_i)] = 2`, the
order-four image, and the odd local index inside `N_M(V_i)`. The argument uses
the literal action on supported vectors; no enumeration of subgroup families
or abstract wreath identification stands in for that action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the definite-plane
decomposition on printed pp.1121–1122 and the local calculation in 15.3.6(4).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03
open Subgroup
namespace OrthogonalGeometry
local instance : MulDistribMulAction OrthogonalPlaneActor OrthogonalPlaneVector :=
  FourGroupMatrixCoordinates.naturalAction
local instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction

/-- The actor preserves either definite plane exactly when its permutation part is trivial. -/
theorem mem_setwise_plane_iff (g : OrthogonalActor) (i : OrthogonalPlaneIndex) :
    g ∈ setwise (orthogonalCoordinatePlane i) ↔ g.right = 1 := by
  constructor
  · intro hg
    obtain ⟨u, hu⟩ := exists_ne (1 : OrthogonalPlaneVector)
    let w : OrthogonalVector := fun j => if j = i then u else 1
    have hw : w ∈ orthogonalCoordinatePlane i := by
      intro j hj
      exact if_neg hj
    have hf := (hg w).mpr hw
    have hi : g.right * i = i := by
      by_contra hi
      have hz := hf (g.right * i) hi
      change g.left (g.right * i) • w (g.right⁻¹ * (g.right * i)) = 1 at hz
      simp only [inv_mul_cancel_left, w, if_pos rfl] at hz
      exact hu (MulAction.injective (g.left (g.right * i)) (hz.trans (smul_one _).symm))
    exact mul_right_cancel (hi.trans (one_mul i).symm)
  · intro hg w
    constructor
    · intro hw j hj
      have h := hw j hj
      change g.left j • w (g.right⁻¹ * j) = 1 at h
      rw [hg, inv_one, one_mul] at h
      exact MulAction.injective (g.left j) (h.trans (smul_one _).symm)
    · intro hw j hj
      change g.left j • w (g.right⁻¹ * j) = 1
      rw [hg, inv_one, one_mul, hw j hj, smul_one]

theorem setwise_plane_eq_ker (i : OrthogonalPlaneIndex) :
    setwise (orthogonalCoordinatePlane i) =
      (RegularWreathProduct.rightHom : OrthogonalActor →* OrthogonalPlaneIndex).ker := by
  ext g
  exact mem_setwise_plane_iff g i

private theorem rightHom_surjective : Function.Surjective
    (RegularWreathProduct.rightHom : OrthogonalActor →* OrthogonalPlaneIndex) :=
  fun q => ⟨⟨1, q⟩, rfl⟩

/-- The full actor's plane stabilizer has index two. -/
theorem setwise_plane_index (i : OrthogonalPlaneIndex) :
    (setwise (orthogonalCoordinatePlane i)).index = 2 := by
  rw [setwise_plane_eq_ker, index_ker,
    MonoidHom.range_eq_top_of_surjective _ rightHom_surjective, Nat.card_congr (topEquiv).toEquiv]
  norm_num [OrthogonalPlaneIndex, Nat.card_eq_fintype_card]

/-- Every Sylow two-subgroup contains an actor interchanging the planes. -/
theorem sylow_right_image (P : Sylow 2 OrthogonalActor) :
    (P : Subgroup OrthogonalActor).map
      (RegularWreathProduct.rightHom : OrthogonalActor →* OrthogonalPlaneIndex) = ⊤ := by
  let Q := P.mapSurjective rightHom_surjective
  have htwo : IsPGroup 2 OrthogonalPlaneIndex := IsPGroup.of_card (n := 1) (by
    norm_num [OrthogonalPlaneIndex, Nat.card_eq_fintype_card])
  have h := Q.is_maximal' (htwo.to_subgroup ⊤) le_top
  exact h.symm

/-- The two definite planes form a two-element orbit of every Sylow subgroup. -/
theorem setwise_plane_sylow_relIndex (P : Sylow 2 OrthogonalActor)
    (i : OrthogonalPlaneIndex) :
    (setwise (orthogonalCoordinatePlane i)).relIndex P = 2 := by
  rw [setwise_plane_eq_ker, relIndex_ker, sylow_right_image,
    Nat.card_congr (topEquiv).toEquiv]
  norm_num [OrthogonalPlaneIndex, Nat.card_eq_fintype_card]

/-- The order calculation uses an equivalence of the actual Sylow subgroup. -/
theorem sylow_card (P : Sylow 2 OrthogonalActor) : Nat.card P = 8 := by
  obtain ⟨e⟩ := wreath_two_sylow_mulEquiv_dihedral_four P
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

/-- The subgroup of a Sylow actor preserving a definite plane has order four. -/
theorem plane_sylow_card (P : Sylow 2 OrthogonalActor) (i : OrthogonalPlaneIndex) :
    Nat.card ↥((P : Subgroup OrthogonalActor) ⊓ setwise (orthogonalCoordinatePlane i)) = 4 := by
  let Q := (P : Subgroup OrthogonalActor) ⊓ setwise (orthogonalCoordinatePlane i)
  have he := (Q.subgroupOf P).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show Q ≤ P from inf_le_left)).toEquiv] at he
  change Nat.card Q * Q.relIndex P = Nat.card P at he
  rw [sylow_card, show Q.relIndex P = 2 from
    (inf_relIndex_left _ _).trans (setwise_plane_sylow_relIndex P i)] at he
  change Nat.card Q = 4
  omega

end OrthogonalGeometry

namespace NaturalOrthogonalAction
open OrthogonalGeometry
variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)

include hTM

/-- The ambient plane stabilizer has index two in the given Sylow group. -/
theorem planeStabilizer_index_two (i : OrthogonalPlaneIndex) :
    ((planeStabilizer T (d.plane i)).subgroupOf T).index = 2 := by
  rw [d.index_planeStabilizer T hTM]
  exact setwise_plane_sylow_relIndex (d.sylowImage T hTM) i

/-- The given plane stabilizer is Sylow in its plane normalizer inside `M`. -/
theorem not_dvd_planeStabilizer_normalizer_relIndex (i : OrthogonalPlaneIndex) :
    ¬ 2 ∣ (planeStabilizer T (d.plane i)).relIndex
      (M ⊓ normalizer (d.plane i : Set G)) := by
  apply d.planeStabilizer_local_normalizer_index T hTM i
  · exact setwise_plane_sylow_relIndex (d.sylowImage T hTM) i
  · rw [setwise_plane_index]
/-- The action image of the actual plane stabilizer has order four. -/
theorem card_image_planeStabilizer (i : OrthogonalPlaneIndex) :
    Nat.card (d.image (planeStabilizer T (d.plane i))) = 4 := by
  rw [d.image_planeStabilizer]
  exact plane_sylow_card (d.sylowImage T hTM) i

end NaturalOrthogonalAction
end CFSG.Quasithin.Chapter15.Section03

end
