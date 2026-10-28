module

public import Theory.GroupTheory.SubgroupSectionConjugation

/-!
# Conjugating an exact centralizer image

For a normal subgroup of the target of a homomorphism, equality between
the image of an actual centralizer and the centralizer of its image
transports along every prescribed conjugator.  The original homomorphism
and normal target subgroup are retained.  This supplies the second actual
factor-centralizer image in Aschbacher–Smith 10.2.1, pp.742–743.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H]

theorem map_conjugate_image (q : G →* H) (A : Subgroup G) (t : G) :
    (A.map (MulAut.conj t).toMonoidHom).map q =
      (A.map q).map (MulAut.conj (q t)).toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  ext x
  change q (t*x*t⁻¹) = q t*q x*(q t)⁻¹
  rw [map_mul,map_mul,map_inv]

/-- An exact centralizer image remains exact after simultaneous conjugation
of the original subgroup and its image. -/
theorem centralizer_image_eq_conjugate
    (q : G →* H) (Y : Subgroup H) [Y.Normal] (A : Subgroup G) (t : G)
    (h : (Y.comap q ⊓ centralizer (A : Set G)).map q =
      Y ⊓ centralizer (A.map q : Set H)) :
    (Y.comap q ⊓ centralizer (A.map (MulAut.conj t).toMonoidHom : Set G)).map q =
      Y ⊓ centralizer ((A.map (MulAut.conj t).toMonoidHom).map q : Set H) := by
  calc
    _ = ((Y.comap q ⊓ centralizer (A : Set G)).map q).map
        (MulAut.conj (q t)).toMonoidHom := by
      rw [←inf_centralizer_conjugate (Y.comap q) A t,map_conjugate_image]
    _ = (Y ⊓ centralizer (A.map q : Set H)).map
        (MulAut.conj (q t)).toMonoidHom := by rw [h]
    _ = _ := by rw [inf_centralizer_conjugate,map_conjugate_image]

end Theory.GroupTheory
