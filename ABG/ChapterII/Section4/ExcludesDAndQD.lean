module
public import ABG.ChapterII.Section3.QFourFusionObstruction
public import ABG.ChapterII.Section2.DQDFourFusion
public import GorensteinWalter.KleinFourMapInjective

/-!
# Q-groups contain no D-group or QD-group

No subgroup of a finite enlarged Q-group is a D-group or a QD-group.
There is no restriction to semidihedral or wreathed Sylow subgroups.

Every D/QD group has a Klein-four subgroup whose three nonidentity elements
are ambient-conjugate. Map that actual subgroup into the Q-group through the
subgroup inclusion; injectivity preserves both its four-group structure and
its nonidentity elements, and the ambient homomorphism preserves conjugacy.
This contradicts the Q-group four-fusion obstruction, which fixes a central
Sylow involution by weak closure.

This is ABG II.4 Lemma 17, article page 45. The two imported ingredients
retain every enlarged Q/D case, so no characteristic-power or simple-group
assumption is required.
-/

namespace ABG
universe u

public theorem qGroup_no_d_or_qd_subgroup
    {H : Type u} [Group H] [Finite H] (hH : IsQGroup H) (K : Subgroup H) :
    ¬ IsDGroup K ∧ ¬ IsQDGroup K := by
  apply not_or.mp
  intro hK
  obtain ⟨T, hT, hfusion⟩ := d_or_qd_exists_fused_four hK
  let W := T.map K.subtype
  have hW : IsKleinFour W := GorensteinWalter.isKleinFour_map_of_injective
    T hT K.subtype K.subtype_injective
  let e : T ≃* W := Subgroup.equivMapOfInjective T K.subtype K.subtype_injective
  apply qGroup_not_all_four_involutions_conjugate hH W hW
  intro x y hx hy
  have hx' : e.symm x ≠ 1 := fun h =>
    hx (e.symm.injective (h.trans e.symm.map_one.symm))
  have hy' : e.symm y ≠ 1 := fun h =>
    hy (e.symm.injective (h.trans e.symm.map_one.symm))
  have h := K.subtype.map_isConj (hfusion (e.symm x) (e.symm y) hx' hy')
  have hex : ((e.symm x : T) : H) = (x : H) :=
    congrArg Subtype.val (e.apply_symm_apply x)
  have hey : ((e.symm y : T) : H) = (y : H) :=
    congrArg Subtype.val (e.apply_symm_apply y)
  change IsConj (((e.symm x : T) : K) : H) (((e.symm y : T) : K) : H) at h
  rwa [hex, hey] at h

end ABG
