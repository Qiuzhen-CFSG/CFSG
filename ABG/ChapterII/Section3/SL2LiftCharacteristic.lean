module

public import Theory.SpecificGroups.SL2.NoIndexTwo
public import Theory.GroupTheory.PGroup.CharacteristicKernel

/-!
# Characteristicity and uniqueness of the central SL2 lift

In Alperin--Brauer--Gorenstein, II.3 Proposition 2 (article pages 22--23),
the inverse image H0 of the normal PSL2 subgroup has the form Z L, with Z
a central two-group and L a normal SL2 subgroup over a finite odd field.
The lift L is characteristic in H0 and is the only normal SL2 supplement
to Z, even when the field has order three.

SL2 has no subgroup of index two, by transvection generation. Thus its image
in every finite two-group is trivial. The generic quotient-map universal
property gives containment in every normal subgroup with two-group quotient,
characteristicity, and uniqueness. This proves the source's two-residual
argument without assuming perfectness. The source-facing wrappers retain
centrality of Z, although the universal property only needs its two-group
supplement property. Normality in the larger ambient group is obtained by the
consumer from characteristicity in its normal subgroup H0. The no-index-two
transport is public for the final ambient uniqueness argument.
-/

namespace ABG

public theorem sl2_no_normal_index_two
    {G F : Type*} [Group G] [Field F] (hF : (2 : F) ≠ 0)
    (e : G ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ∀ K : Subgroup G, K.Normal → K.index ≠ 2 := by
  intro K _ hK
  have hi : (K.comap e.symm.toMonoidHom).index = K.index :=
    K.index_comap_of_surjective e.symm.surjective
  exact Matrix.SpecialLinearGroup.index_ne_two hF _ (hi.trans hK)

/-- An odd-field SL2 subgroup is contained in every normal subgroup with
two-group quotient. -/
public theorem sl2_lift_le_normal_of_two_group_quotient
    {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]
    (L N : Subgroup H) [N.Normal] (hF : (2 : F) ≠ 0)
    (eL : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hN : IsPGroup 2 (H ⧸ N)) : L ≤ N := by
  exact Subgroup.le_normal_of_no_normal_index_prime L N (sl2_no_normal_index_two hF eL) hN

/-- The normal SL2 lift under a central two-group supplement is characteristic. -/
public theorem sl2_central_lift_characteristic
    {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]
    (Z L : Subgroup H) [L.Normal]
    (_hZcentral : Z ≤ Subgroup.center H) (hZ : IsPGroup 2 Z)
    (hgen : Z ⊔ L = ⊤) (hF : (2 : F) ≠ 0)
    (eL : L ≃* Matrix.SpecialLinearGroup (Fin 2) F) : L.Characteristic := by
  exact Subgroup.characteristic_of_no_normal_index_prime L
    (sl2_no_normal_index_two hF eL)
    (Subgroup.quotient_isPGroup_of_sup_eq_top Z L hZ hgen)

/-- Two normal odd-field SL2 supplements to the same central two-group agree. -/
public theorem sl2_central_lift_unique
    {H F E : Type*} [Group H] [Finite H] [Field F] [Finite F] [Field E] [Finite E]
    (Z L M : Subgroup H) [L.Normal] [M.Normal]
    (_hZcentral : Z ≤ Subgroup.center H) (hZ : IsPGroup 2 Z)
    (hgenL : Z ⊔ L = ⊤) (hgenM : Z ⊔ M = ⊤)
    (hF : (2 : F) ≠ 0) (hE : (2 : E) ≠ 0)
    (eL : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (eM : M ≃* Matrix.SpecialLinearGroup (Fin 2) E) : M = L := by
  exact Subgroup.eq_of_no_normal_index_prime M L
    (sl2_no_normal_index_two hE eM) (sl2_no_normal_index_two hF eL)
    (Subgroup.quotient_isPGroup_of_sup_eq_top Z M hZ hgenM)
    (Subgroup.quotient_isPGroup_of_sup_eq_top Z L hZ hgenL)

end ABG
