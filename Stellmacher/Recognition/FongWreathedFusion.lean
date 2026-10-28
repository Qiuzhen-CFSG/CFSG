module

public import Stellmacher.Recognition.FongWreathedFusionOrientationDefs
public import Stellmacher.Recognition.FongWreathedFusionTable
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Assembling Fong's six ambient classes from an oriented presentation

For a compatible actual presentation, the fourteen internal representatives
collapse to the six ambient classes `F,F³,F²,F⁻²,XF²,J`. The base-orientation
hypothesis supplies the four fusions sensitive to the choice of generators;
the quaternion automizer and involution fusion supply the others. Separation
holds for every presentation. Conjugating each two-element into the Sylow
subgroup gives ambient coverage and uniqueness of its representative.

These assembly theorems take `BaseOrientation` explicitly. The existence of
such a presentation is the separate base-normalizer calculation; an arbitrary
initial presentation is not assumed to satisfy it.

Source: Fong (1967), pp. 69–70, table (4) and equation (5).
-/

namespace Stellmacher.Recognition.FongWreathedIntrinsic
open ABG

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
  (S : Sylow 2 G) (P : Wreathed.Presentation S 2)

private theorem sylow_fusionRepresentative_covers (ho : BaseOrientation S P)
    (x : S) (hx : x ≠ 1) :
    ∃ i : Fin 6, IsConj (x : G) ((fusionRepresentative S P i : S) : G) := by
  obtain ⟨i, hi⟩ := sylowRepresentative_covers P x
  have h := (S : Subgroup G).subtype.map_isConj hi
  fin_cases i
  · exact (hx (isConj_one_left.mp hi)).elim
  · exact ⟨5, h⟩
  · exact ⟨5, h.trans (isConj_X_J S P)⟩
  · exact ⟨2, h⟩
  · exact ⟨3, h⟩
  · exact ⟨4, h⟩
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨3, h.trans ho.square_inv_E.symm⟩
  · exact ⟨4, h.trans ho.X_square_EJ.symm⟩
  · exact ⟨2, h.trans ho.square_EX.symm⟩
  · exact ⟨4, h.trans ho.X_square_EXJ.symm⟩
  · exact ⟨4, h.trans (isConj_XF_sq_EF S P).symm⟩
  · exact ⟨5, h.trans (isConj_EF_inv_J S P)⟩

/-- Every nonidentity two-element belongs to one of the six classes. -/
public theorem fusionRepresentative_covers (ho : BaseOrientation S P)
    (x : G) (hx : IsPElement 2 x) (hne : x ≠ 1) :
    ∃ i : Fin 6, IsConj x ((fusionRepresentative S P i : S) : G) := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨y, hy⟩ := S.exists_isConj_of_orderOf_eq_prime_pow hn
  have hyne : y ≠ 1 := by
    intro he
    apply hne
    apply isConj_one_left.mp
    simpa only [he, Subgroup.coe_one] using hy
  obtain ⟨i, hi⟩ := sylow_fusionRepresentative_covers S P ho y hyne
  exact ⟨i, hy.trans hi⟩

/-- The six classes cover each nonidentity two-element exactly once. -/
public theorem fusionRepresentative_unique (ho : BaseOrientation S P)
    (x : G) (hx : IsPElement 2 x) (hne : x ≠ 1) :
    ∃! i : Fin 6, IsConj x ((fusionRepresentative S P i : S) : G) := by
  obtain ⟨i, hi⟩ := fusionRepresentative_covers S P ho x hx hne
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact fusionRepresentative_separated S P j i (hj.symm.trans hi)

/-- The oriented six-class statement, with actual representatives in the Sylow subgroup. -/
public structure SixClassFusion : Prop where
  base : BaseOrientation S P
  covers : ∀ x : G, IsPElement 2 x → x ≠ 1 →
    ∃! i : Fin 6, IsConj x ((fusionRepresentative S P i : S) : G)
  separated : ∀ i j : Fin 6,
    IsConj ((fusionRepresentative S P i : S) : G)
      ((fusionRepresentative S P j : S) : G) → i = j
  orders : ∀ i : Fin 6, orderOf (fusionRepresentative S P i) = ![8, 8, 4, 4, 4, 2] i
  X_square_EF : IsConj ((X P * F P ^ 2 : S) : G) ((E P * F P : S) : G)
  X_EF_inv : IsConj ((X P : S) : G) ((E P * (F P)⁻¹ : S) : G)
  EF_inv_J : IsConj ((E P * (F P)⁻¹ : S) : G) ((J P : S) : G)

/-- Once the base orientation is chosen, all of equation (5) follows. -/
public theorem sixClassFusion_of_baseOrientation (ho : BaseOrientation S P) :
    SixClassFusion S P where
  base := ho
  covers := fusionRepresentative_unique S P ho
  separated := fusionRepresentative_separated S P
  orders := fusionRepresentative_orderOf S P
  X_square_EF := isConj_XF_sq_EF S P
  X_EF_inv := isConj_X_EF_inv S P
  EF_inv_J := isConj_EF_inv_J S P

end Stellmacher.Recognition.FongWreathedIntrinsic
