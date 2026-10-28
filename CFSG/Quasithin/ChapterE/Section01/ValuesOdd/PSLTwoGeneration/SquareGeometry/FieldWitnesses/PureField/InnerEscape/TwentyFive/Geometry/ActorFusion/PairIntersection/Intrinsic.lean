module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.ActorFusion.Inputs
public import GorensteinWalter.PGL2DerivedSubgroup

/-!
# Intrinsic markings for the characteristic-five centralizers

In PGL₂(5) × C₂, the inverse image of PSL₂(5) is the product of the
commutator subgroup and the center. Both factors are preserved by every
isomorphism. Thus the literal large subgroup of any frame is independent
of its supplied comparison, even when that comparison moves the linear
factor. The final theorem applies this description to the original Sylow.

Source: the local coordinate calculation supporting Aschbacher--Smith
E.1.14(6), printed p.214, referring to Asc82a, Lemma 4.10.
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix

private theorem map_center_eq {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (center G).map e.toMonoidHom = center H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy := mem_center_iff.mp hy
    apply mem_center_iff.mpr
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    change e w * e y = e y * e w
    simpa only [map_mul] using congrArg e (hy w)
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    have hx := mem_center_iff.mp hx
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y)

private theorem map_derivedCenter_eq {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) :
    (commutator G ⊔ center G).map e.toMonoidHom = commutator H ⊔ center H := by
  rw [Subgroup.map_sup, map_center_eq, map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  rfl

private theorem product_derivedCenter {G H : Type*} [Group G] [Group H] [IsMulCommutative H]
    (hG : center G = ⊥) :
    commutator (G × H) ⊔ center (G × H) = (commutator G).prod ⊤ := by
  have hd : commutator (G × H) = (commutator G).prod ⊥ := by
    rw [commutator_def, ← top_prod_top, commutator_prod_prod]
    rw [← commutator_def, ← commutator_def, commutator_eq_bot H]
  rw [hd, Subgroup.center_prod, hG, Subgroup.center_eq_top]
  apply le_antisymm
  · exact sup_le (prod_mono le_rfl bot_le) (prod_mono bot_le le_rfl)
  · rintro ⟨x, y⟩ hxy
    have hx : (x, (1 : H)) ∈ (commutator G).prod (⊥ : Subgroup H) := ⟨hxy.1, rfl⟩
    have hy : ((1 : G), y) ∈ (⊥ : Subgroup G).prod (⊤ : Subgroup H) := ⟨rfl, trivial⟩
    simpa only [Prod.mk_mul_mk, mul_one, one_mul] using mul_mem_sup hx hy

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame
variable {F : Type*} [Field F] [Finite F] {σ : F ≃+* F}
variable (c : Frame σ) (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2)

/-- Every comparison identifies the PSL₂ preimage with the same intrinsic subgroup. -/
theorem psl_preimage_comparison (i : Bool)
    (a : c.centralizerAt i ≃* centralizer ({pure σ} : Set (innerModel F σ))) :
    (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2)
      (R := FixedPoints.subfield (zpowers σ) F)).range.comap
        ((projectiveProjection hF σ hσ).comp a.toMonoidHom) =
      commutator (c.centralizerAt i) ⊔ center (c.centralizerAt i) := by
  let K := FixedPoints.subfield (zpowers σ) F
  let e := a.trans (pureCentralizerEquiv (by decide : Nat.Prime 5) (by decide) hF σ hσ)
  have hK : Nat.card K = 5 := fixedSubfield_card hF σ
    ((orderOf_eq_prime_iff (x := σ)).mp hσ).1
    ((orderOf_eq_prime_iff (x := σ)).mp hσ).2
  have hd : commutator (PGL2 K) =
      (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three K
      ⟨5, 1, by decide, by decide, le_rfl, by simpa using hK⟩ (by omega)
  have hm := map_derivedCenter_eq e
  rw [product_derivedCenter (pgl2_center_eq_bot K), hd] at hm
  ext x
  change (e x).1 ∈ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range ↔
    x ∈ commutator (c.centralizerAt i) ⊔ center (c.centralizerAt i)
  have hh := mem_map_equiv (f := e)
    (K := commutator (c.centralizerAt i) ⊔ center (c.centralizerAt i)) (x := e x)
  rw [hm] at hh
  simpa only [mem_prod, mem_top, and_true, e.symm_apply_apply] using hh

/-- Intrinsic description of the literal projective preimage. -/
theorem projection_preimage_eq_derivedCenter (i : Bool) :
    (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2)
      (R := FixedPoints.subfield (zpowers σ) F)).range.comap
        (c.projection hF hσ i) =
      commutator (c.centralizerAt i) ⊔ center (c.centralizerAt i) :=
  c.psl_preimage_comparison hF hσ i (c.comparisonAt i)

/-- Replacing the supplied comparison does not change the PSL₂ preimage. -/
theorem projection_preimage_independent (i : Bool)
    (a : c.centralizerAt i ≃* centralizer ({pure σ} : Set (innerModel F σ))) :
    (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2)
      (R := FixedPoints.subfield (zpowers σ) F)).range.comap
        (c.projection hF hσ i) =
    (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2)
      (R := FixedPoints.subfield (zpowers σ) F)).range.comap
        ((projectiveProjection hF σ hσ).comp a.toMonoidHom) :=
  (c.projection_preimage_eq_derivedCenter hF hσ i).trans
    (c.psl_preimage_comparison hF hσ i a).symm

/-- The large subgroup is independent of any coordinate choices. -/
theorem large_eq_intrinsic (i : Bool) :
    c.large hF hσ i = (c.T : Subgroup (innerModel F σ)) ⊓
      (commutator (c.centralizerAt i) ⊔ center (c.centralizerAt i)).map
        (c.centralizerAt i).subtype := by
  unfold large
  rw [c.projection_preimage_eq_derivedCenter hF hσ]

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame
