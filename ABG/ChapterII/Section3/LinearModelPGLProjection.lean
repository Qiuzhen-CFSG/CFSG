module
public import Theory.SpecificGroups.GL2.TopDeterminantCentralLayer
public import ABG.ChapterII.Section3.MatrixModelCentralQuotient
public import GorensteinWalter.NormalSL2CentralPGLProjection

/-!
# The canonical PGL projection of a full linear determinant model

For an actual determinant level at the full two-part of |F|-1, suppose its
chosen Sylow subgroup is semidihedral or wreathed with scalar center in GL2.
There is a surjection onto PGL2(F) whose kernel is the actual model center,
a two-group. On the original determinant-one subgroup it preserves the
canonical SL2 projective map. The inverse image of the canonical PSL2 range
is precisely the predecessor determinant level inside the full model.

The exact center and central-join theorem identifies that predecessor as
the join of the model center and determinant-one subgroup, of index two.
The actual matrix Sylow quotient is dihedral. Applying the prescribed
normal-SL2 central-quotient projection theorem constructs the surjection
and retains both its element equation and its exact subgroup inverse image.
The Sylow hypotheses are produced by the existing linear wreathed and
semidihedral matrix models, including determinant level one.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article p26. This is
the concrete target projective map for the cyclic-square extension comparison;
no abstract linear-group recognition or action agreement is assumed.
-/

namespace ABG
open GorensteinWalter Matrix.GeneralLinearGroup

public theorem exists_top_determinant_pgl_projection
    (F : Type*) [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (m : ℕ) (hm : 1 ≤ m) (hd : 2 ^ m ∣ Nat.card F - 1)
    (ho : Odd ((Nat.card F - 1) / 2 ^ m))
    (S : Sylow 2 (determinantTwoPower F m))
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S)
    (hcenter : (Subgroup.center S).map
      ((determinantTwoPower F m).subtype.comp (S : Subgroup _).subtype) ≤
        Subgroup.center (GL (Fin 2) F)) :
    ∃ f : determinantTwoPower F m →* PGL2 F,
      Function.Surjective f ∧ f.ker = Subgroup.center (determinantTwoPower F m) ∧
      IsPGroup 2 f.ker ∧
      (∀ a : determinantTwoPower F 0,
        f ⟨a.val, determinantTwoPower_mono (Nat.zero_le m) a.property⟩ =
          Matrix.ProjectiveSpecialLinearGroup.toPGL
            (sl2ProjectiveProjection F (determinantTwoPowerZeroEquivSL F a))) ∧
      (Matrix.ProjectiveSpecialLinearGroup.toPGL.range).comap f =
        (determinantTwoPower F (m - 1)).subgroupOf (determinantTwoPower F m) := by
  let D := determinantTwoPower F m
  let K := determinantTwoPower F 0
  let B := determinantTwoPower F (m - 1)
  let M := K.subgroupOf D
  have hKD : K ≤ D := determinantTwoPower_mono (Nat.zero_le m)
  have hBD : B ≤ D := determinantTwoPower_mono (Nat.sub_le m 1)
  let : M.Normal := inferInstance
  let eM : M ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (Subgroup.subgroupOfEquivOfLe hKD).trans (determinantTwoPowerZeroEquivSL F)
  have hcD : subgroupCenter (S : Subgroup D) ≤ Subgroup.center D := by
    rintro c ⟨c, hc, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro a
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcenter ⟨c, hc, rfl⟩) a.val
  obtain ⟨heC, hquot⟩ := hasDihedralSylowTwo_quotient_center_of_matrix_model D.subtype
    D.subtype_injective m (by rw [D.range_subtype]) S hS hcD
  have hCp : IsPGroup 2 (Subgroup.center D) := by
    rw [heC]
    exact (S.isPGroup'.to_subgroup (Subgroup.center S)).map (S : Subgroup D).subtype
  obtain ⟨_, hgen, hbi⟩ := top_determinant_central_layer F m hm hd ho
  have hCM : Subgroup.center D ⊔ M = B.subgroupOf D := by
    apply Subgroup.map_injective D.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKD,
      Subgroup.map_subgroupOf_eq_of_le hBD]
    exact hgen
  have hindex : (Subgroup.center D ⊔ M).index = 2 := by
    rw [hCM]
    exact hbi
  obtain ⟨f, hf, hfker, hfcore, hfpre⟩ :=
    exists_pgl2_projection_of_central_sl2_join_index_two S (Subgroup.center D) M
      le_rfl hcD hindex hquot F hF eM
  refine ⟨f, hf, hfker, hfker ▸ hCp, ?_, hfpre.trans hCM⟩
  intro a
  exact hfcore ⟨⟨a.val, hKD a.property⟩, a.property⟩

end ABG
