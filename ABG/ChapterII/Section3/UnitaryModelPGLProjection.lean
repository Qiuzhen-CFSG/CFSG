module
public import ABG.ChapterII.Section2.UnitaryTopDeterminantCentralLayer
public import ABG.ChapterII.Section3.MatrixModelCentralQuotient
public import GorensteinWalter.NormalSL2CentralPGLProjection

/-!
# The canonical PGL projection of a full unitary determinant model

Let q = p^n with odd p and nonzero n, and let 2^m be the exact two-part of
q+1, with m at least one. Suppose an actual Sylow subgroup of SU2Level m
is semidihedral or wreathed and its mapped center is central in GU2.
There is a surjection from this determinant level onto PGL2(GF(q)) whose
kernel is the actual model center, a two-group. Its formula on level zero
uses the supplied special-unitary to special-linear equivalence eSU.
The exact inverse image of the canonical PSL2 range is level m-1 inside
the full determinant level.

The faithful inclusion into GL2(GF(q^2)) and the matrix Sylow quotient
theorem show that quotienting by the actual center gives dihedral Sylow
two-subgroups. The unitary top-center theorem identifies the join of this
center and level zero with level m-1, of index two. The prescribed normal
SL2 central-quotient theorem now constructs the projective map, retaining
its element formula and subgroup inverse image. All inclusions use the
original Hermitian unitary model, including at m=1.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article page 26.
This supplies the actual target projective map for the unitary cyclic-square
extension comparison; the special-unitary equivalence is retained as input
so later comparisons can agree on the identified original core.
-/

namespace ABG
open GorensteinWalter Matrix.GeneralLinearGroup

public theorem exists_top_unitary_determinant_pgl_projection
    (p n : ℕ) [Fact p.Prime] (hp : Odd p) (hn : n ≠ 0)
    (m : ℕ) (hm : 1 ≤ m) (hd : 2 ^ m ∣ p ^ n + 1)
    (ho : Odd ((p ^ n + 1) / 2 ^ m))
    (eSU : (unitaryForm 2 p n hn).specialSubgroup ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField p n))
    (S : Sylow 2 (SU2Level p n hn m))
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S)
    (hcenter : (Subgroup.center S).map
      ((SU2Level p n hn m).subtype.comp (S : Subgroup _).subtype) ≤
        Subgroup.center (GU2 p n hn)) :
    ∃ f : SU2Level p n hn m →* PGL2 (GaloisField p n),
      Function.Surjective f ∧ f.ker = Subgroup.center (SU2Level p n hn m) ∧
      IsPGroup 2 f.ker ∧
      (∀ a : SU2Level p n hn 0,
        f ⟨a.val, SU2Level_mono p n hn (Nat.zero_le m) a.property⟩ =
          Matrix.ProjectiveSpecialLinearGroup.toPGL
            (sl2ProjectiveProjection (GaloisField p n)
              (eSU (SU2LevelZeroEquivSpecial p n hn a)))) ∧
      (Matrix.ProjectiveSpecialLinearGroup.toPGL.range).comap f =
        (SU2Level p n hn (m - 1)).subgroupOf (SU2Level p n hn m) := by
  let D := SU2Level p n hn m
  let K := SU2Level p n hn 0
  let B := SU2Level p n hn (m - 1)
  let M := K.subgroupOf D
  have hKD : K ≤ D := SU2Level_mono p n hn (Nat.zero_le m)
  have hBD : B ≤ D := SU2Level_mono p n hn (Nat.sub_le m 1)
  let : M.Normal := inferInstance
  let eM : M ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p n) :=
    (Subgroup.subgroupOfEquivOfLe hKD).trans
      ((SU2LevelZeroEquivSpecial p n hn).trans eSU)
  have hcD : subgroupCenter (S : Subgroup D) ≤ Subgroup.center D := by
    rintro c ⟨c, hc, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro a
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcenter ⟨c, hc, rfl⟩) a.val
  let j : D →* GL (Fin 2) (GaloisField p (2 * n)) :=
    (unitaryForm 2 p n hn).unitarySubgroup.subtype.comp D.subtype
  have hj : Function.Injective j :=
    (unitaryForm 2 p n hn).unitarySubgroup.subtype_injective.comp D.subtype_injective
  have hlevel : j.range ≤ determinantTwoPower (GaloisField p (2 * n)) m := by
    rintro A ⟨a, rfl⟩
    exact a.property
  obtain ⟨heC, hquot⟩ := hasDihedralSylowTwo_quotient_center_of_matrix_model j hj
    m hlevel S hS hcD
  have hCp : IsPGroup 2 (Subgroup.center D) := by
    rw [heC]
    exact (S.isPGroup'.to_subgroup (Subgroup.center S)).map (S : Subgroup D).subtype
  obtain ⟨_, hgen, hbi⟩ := SU2Level_top_central_layer p n hp hn m hm hd ho
  have hCM : Subgroup.center D ⊔ M = B.subgroupOf D := by
    apply Subgroup.map_injective D.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKD,
      Subgroup.map_subgroupOf_eq_of_le hBD]
    exact hgen
  have hindex : (Subgroup.center D ⊔ M).index = 2 := by
    rw [hCM]
    exact hbi
  have hF : IsOddPrimePower (Nat.card (GaloisField p n)) :=
    ⟨p, n, Fact.out, hp, Nat.pos_of_ne_zero hn, GaloisField.card p n hn⟩
  obtain ⟨f, hf, hfker, hfcore, hfpre⟩ :=
    exists_pgl2_projection_of_central_sl2_join_index_two S (Subgroup.center D) M
      le_rfl hcD hindex hquot (GaloisField p n) hF eM
  refine ⟨f, hf, hfker, hfker ▸ hCp, ?_, hfpre.trans hCM⟩
  intro a
  exact hfcore ⟨⟨a.val, hKD a.property⟩, a.property⟩

end ABG
