module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.Setup
public import Theory.GroupTheory.PGroup.UniqueInvolution
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# A fixed marked four-group from a noncyclic inner preimage

In a centerless group, commutation with an inner automorphism means fixing
its conjugating element. Thus the inner preimage of the abelian actor is an
abelian two-group fixed pointwise by the entire actor. If it is not cyclic,
uniqueness of involutions fails; adjoining a second involution to the marked
one gives the required four-group.

For the actual normalized projective unitary group, simplicity and the
explicit inverted root line prove centerlessness without a separate model
simplicity or perfectness theorem. This discharges the noncyclic branch of
AbelianOuterCoordinateGeometry once the standard-four fixer is placed.
Source: Aschbacher--Smith E.1.14(7), printed p.214, and A.3.21(a)--(b),
printed p.55; Aschbacher (1982), Lemma 4.11.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry
variable {K : Type*} [Group K]

private theorem fixes_innerPreimage (hZ : center K = ⊥)
    (U : Subgroup (MulAut K)) [IsMulCommutative U]
    (a : MulAut K) (ha : a ∈ U) (x : K) (hx : x ∈ U.comap MulAut.conj) : a x = x := by
  apply MulAut.conj_injective_of_center_eq_bot hZ
  have hcomm : a * MulAut.conj x = MulAut.conj x * a :=
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : U) ⟨MulAut.conj x, hx⟩)
  calc
    MulAut.conj (a x) = a * MulAut.conj x * a⁻¹ := by ext y; simp
    _ = MulAut.conj x := by rw [hcomm, mul_inv_cancel_right]

private theorem innerPreimage_isMulCommutative (hZ : center K = ⊥)
    (U : Subgroup (MulAut K)) [IsMulCommutative U] :
    IsMulCommutative (U.comap MulAut.conj) := by
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  have h := fixes_innerPreimage hZ U (MulAut.conj x.val) x.property y.val y.property
  exact mul_inv_eq_iff_eq_mul.mp h

private theorem exists_fixed_four [Finite K]
    (hZ : center K = ⊥) (U : Subgroup (MulAut K))
    (hU : IsPGroup 2 U) [IsMulCommutative U]
    (hn : ¬ IsCyclic (U.comap MulAut.conj))
    (w : K) (hw : orderOf w = 2) (hwU : MulAut.conj w ∈ U) :
    ∃ B : Subgroup K, IsElementaryAbelian 2 B ∧ Nat.card B = 4 ∧ w ∈ B ∧
      ∀ a ∈ U, ∀ x ∈ B, a x = x := by
  let C := U.comap MulAut.conj
  let : IsMulCommutative C := innerPreimage_isMulCommutative hZ U
  have hC : IsPGroup 2 C := hU.comap_of_injective MulAut.conj
    (MulAut.conj_injective_of_center_eq_bot hZ)
  let v : C := ⟨w, hwU⟩
  have hv : orderOf v = 2 := by
    rw [← Subgroup.orderOf_coe v]
    exact hw
  obtain ⟨x, hx, hxv⟩ : ∃ x : C, orderOf x = 2 ∧ x ≠ v := by
    by_contra! h
    exact hn (hC.isCyclic_of_unique_involution_of_isMulCommutative ⟨v, hv, h⟩)
  let B : Subgroup K := closure ({w, x.val} : Set K)
  let : IsKleinFour B := isKleinFour_closure_pair_of_orderOf w x.val hw
    (by simpa only [orderOf_coe] using hx)
    (fun he => hxv (Subtype.ext he.symm))
    (congrArg Subtype.val (mul_comm' v x))
  have hBC : B ≤ C := by
    apply (closure_le _).mpr
    intro y hy
    rcases hy with rfl | rfl
    · exact hwU
    · exact x.property
  have hBe : IsElementaryAbelian 2 B :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by simp only [IsKleinFour.exponent_two, dvd_refl] }
  refine ⟨B, hBe, IsKleinFour.card_four, subset_closure (by simp), ?_⟩
  intro a ha y hy
  exact fixes_innerPreimage hZ U a ha y (hBC hy)

/-- The noncyclic inner preimage supplies a genuine four-group containing
the marked projective involution and fixed pointwise by the whole actor. -/
theorem fixed_four_of_noncyclic_innerPreimage {F : Type} [Field F] [Finite F]
    (J : HermitianForm 3 F) (hZ : center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥)
    (U : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hU : IsPGroup 2 U) [IsMulCommutative U]
    (hn : ¬ IsCyclic (U.comap MulAut.conj))
    (w : ProjectiveSpecialUnitaryMatrixGroup J) (hw : orderOf w = 2)
    (hwU : MulAut.conj w ∈ U) :
    ∃ B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      IsElementaryAbelian 2 B ∧ Nat.card B = 4 ∧ w ∈ B ∧
        ∀ a ∈ U, ∀ x ∈ B, a x = x := by
  let : Finite (ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  exact exists_fixed_four hZ U hU hn w hw hwU

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry

public section

open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry
variable {F : Type*} [Field F]
/-- The explicit inverted root line excludes an abelian simple model. -/
theorem projective_center_eq_bot (J : HermitianForm 3 F)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (h2 : (2 : F) ≠ 0) :
    center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
  rcases (inferInstance : (center (ProjectiveSpecialUnitaryMatrixGroup J)).Normal).eq_bot_or_eq_top
      with h | h
  · exact h
  · let : IsMulCommutative (ProjectiveSpecialUnitaryMatrixGroup J) := center_eq_top_iff.mp h
    let t : Multiplicative (FixedBy.subfield F J.conj) := Multiplicative.ofAdd 1
    have he : fixedRoot J hJ h2 t = (fixedRoot J hJ h2 t)⁻¹ := by
      have hi := fixedRoot_inverted J hJ h2 t
      rw [mul_comm' (hermitianTorusPSU J hJ (-1)), mul_inv_cancel_right] at hi
      exact hi
    have ht : t = t⁻¹ := fixedRoot_injective J hJ h2 (he.trans (map_inv _ _).symm)
    have hF : (1 : F) = -1 := congrArg (fun s : Multiplicative (FixedBy.subfield F J.conj) =>
      (s.toAdd : F)) ht
    apply (h2 ?_).elim
    linear_combination hF
end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry
