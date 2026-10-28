module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.TwoPointRoots.Algebra
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.CentralCover.Unitary.Normalization
public import Theory.SpecificGroups.SU3.BorelTorus.Basic
public import Theory.GroupTheory.SolvableNormalSup
public import BenderSuzuki.SE.Proposition84TorusModels

/-!
# Two-point tori in PSU₃

Every Sylow two-normalizer is a genuine solvable Borel. Normalize an arbitrary
Borel pair to the opposite root normalizers; their intersection is the actual
diagonal torus. Its quotient kernel gives order (q²-1)/gcd(3,q+1).
The inverted-torus calculation identifies the literal commutator of order
q-1. Fixed/inverted factorization gives cyclic C_D(t) of order
(q+1)/gcd(3,q+1). No standard-pair premise remains in these exports.

Source: GLS4, Chapter 4, Lemma 3.2(c)-(e), with Huppert II.10.12.
-/

open Subgroup BenderSuzuki BenderSuzuki.PFAppendixIII BenderSuzuki.PFchapter1section1
open scoped commutatorElement
namespace BenderSuzuki.ZD.RankOneModelGeometry
open _root_.BenderSuzuki.MatrixGroups HermitianForm External
open HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
open scoped LinearAlgebra.Projectivization
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
private instance : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

include hn hcard hfixed hJ in
public theorem unitary_projective_borel [Finite (ProjectiveSpecialUnitaryMatrixGroup J)] (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    IsBorelSubgroup (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  obtain ⟨_, rho, alpha, _, _, _, hroot, _, _⟩ :=
    huppert_II_10_12 J (2 ^ n) hcard hfixed hJ
  obtain ⟨R, H, hR, hH, hnorm, _, hsup, hc, hRcard, _, _, _, hregular,
    ⟨coord, hcoord⟩, _⟩ := hroot
  have hcoord_eq (z : hermitianUnipotentCoord J) :
      (coord z).val = root J hJ z := by
    obtain ⟨M, hM, heq⟩ := hcoord z
    have hM' : M = hermitianUnipotentGL J z := Units.ext hM
    apply Subtype.ext
    simpa only [hM', hermitianUnipotentPSU_val] using heq
  have hRe : R = rootGroup J hJ := by
    apply le_antisymm
    · intro r hr
      obtain ⟨z, hz⟩ := coord.surjective ⟨r, hr⟩
      exact ⟨z, (hcoord_eq z).symm.trans (congrArg Subtype.val hz)⟩
    · rintro r ⟨z, rfl⟩
      rw [← hcoord_eq z]
      exact (coord z).property
  let S := EvenTwoRank.rootSylow J hJ (by omega : 0 < n) hcard hfixed
  have hS : (S : Subgroup _) = R := hRe.symm
  let U := (MulAction.stabilizer _ alpha).comap rho
  have hUne : R ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hRcard
    have hp : 1 < (2 ^ n) ^ 3 := one_lt_pow₀ (one_lt_pow₀ (by decide) (by omega)) (by decide)
    omega
  let _ : MulAction (ProjectiveSpecialUnitaryMatrixGroup J)
      {x : ℙ E (Fin 3 → E) // x ∈ {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0),
        x = Projectivization.mk E v hv ∧
          dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}} :=
    MulAction.compHom _ rho
  have hN : normalizer (R : Set _) = U :=
    normalizer_eq_stabilizer_of_regular_compl R alpha hR hUne hregular hnorm
  have hRp : IsPGroup 2 R := by rw [← hS]; exact S.isPGroup'
  let : Group.IsNilpotent R := hRp.isNilpotent
  let : IsCyclic H := hc
  let := IsCyclic.commGroup (α := H)
  let eR := subgroupOfEquivOfLe hR
  let eH := subgroupOfEquivOfLe hH
  let : Group.IsSolvable (R.subgroupOf U) :=
    Group.isSolvable_of_isSolvable_injective (f := eR.toMonoidHom) eR.injective
  let : Group.IsSolvable (H.subgroupOf U) :=
    Group.isSolvable_of_isSolvable_injective (f := eH.toMonoidHom) eH.injective
  let : (R.subgroupOf U).Normal := (normal_subgroupOf_iff_le_normalizer hR).mpr hnorm
  have hsol : Group.IsSolvable U := by
    apply Group.isSolvable_of_normal_sup_eq_top (R.subgroupOf U) (H.subgroupOf U)
    rw [← subgroupOf_sup hR hH, hsup, subgroupOf_self]
  have hBU : IsBorelSubgroup U := ⟨hsol, S, by rw [hS, hN]⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) S P
  have hm : (S : Subgroup _).map (MulAut.conj g).toMonoidHom = (P : Subgroup _) :=
    congrArg Sylow.toSubgroup hg
  have hu : U.map (MulAut.conj g).toMonoidHom = normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [← hN, ← hS, map_equiv_normalizer_eq, hm]
    rfl
  exact hu ▸ hBU.map_mulEquiv (MulAut.conj g)

include hn hcard hfixed hJ in
public theorem unitary_projective_twoPoint_torus (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : IsInvolution t)
    (htB : t ∉ normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
    IsCyclic (twoPoint (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) t) ∧
      Nat.card (twoPoint (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) t) =
        ((2 ^ n) ^ 2 - 1) / Nat.gcd 3 (2 ^ n + 1) := by
  let B := normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))
  obtain ⟨c, hcB, hcBt, _⟩ := exists_unitary_borel_pair_normalization
    J hJ (by omega : 0 < n) hcard hfixed B (unitary_projective_borel J hn hcard hfixed hJ P) t ht htB
  have hm : (twoPoint B t).map c.toMonoidHom = BorelTorus.projectiveTorus J hJ := by
    rw [twoPoint, Subgroup.map_inf _ _ _ c.injective, hcB, hcBt,
      ← EvenSemilinear.rootTorus_eq_normalizer_inf J hJ
        (EvenSemilinear.coord_first_surjective J hcard hfixed 1)]
    rfl
  let e := ((twoPoint B t).equivMapOfInjective c.toMonoidHom c.injective).trans
    (MulEquiv.subgroupCongr hm)
  have hc : IsCyclic (BorelTorus.projectiveTorus J hJ) :=
    isCyclic_of_surjective (hermitianTorusPSU J hJ).rangeRestrict (hermitianTorusPSU J hJ).rangeRestrict_surjective
  refine ⟨e.isCyclic.mpr hc, ?_⟩
  rw [Nat.card_congr e.toEquiv, BorelTorus.projective_card J hJ hcard
    (huppert_II_10_4_conj_eq_frobenius J (2 ^ n) hcard hfixed), Nat.gcd_comm]


include hn hcard hfixed hJ in
public theorem unitary_projective_commutator_torus (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : IsInvolution t)
    (htB : t ∉ normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
    IsCyclic (⁅twoPoint (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) t, zpowers t⁆ : Subgroup _) ∧
      Nat.card (⁅twoPoint (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) t, zpowers t⁆ : Subgroup _) = 2 ^ n - 1 ∧
      ∀ x ∈ ⁅twoPoint (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) t, zpowers t⁆,
        rightConjugateElem x t = x⁻¹ := by
  obtain ⟨T, hT, hc, hTcard⟩ := psu_invertedTorus_of_borel J n hn hcard hfixed hJ
    (unitary_projective_borel J hn hcard hfixed hJ P) t ht htB
  have ho : Odd (Nat.card T) := by
    rw [hTcard]
    exact Nat.Even.sub_odd (by exact Nat.one_le_pow n 2 (by decide)) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  rw [twoPoint_commutator_of_inverted _ T t ht hT ho]
  exact ⟨hc, hTcard, fun x hx => ((Set.ext_iff.mp hT x).mp hx).2.2⟩

include hn hcard hfixed hJ in
public theorem unitary_projective_fixed_torus (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : IsInvolution t)
    (htB : t ∉ normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
    IsCyclic (twoPoint (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) t ⊓
      centralizer ({t} : Set _) : Subgroup _) ∧
    Nat.card (twoPoint (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) t ⊓
      centralizer ({t} : Set _) : Subgroup _) = (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) := by
  let B := normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))
  let D := twoPoint B t
  obtain ⟨hcD, hcardD⟩ := unitary_projective_twoPoint_torus J hn hcard hfixed hJ P t ht htB
  let : IsCyclic D := hcD
  have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq (2 ^ n) 1
  have hdvd : Nat.gcd 3 (2 ^ n + 1) ∣ (2 ^ n) ^ 2 - 1 := by
    rw [hfac]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right 3 _) _
  have hoddD : Odd (Nat.card D) := by
    rw [hcardD]
    apply Odd.of_dvd_nat _ (Nat.div_dvd_of_dvd hdvd)
    apply Nat.Even.sub_odd (by exact Nat.one_le_pow 2 (2 ^ n) (Nat.one_le_pow n 2 (by decide))) _ odd_one
    have he : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    exact he.pow_of_ne_zero (by decide : 2 ≠ 0)
  obtain ⟨T, hT, _, hTc⟩ := psu_invertedTorus_of_borel J n hn hcard hfixed hJ
    (unitary_projective_borel J hn hcard hfixed hJ P) t ht htB
  have hm := card_fixed_mul_inverted D T t ht
    (inf_rightConjugate_mem_normalizer_of_isInvolution B ht) hoddD
    (fun x => (Set.ext_iff.mp hT x).trans and_assoc.symm)
  refine ⟨isCyclic_of_le (show D ⊓ centralizer ({t} : Set _) ≤ D from inf_le_left), ?_⟩
  have hq : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
  apply Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hq)
  calc
    _ = Nat.card D := by simpa only [hTc] using hm.symm
    _ = ((2 ^ n) ^ 2 - 1) / Nat.gcd 3 (2 ^ n + 1) := hcardD
    _ = _ := by rw [hfac, Nat.mul_div_assoc _ (Nat.gcd_dvd_right 3 _)]; exact Nat.mul_comm _ _



end BenderSuzuki.ZD.RankOneModelGeometry
