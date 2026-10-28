module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.Residual
public import Theory.SpecificGroups.PSL2.OuterSolvable.OddCoverage
public import Theory.SpecificGroups.GL2.DiagonalSwap
public import Theory.SpecificGroups.GL2.NoncommutativeCentralizer
public import Theory.GroupTheory.PerfectCentralCoverSylowRigidity
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The entire Sylow center centralizes the unitary involution residual

Let D be normal in a finite ambient group, with D isomorphic to the actual
PSU₃(q) for an odd prime q > 3. At an involution z of D in the ambient Sylow
center, the solvable residual R of C_D(z) is SL₂(q). It is normalized by C_J(z),
so it has a Sylow two-subgroup contained in the ambient Sylow subgroup.
Every element of its center therefore induces an automorphism of R fixing
that Sylow subgroup pointwise.

Such an automorphism of SL₂(q) is trivial. The genuine PSL₂ automorphism
classification, the absence of field automorphisms of ZMod q, and uniqueness
of lifts from a perfect central cover realize it by conjugation in GL₂(q).
Transfer places the nontrivial scalar involution in the Sylow commutator,
so that Sylow subgroup is noncommutative. Its GL₂ centralizer consists of
scalars, proving the required rigidity. This handles ambient elements outside
D as well as those inside it, without replacing a cyclic center by its involution.

The unitary-to-SL₂ comparison is the one in `UnitaryPosition.Residual`; it
retains the fixed-field order q, matrix-field order q², Frobenius conjugation,
and actual projective Hermitian form comparison. Cyclic-factor positioning
is a separate assertion. In fact, the centralization needs only normality
and the concrete model, without the remaining odd Cartan hypotheses.

Source: Aschbacher–Smith, A.3.15(3), printed pp.50–51, and the proof of 1.3.4,
printed pp.510–511. The rank-one automorphism input is GLS3, Theorem 2.5.12
and §2.7, as formalized in `Theory.PSL2.OuterSolvable.odd_semilinear_coverage`.
-/

public section
open Subgroup Matrix
open Theory.PSL2 Theory.PSL2.OuterSolvable
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition

private theorem sl2_sylow_noncommutative (q : ℕ) [Fact q.Prime]
    (hq : Odd q) (hlarge : 3 < q)
    (P : Sylow 2 (SpecialLinearGroup (Fin 2) (ZMod q))) : ¬ IsMulCommutative P := by
  intro hP
  let _ : Group.IsPerfect (SpecialLinearGroup (Fin 2) (ZMod q)) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod q) (by simpa using hlarge)
  have hcard : Nat.card (center (SpecialLinearGroup (Fin 2) (ZMod q))) = 2 := by
    simpa only [GorensteinWalter.sl2ProjectiveProjection_ker] using
      GorensteinWalter.sl2ProjectiveProjection_ker_card (ZMod q) (by simpa using hq)
  have hZP : center (SpecialLinearGroup (Fin 2) (ZMod q)) ≤ P :=
    (IsPGroup.of_card (p := 2) (n := 1) (by simpa using hcard)).le_sylow_of_normal P
  have hle := center_inf_commutator_inf_sylow_le_commutator P
  have hPP : ⁅(P : Subgroup (SpecialLinearGroup (Fin 2) (ZMod q))),
      (P : Subgroup (SpecialLinearGroup (Fin 2) (ZMod q)))⁆ = ⊥ :=
    commutator_self_eq_bot_iff.mpr hP
  rw [Group.IsPerfect.commutator_eq_top, inf_top_eq, inf_eq_left.mpr hZP, hPP] at hle
  have hZ : center (SpecialLinearGroup (Fin 2) (ZMod q)) = ⊥ := bot_unique hle
  simp [hZ] at hcard

private theorem diagonal_toGL {F : Type*} [Field F] (u : Fˣ)
    (x : SpecialLinearGroup (Fin 2) F) :
    SpecialLinearGroup.toGL (slDiagonal u x) =
      GeneralLinearGroup.diagonalPair F (u, 1) * SpecialLinearGroup.toGL x *
        (GeneralLinearGroup.diagonalPair F (u, 1))⁻¹ := by
  apply Units.ext
  change (slDiagonal u x).val = _
  rw [← map_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slDiagonal, GeneralLinearGroup.diagonalPair_val, Matrix.mul_apply,
      Fin.sum_univ_two, mul_comm, mul_left_comm, mul_assoc]

private theorem sl2_aut_linear (q : ℕ) [Fact q.Prime] (hlarge : 3 < q)
    (a : MulAut (SpecialLinearGroup (Fin 2) (ZMod q))) :
    ∃ A : GL (Fin 2) (ZMod q), ∀ x,
      SpecialLinearGroup.toGL (a x) = A * SpecialLinearGroup.toGL x * A⁻¹ := by
  let pi := quotientMap (ZMod q)
  let f : PerfectCentralCovering.Cover (SpecialLinearGroup (Fin 2) (ZMod q))
      (Theory.PSL2.Group (ZMod q)) :=
    { toMonoidHom := pi
      surjective := quotientMap_surjective _
      isPerfect := GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod q) (by simpa using hlarge)
      ker_le_center := (QuotientGroup.ker_mk' _).le }
  obtain ⟨b, hb⟩ := f.exists_descended_aut (by exact QuotientGroup.ker_mk' _) a
  obtain ⟨g, u, σ, hg⟩ := odd_semilinear_coverage
    (K := ZMod q) (by rw [ringChar.eq (ZMod q) q]; omega) (by simpa using hlarge) b
  have hσ : σ = 1 := Subsingleton.elim _ _
  rw [hσ, map_one, mul_one] at hg
  obtain ⟨g, rfl⟩ := quotientMap_surjective (ZMod q) g
  let a' := MulAut.conj g * slDiagonalAut u
  have ha : a = a' := by
    apply MulEquiv.toMonoidHom_injective
    let _ := f.isPerfect
    apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
      f.toMonoidHom f.ker_le_center
    ext x
    change pi (a x) = pi (g * slDiagonal u x * g⁻¹)
    rw [← hb, hg]
    change MulAut.conj (pi g) (diagonalAutHom u (pi x)) = _
    rw [diagonalAutHom_apply_quotientMap]
    simp only [MulAut.conj_apply, map_mul, map_inv]
    rfl
  refine ⟨SpecialLinearGroup.toGL g * GeneralLinearGroup.diagonalPair (ZMod q) (u, 1), ?_⟩
  intro x
  rw [ha]
  change SpecialLinearGroup.toGL (g * slDiagonal u x * g⁻¹) = _
  rw [map_mul, map_mul, map_inv, diagonal_toGL]
  group

private theorem sl2_aut_eq_one_of_fixes_sylow (q : ℕ) [Fact q.Prime]
    (hq : Odd q) (hlarge : 3 < q)
    (P : Sylow 2 (SpecialLinearGroup (Fin 2) (ZMod q)))
    (a : MulAut (SpecialLinearGroup (Fin 2) (ZMod q)))
    (ha : ∀ x ∈ P, a x = x) : a = 1 := by
  obtain ⟨A, hA⟩ := sl2_aut_linear q hlarge a
  let U := (P : Subgroup (SpecialLinearGroup (Fin 2) (ZMod q))).map SpecialLinearGroup.toGL
  have hU : ¬ IsMulCommutative U := by
    intro hU
    let _ := hU
    apply sl2_sylow_noncommutative q hq hlarge P
    let e := (P : Subgroup (SpecialLinearGroup (Fin 2) (ZMod q))).equivMapOfInjective
      SpecialLinearGroup.toGL SpecialLinearGroup.toGL_injective
    exact .of_comm fun x y => e.injective (by simp only [map_mul]; exact mul_comm' _ _)
  have hAC : A ∈ centralizer (U : Set (GL (Fin 2) (ZMod q))) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ((mul_inv_eq_iff_eq_mul).mp ((hA x).symm.trans (congrArg _ (ha x hx)))).symm
  obtain ⟨c, rfl⟩ := GeneralLinearGroup.centralizer_le_scalar_of_noncommutative U hU hAC
  apply MulEquiv.ext
  intro x
  apply SpecialLinearGroup.toGL_injective
  change SpecialLinearGroup.toGL (a x) = SpecialLinearGroup.toGL x
  rw [hA, GeneralLinearGroup.scalar_commute c _, mul_inv_cancel_right]

variable {J : Type*} [Group J]

private theorem centralizer_le_normalizer_involutionResidual
    (D : Subgroup J) [D.Normal] (z : D) :
    centralizer ({(z : J)} : Set J) ≤ normalizer (involutionResidual D z : Set J) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  let a := MulAut.conjNormal g (H := D)
  have haz : a z = z := by
    apply Subtype.ext
    exact (mul_inv_eq_iff_eq_mul).mpr (mem_centralizer_singleton_iff.mp hg)
  let C := centralizer ({z} : Set D)
  let ac : C →* C := (a.toMonoidHom.comp C.subtype).codRestrict C (by
    intro y
    apply mem_centralizer_singleton_iff.mpr
    change a y * z = z * a y
    rw [← haz, ← map_mul, ← map_mul]
    exact congrArg a (mem_centralizer_singleton_iff.mp y.property))
  obtain ⟨y, ⟨r, hr, rfl⟩, rfl⟩ := hx
  have hres : ac r ∈ solvableResidual C :=
    map_solvableResidual_le ac (mem_map_of_mem ac hr)
  exact ⟨ac r, ⟨ac r, hres, rfl⟩, rfl⟩

private theorem exists_sylow_in_normalized (S : Sylow 2 J) (R : Subgroup J)
    (hn : (S : Subgroup J) ≤ normalizer (R : Set J)) [Finite J] :
    ∃ P : Sylow 2 R, ∀ x ∈ P, (x : J) ∈ S := by
  let N := normalizer (R : Set J)
  let T := S.subtype hn
  obtain ⟨Q, hQ⟩ := T.exists_subgroupOf_eq_of_normal (R.subgroupOf N)
  let e : R.subgroupOf N ≃* R := subgroupOfEquivOfLe R.le_normalizer
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  rw [hQ] at hy
  exact hy

/-- The whole ambient Sylow center centralizes the residual at a central involution in PSU₃. -/
theorem involutionResidual_le_centralizer_centerImage [Finite J]
    (D : Subgroup J) [D.Normal] (S : Sylow 2 J)
    (q : ℕ) [Fact q.Prime] (hq : Odd q) (hlarge : 3 < q)
    (hmodel : ClassicalGroup.IsPSU D 3 q) (z : D) (hz : orderOf z = 2)
    (hzS : (z : J) ∈ centerImage (S : Subgroup J)) :
    involutionResidual D z ≤ centralizer (centerImage (S : Subgroup J) : Set J) := by
  let R := involutionResidual D z
  have hSC : (S : Subgroup J) ≤ centralizer ({(z : J)} : Set J) := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr
      ((le_centralizer_centerImage (S : Subgroup J) hs) z hzS).symm
  have hn := hSC.trans (centralizer_le_normalizer_involutionResidual D z)
  obtain ⟨P, hP⟩ := exists_sylow_in_normalized S R hn
  obtain ⟨e⟩ := involutionResidual_equiv D q hq hlarge hmodel z hz
  intro r hr s hs
  have hsS : s ∈ S := map_subtype_le _ hs
  let a := R.normalizerMonoidHom ⟨s, hn hsS⟩
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let b := MulAut.congr e a
  have hb : b = 1 := by
    apply sl2_aut_eq_one_of_fixes_sylow q hq hlarge Q b
    rintro x ⟨y, hy, rfl⟩
    change e (a (e.symm (e y))) = e y
    rw [e.symm_apply_apply]
    apply congrArg e
    apply Subtype.ext
    change s * (y : J) * s⁻¹ = (y : J)
    exact mul_inv_eq_iff_eq_mul.mpr
      (le_centralizer_centerImage (S : Subgroup J) (hP y hy) s hs)
  have ha : a = 1 := (MulAut.congr e).injective (hb.trans (map_one _).symm)
  have har := DFunLike.congr_fun ha (⟨r, hr⟩ : R)
  have he : s * r * s⁻¹ = r := congrArg Subtype.val har
  exact mul_inv_eq_iff_eq_mul.mp he

/-- The whole-center conclusion for the unitary case of the odd Cartan argument. -/
theorem caseThree_involutionResidual_le_centralizer_centerImage [Finite J]
    {κ : GroupClass} {D B K : Subgroup J} {S : Sylow 2 J} {p q : ℕ} [Fact q.Prime]
    (hA : AmbientInput κ D B S p)
    (hC : CaseThree D B (S : Subgroup J) K q .unitary .unitary)
    (_hB : ¬ IsCyclic B) (hlarge : 3 < q)
    (z : D) (hz : orderOf z = 2) (hzS : (z : J) ∈ centerImage (S : Subgroup J)) :
    involutionResidual D z ≤ centralizer (centerImage (S : Subgroup J) : Set J) := by
  let _ := hA.normal
  exact involutionResidual_le_centralizer_centerImage D S q hC.odd_characteristic
    hlarge hC.model z hz hzS

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition
