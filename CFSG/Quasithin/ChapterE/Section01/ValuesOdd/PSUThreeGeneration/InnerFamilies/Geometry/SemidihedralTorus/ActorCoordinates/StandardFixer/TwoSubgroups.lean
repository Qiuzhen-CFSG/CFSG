module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus.ActorCoordinates.StandardFixer.Coordinates
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Semilinear
public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.Torus
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.Coordinates
public import Theory.SpecificGroups.SU3.OuterSolvable
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.SemilinearReduction
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Simultaneous sign coordinates for diagonal semilinear two-subgroups

The three norm-one diagonal units and the coefficient-field automorphisms form
an actual finite semidirect cover of the diagonal semilinear automorphisms of
PSU₃. The cover acts through unitary conjugation and the literal PGL field map;
no faithfulness or scalar-kernel calculation is needed.

For a prime p congruent to 1 modulo 4, the subgroup with sign diagonal entries
is elementary abelian of exponent two and has odd index ((p + 1) / 2)³.
Lift a given two-subgroup using a Sylow subgroup of its preimage, extend it to
a Sylow subgroup of the cover, and use Sylow conjugacy once. Mapping this single
conjugator to PSU₃ automorphisms proves the normalization premise of
`standardFixerCoordinates_of_diagonal_normalization`.

This is the diagonal-coordinate calculation used in Aschbacher--Smith E.1.14(7),
printed p.214, and A.3.21(a)--(b), printed p.55; see also Aschbacher (1982),
Lemma 4.11. Automorphism coverage and final standard-fixer assembly are supplied
separately by the enclosing `StandardFixer` module.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open BenderSuzuki.External
open BenderSuzuki.MatrixGroups.HermitianForm.EvenInner
open scoped Pointwise

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus.StandardFixer

variable {F : Type*} [Field F] [Finite F]

private def normOneAut (J : HermitianForm 3 F) (σ : F ≃+* F) : normOne J ≃* normOne J where
  toFun k := ⟨Units.map σ.toMonoidHom k.1, by
    have hc : J.conj (σ (k.1 : F)) = σ (J.conj (k.1 : F)) := by
      let := BenderSuzuki.MatrixGroups.HermitianForm.finiteFieldAut_isCyclic (E := F)
      let := IsCyclic.commGroup (α := F ≃+* F)
      exact congrArg (fun f : F ≃+* F => f (k.1 : F)) (Commute.all J.conj σ).eq
    change J.conj (σ (k.1 : F)) = (σ (k.1 : F))⁻¹
    rw [hc, k.2, map_inv₀]
  ⟩
  invFun k := ⟨Units.map σ.symm.toMonoidHom k.1, by
    have hc : J.conj (σ.symm (k.1 : F)) = σ.symm (J.conj (k.1 : F)) := by
      let := BenderSuzuki.MatrixGroups.HermitianForm.finiteFieldAut_isCyclic (E := F)
      let := IsCyclic.commGroup (α := F ≃+* F)
      exact congrArg (fun f : F ≃+* F => f (k.1 : F)) (Commute.all J.conj σ.symm).eq
    change J.conj (σ.symm (k.1 : F)) = (σ.symm (k.1 : F))⁻¹
    rw [hc, k.2, map_inv₀]
  ⟩
  left_inv k := by apply Subtype.ext; exact Units.ext (σ.symm_apply_apply _)
  right_inv k := by apply Subtype.ext; exact Units.ext (σ.apply_symm_apply _)
  map_mul' x y := by apply Subtype.ext; exact Units.ext (map_mul σ _ _)
private def fieldD (J : HermitianForm 3 F) (σ : F ≃+* F) : MulAut (Fin 3 → normOne J) :=
  MulEquiv.piCongrRight (fun _ => normOneAut J σ)
private def fieldDHom (J : HermitianForm 3 F) : (F ≃+* F) →* MulAut (Fin 3 → normOne J) where
  toFun := fieldD J
  map_one' := by
    ext d i
    rfl
  map_mul' σ τ := by
    ext d i
    rfl

private def diagonalUnitary' (J : HermitianForm 3 F) (hJ : J.form = 1)
    (d : Fin 3 → normOne J) : J.unitarySubgroup :=
  ⟨UnitaryThree.OddTorusNormalizer.diagonalHom (fun i => (d i : Fˣ)), by
    apply (CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus.StandardFixer.diagonal_mem_unitary J hJ _).2
    intro i
    exact (d i).property ▸ (by simp)⟩

private def diagHom (J : HermitianForm 3 F) (hJ : J.form = 1) :
    (Fin 3 → normOne J) →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (BenderSuzuki.MatrixGroups.HermitianForm.unitaryConjHom J).comp {
    toFun := diagonalUnitary' J hJ
    map_one' := by apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [diagonalUnitary', UnitaryThree.OddTorusNormalizer.diagonalHom]
    map_mul' x y := by apply Subtype.ext; apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [diagonalUnitary', UnitaryThree.OddTorusNormalizer.diagonalHom]
  }

omit [Finite F] in
private theorem diagHom_apply (J : HermitianForm 3 F) (hJ : J.form = 1)
    (d : Fin 3 → normOne J) :
    diagHom J hJ d = J.unitaryConj (diagonalUnitary' J hJ d) := by
  change J.unitaryConjHom (diagonalUnitary' J hJ d) = _
  exact J.unitaryConjHom_apply _

private theorem field_special_mem (J : HermitianForm 3 F) (hJ : J.form = 1)
    (σ : F ≃+* F) (x : J.specialSubgroup) :
    GeneralLinearGroup.map σ.toRingHom x.val ∈ J.specialSubgroup := by
  obtain ⟨hx, hd⟩ := (J.mem_specialSubgroup_iff x.val).mp x.property
  apply (J.mem_specialSubgroup_iff _).mpr
  constructor
  · have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M.map σ) hx
    have ht : (J.conjTranspose x.val.val).map σ = J.conjTranspose (x.val.val.map σ) := by
      ext i j
      change σ (J.conj (x.val.val j i)) = J.conj (σ (x.val.val j i))
      exact BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.SemilinearActors.field_conj_commute J σ _
    have hf : J.form.map σ = J.form := by rw [hJ]; ext i j; fin_cases i <;> fin_cases j <;> simp
    change J.conjTranspose (x.val.val.map σ) * J.form * x.val.val.map σ = J.form
    simpa only [Matrix.map_mul, ht, hf] using h
  · apply Units.ext
    change (σ.mapMatrix x.val.val).det = 1
    rw [← RingEquiv.map_det]
    have hd' : x.val.val.det = 1 := congrArg Units.val hd
    rw [hd', map_one]

private def fieldMap (J : HermitianForm 3 F) (hJ : J.form = 1) (σ : F ≃+* F) :
    ProjectiveSpecialUnitaryMatrixGroup J →* ProjectiveSpecialUnitaryMatrixGroup J :=
  ((ProjGenLinGroup.map σ.toRingHom).comp
    (ProjectiveSpecialUnitaryMatrixGroup J).subtype).codRestrict _ (by
      intro b
      obtain ⟨x, rfl⟩ := J.specialToProjective_surjective b
      change ProjGenLinGroup.map σ.toRingHom (J.specialToProjective x).val ∈ _
      rw [J.specialToProjective_apply_val, ProjGenLinGroup.map_mk]
      exact Subgroup.mem_map_of_mem _ (field_special_mem J hJ σ x))

private def fieldActor (J : HermitianForm 3 F) (hJ : J.form = 1) (σ : F ≃+* F) :
    MulAut (ProjectiveSpecialUnitaryMatrixGroup J) where
  toFun := fieldMap J hJ σ
  invFun := fieldMap J hJ σ.symm
  left_inv x := by
    apply Subtype.ext
    obtain ⟨g, hg⟩ := ProjGenLinGroup.mk_surjective x.val
    change ProjGenLinGroup.map σ.symm.toRingHom (ProjGenLinGroup.map σ.toRingHom x.val) = x.val
    rw [← hg, ProjGenLinGroup.map_mk, ProjGenLinGroup.map_mk]
    congr 1; apply Units.ext; ext i j; exact σ.symm_apply_apply _
  right_inv x := by
    apply Subtype.ext
    obtain ⟨g, hg⟩ := ProjGenLinGroup.mk_surjective x.val
    change ProjGenLinGroup.map σ.toRingHom (ProjGenLinGroup.map σ.symm.toRingHom x.val) = x.val
    rw [← hg, ProjGenLinGroup.map_mk, ProjGenLinGroup.map_mk]
    congr 1; apply Units.ext; ext i j; exact σ.apply_symm_apply _
  map_mul' := (fieldMap J hJ σ).map_mul

private def fieldHom (J : HermitianForm 3 F) (hJ : J.form = 1) :
    (F ≃+* F) →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) where
  toFun := fieldActor J hJ
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change ProjGenLinGroup.map (RingHom.id F) x.val = x.val
    simp [ProjGenLinGroup.map_id]
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change ProjGenLinGroup.map (σ.toRingHom.comp τ.toRingHom) x.val =
      ProjGenLinGroup.map σ.toRingHom (ProjGenLinGroup.map τ.toRingHom x.val)
    rw [ProjGenLinGroup.map_comp]
    rfl

@[simp] private theorem fieldActor_apply_val (J : HermitianForm 3 F) (hJ : J.form = 1)
    (σ : F ≃+* F) (x : ProjectiveSpecialUnitaryMatrixGroup J) :
    (fieldActor J hJ σ x).val = ProjGenLinGroup.map σ.toRingHom x.val := by rfl

private theorem diagonal_map (J : HermitianForm 3 F) (σ : F ≃+* F)
    (d : Fin 3 → normOne J) :
    GeneralLinearGroup.map σ.toRingHom
      (UnitaryThree.OddTorusNormalizer.diagonalHom (fun i => (d i : Fˣ))) =
      UnitaryThree.OddTorusNormalizer.diagonalHom
        (fun i => ((fieldD J σ d i : normOne J) : Fˣ)) := by
  apply Units.ext
  ext i j
  by_cases hij : i = j
  · subst j
    simp [UnitaryThree.OddTorusNormalizer.diagonalHom, fieldD, normOneAut]
  · simp [UnitaryThree.OddTorusNormalizer.diagonalHom, hij]

private theorem covariance (J : HermitianForm 3 F) (hJ : J.form = 1)
    (σ : F ≃+* F) (d : Fin 3 → normOne J) :
    diagHom J hJ (fieldD J σ d) =
      fieldHom J hJ σ * diagHom J hJ d * (fieldHom J hJ σ)⁻¹ := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  simp only [diagHom_apply]
  change (J.unitaryConj (diagonalUnitary' J hJ (fieldD J σ d)) x).val =
    ((fieldActor J hJ σ) ((J.unitaryConj (diagonalUnitary' J hJ d))
      ((fieldActor J hJ σ)⁻¹ x))).val
  rw [J.unitaryConj_apply_val, fieldActor_apply_val]
  rw [J.unitaryConj_apply_val]
  have hxin : ((fieldActor J hJ σ)⁻¹ x).val =
      ProjGenLinGroup.map σ.symm.toRingHom x.val := by
    change ProjGenLinGroup.map σ.symm.toRingHom x.val = _
    rfl
  rw [hxin]
  simp only [map_mul, map_inv, ProjGenLinGroup.map_mk]
  have hdu : GeneralLinearGroup.map σ.toRingHom (diagonalUnitary' J hJ d).val =
      (diagonalUnitary' J hJ (fieldD J σ d)).val := by
    dsimp [diagonalUnitary']
    exact diagonal_map J σ d
  rw [hdu]
  have hcomp : ProjGenLinGroup.map σ.toRingHom
      (ProjGenLinGroup.map σ.symm.toRingHom x.val) = x.val := by
    obtain ⟨g, hg⟩ := ProjGenLinGroup.mk_surjective x.val
    rw [← hg, ProjGenLinGroup.map_mk, ProjGenLinGroup.map_mk]
    congr 1
    apply Units.ext
    ext i j
    exact σ.apply_symm_apply _
  rw [hcomp]

private def coverHom (J : HermitianForm 3 F) (hJ : J.form = 1) :
    (Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F) →*
      MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
  SemidirectProduct.lift (diagHom J hJ) (fieldHom J hJ) (by
    intro σ
    apply MonoidHom.ext
    intro d
    exact covariance J hJ σ d)

private theorem coverHom_apply (J : HermitianForm 3 F) (hJ : J.form = 1)
    (d : Fin 3 → normOne J) (σ : F ≃+* F) (x : ProjectiveSpecialUnitaryMatrixGroup J) :
    coverHom J hJ ⟨d, σ⟩ x =
      (diagHom J hJ d) ((fieldHom J hJ σ) x) := by
  have he : (⟨d, σ⟩ : (Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F)) =
      SemidirectProduct.inl d * SemidirectProduct.inr σ := by
    apply SemidirectProduct.ext
    · rw [SemidirectProduct.mul_def]
      simp
    · simp
  rw [he, map_mul]
  change ((SemidirectProduct.lift (diagHom J hJ) (fieldHom J hJ) _) (SemidirectProduct.inl d) *
      (SemidirectProduct.lift (diagHom J hJ) (fieldHom J hJ) _) (SemidirectProduct.inr σ)) x = _
  rw [SemidirectProduct.lift_inl, SemidirectProduct.lift_inr, MulAut.mul_apply]

private def dTwo (J : HermitianForm 3 F) : Subgroup (Fin 3 → normOne J) where
  carrier := {d | ∀ i, d i ^ 2 = 1}
  one_mem' := by intro i; simp
  mul_mem' := by
    intro a b ha hb i
    rw [Pi.mul_apply, mul_pow, ha i, hb i]
    simp
  inv_mem' := by
    intro a ha i
    rw [Pi.inv_apply, inv_pow, ha i, inv_one]

private theorem fieldD_mem_dTwo (J : HermitianForm 3 F) (σ : F ≃+* F)
    {d : Fin 3 → normOne J} (hd : d ∈ dTwo J) : fieldD J σ d ∈ dTwo J := by
  intro i
  change (normOneAut J σ (d i)) ^ 2 = 1
  apply Subtype.ext
  apply Units.ext
  change (σ ((d i : normOne J) : Fˣ)) ^ 2 = 1
  rw [← map_pow]
  have hpow : (((d i : normOne J) : Fˣ) : F) ^ 2 = 1 := by
    exact congrArg (fun z : normOne J => (((z : Fˣ) : F))) (by simpa using hd i)
  simpa using congrArg σ hpow

private def K (J : HermitianForm 3 F) (_hJ : J.form = 1) :
    Subgroup ((Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F)) where
  carrier := {x | x.left ∈ dTwo J}
  one_mem' := by simp [dTwo]
  mul_mem' := by
    intro x y hx hy i
    rw [SemidirectProduct.mul_def]
    change (x.left i * (fieldD J x.right y.left) i) ^ 2 = 1
    rw [mul_pow, hx i, one_mul]
    exact fieldD_mem_dTwo J x.right hy i
  inv_mem' := by
    intro x hx i
    change ((fieldD J x.right.symm x.left⁻¹) i) ^ 2 = 1
    have hx' : x.left⁻¹ ∈ dTwo J := (dTwo J).inv_mem hx
    exact fieldD_mem_dTwo J x.right.symm hx' i

private def oneTwo (J : HermitianForm 3 F) : Subgroup (normOne J) := (powMonoidHom 2).ker
private def dTwoEquiv (J : HermitianForm 3 F) : dTwo J ≃ (Fin 3 → oneTwo J) where
  toFun d := fun i => ⟨d.1 i, by
    change d.1 i ^ 2 = 1
    exact d.2 i⟩
  invFun e := ⟨fun i => e i, by
    intro i
    exact (e i).property⟩
  left_inv d := by ext i; rfl
  right_inv e := by ext i; rfl

private theorem oneTwo_card (J : HermitianForm 3 F) {p : ℕ} (_hp : p.Prime)
    (ho : Odd p) (hcard : Nat.card F = p ^ 2) (hmod : p % 4 = 1)
    (hc : ∀ x, J.conj x = x ^ p) :
    Nat.card (oneTwo J) = 2 := by
  change Nat.card ((powMonoidHom 2).ker : Subgroup (normOne J)) = 2
  rw [IsCyclic.card_powMonoidHom_ker, normOne_card J hcard hc]
  have hdiv : 2 ∣ p + 1 := by
    rcases ho with ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩
  rw [Nat.gcd_eq_right hdiv]

private theorem dTwo_card (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime)
    (ho : Odd p) (hcard : Nat.card F = p ^ 2) (hmod : p % 4 = 1)
    (hc : ∀ x, J.conj x = x ^ p) :
    Nat.card (dTwo J) = 8 := by
  rw [Nat.card_congr (dTwoEquiv J), Nat.card_fun, oneTwo_card J hp ho hcard hmod hc]
  norm_num [Nat.card_fin]

private def KEquiv (J : HermitianForm 3 F) (hJ : J.form = 1) :
    K J hJ ≃ dTwo J × (F ≃+* F) where
  toFun x := ⟨⟨x.1.left, x.2⟩, x.1.right⟩
  invFun x := ⟨⟨x.1, x.2⟩, x.1.2⟩
  left_inv x := by rfl
  right_inv x := by rfl

private theorem K_card (J : HermitianForm 3 F) (hJ : J.form = 1) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hcard : Nat.card F = p ^ 2)
    (hmod : p % 4 = 1) (hc : ∀ x, J.conj x = x ^ p) :
    Nat.card (K J hJ) = 8 * Nat.card (F ≃+* F) := by
  rw [Nat.card_congr (KEquiv J hJ), Nat.card_prod, dTwo_card J hp ho hcard hmod hc]

private theorem H_card (J : HermitianForm 3 F) {p : ℕ}
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p) :
    Nat.card ((Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F)) =
      (p + 1) ^ 3 * Nat.card (F ≃+* F) := by
  rw [Nat.card_congr (SemidirectProduct.equivProd), Nat.card_prod, Nat.card_fun,
    Nat.card_fin, normOne_card J hcard hc]

private theorem K_index (J : HermitianForm 3 F) (hJ : J.form = 1) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hcard : Nat.card F = p ^ 2)
    (hmod : p % 4 = 1) (hc : ∀ x, J.conj x = x ^ p) :
    (K J hJ).index = ((p + 1) / 2) ^ 3 := by
  have hmul := Subgroup.index_mul_card (K J hJ)
  rw [K_card J hJ hp ho hcard hmod hc, H_card J hcard hc] at hmul
  let _ : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => σ.toFun)
    (fun σ τ h => by apply RingEquiv.ext; intro x; exact congrFun h x)
  let _ : Nonempty (F ≃+* F) := ⟨RingEquiv.refl F⟩
  have hA : 0 < Nat.card (F ≃+* F) := Nat.card_pos
  have heq : (K J hJ).index * 8 = (p + 1) ^ 3 := by
    apply Nat.mul_right_cancel hA
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  have hdiv : 2 ∣ p + 1 := by
    rcases ho with ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩
  have hplus : p + 1 = 2 * ((p + 1) / 2) := by
    rw [Nat.mul_comm, Nat.div_mul_cancel hdiv]
  apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 8)
  calc
    8 * (K J hJ).index = (K J hJ).index * 8 := by ring
    _ = (p + 1) ^ 3 := heq
    _ = (2 * ((p + 1) / 2)) ^ 3 := by exact congrArg (fun n : ℕ => n ^ 3) hplus
    _ = 8 * ((p + 1) / 2) ^ 3 := by ring

private theorem K_not_two_dvd (J : HermitianForm 3 F) (hJ : J.form = 1) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hcard : Nat.card F = p ^ 2)
    (hmod : p % 4 = 1) (hc : ∀ x, J.conj x = x ^ p) :
    ¬ 2 ∣ (K J hJ).index := by
  rw [K_index J hJ hp ho hcard hmod hc]
  intro hd
  have h4 := Nat.mod_add_div (p + 1) 4
  have h2 := Nat.mod_add_div (p + 1) 2
  have hq : Odd ((p + 1) / 2) := by
    refine ⟨(p + 1) / 4, ?_⟩
    omega
  have hne : ¬ Even (((p + 1) / 2) ^ 3) := Nat.not_even_iff_odd.mpr hq.pow
  exact hne (even_iff_two_dvd.mpr hd)

private theorem coverHom_of_diagonal
    (J : HermitianForm 3 F) (hJ : J.form = 1)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : HasDiagonalSemilinearForm J a) :
    ∃ h : (Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F), coverHom J hJ h = a := by
  obtain ⟨d, σ, hd, hσ, ha⟩ := ha
  let d₀ : Fin 3 → normOne J := fun i =>
    ⟨d i, by
      change J.conj (d i : F) = (d i : F)⁻¹
      exact eq_inv_of_mul_eq_one_left (hd i)⟩
  refine ⟨⟨d₀, σ⟩, ?_⟩
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [coverHom_apply]
  simp only [diagHom_apply]
  change (J.unitaryConj (diagonalUnitary' J hJ d₀)
      ((fieldActor J hJ σ) x)).val = (a x).val
  rw [J.unitaryConj_apply_val, fieldActor_apply_val]
  rw [ha]
  congr 1

private def Hpre (J : HermitianForm 3 F) (hJ : J.form = 1)
    (U : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) :
    Subgroup ((Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F)) :=
  U.comap (coverHom J hJ)

private def fU (J : HermitianForm 3 F) (hJ : J.form = 1)
    (U : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) :
    Hpre J hJ U →* U where
  toFun h := ⟨coverHom J hJ h.1, h.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by ext; simp

private theorem fU_surjective
    (J : HermitianForm 3 F) (hJ : J.form = 1)
    (U : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hdiag : ∀ a ∈ U, HasDiagonalSemilinearForm J a) :
    Function.Surjective (fU J hJ U) := by
  intro a
  obtain ⟨h, hh⟩ := coverHom_of_diagonal J hJ a (hdiag a a.property)
  have hm : coverHom J hJ h ∈ U := by rw [hh]; exact a.property
  exact ⟨⟨h, hm⟩, by exact Subtype.ext hh⟩

private theorem fieldD_eq_self_of_dTwo (J : HermitianForm 3 F) (_h2 : (2 : F) ≠ 0)
    (σ : F ≃+* F) {d : Fin 3 → normOne J} (hd : d ∈ dTwo J) :
    fieldD J σ d = d := by
  apply funext
  intro i
  apply Subtype.ext
  apply Units.ext
  change σ (((d i : normOne J) : Fˣ) : F) = (((d i : normOne J) : Fˣ) : F)
  have hsq : (((d i : normOne J) : Fˣ) : F) ^ 2 = 1 := by
    exact congrArg (fun z : normOne J => (((z : Fˣ) : F))) (by simpa using hd i)
  obtain h | h := sq_eq_one_iff.mp hsq
  · rw [h]; simp
  · rw [h]; simp

private theorem field_aut_cases (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (σ : F ≃+* F) : σ = 1 ∨ σ = J.conj := by
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  exact BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.fieldAut_eq_one_or_conj
    J hp hcard (J.card_fixed_of_prime_frobenius hc) σ

private theorem K_isPGroup (J : HermitianForm 3 F) (hJ : J.form = 1) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hcard : Nat.card F = p ^ 2)
    (_hmod : p % 4 = 1) (hc : ∀ x, J.conj x = x ^ p) :
    IsPGroup 2 (K J hJ) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : F) ≠ 0 := Field.two_ne_zero_of_odd_card F (by
    rw [hcard]; exact ho.pow)
  rw [IsPGroup.iff_orderOf]
  intro x
  have hfix : fieldD J x.1.right x.1.left = x.1.left :=
    fieldD_eq_self_of_dTwo J h2 _ x.2
  have hσ := field_aut_cases J hp hcard hc x.1.right
  have hsq : x ^ 2 = 1 := by
    apply Subtype.ext
    change (x.1) ^ 2 = (1 : (Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F))
    rw [pow_two]
    apply SemidirectProduct.ext
    · change x.1.left * (fieldD J x.1.right x.1.left) = 1
      rw [hfix]
      apply funext
      intro i
      simpa [Pi.mul_apply, pow_two] using x.2 i
    · change x.1.right * x.1.right = 1
      rcases hσ with hσ | hσ
      · rw [hσ]; simp
      · rw [hσ, show J.conj * J.conj = 1 by
          apply RingEquiv.ext; intro z; exact J.conj_involutive z]
  by_cases hx : x = 1
  · exact ⟨0, by rw [orderOf_eq_one_iff.mpr hx]; norm_num⟩
  · exact ⟨1, by rw [orderOf_eq_prime hsq hx]; norm_num⟩

private theorem exists_sylow_conjugator
    (J : HermitianForm 3 F) (hJ : J.form = 1) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hcard : Nat.card F = p ^ 2)
    (hmod : p % 4 = 1) (hc : ∀ x, J.conj x = x ^ p)
    (U : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hU : IsPGroup 2 U)
    (hdiag : ∀ a ∈ U, HasDiagonalSemilinearForm J a) :
    ∃ (g : (Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F))
      (Q : Sylow 2 (Hpre J hJ U)),
      (∀ (a) (ha : a ∈ U), ∃ q ∈ Q, fU J hJ U q = ⟨a, ha⟩) ∧
      ∀ x ∈ (Q : Subgroup (Hpre J hJ U)).map (Hpre J hJ U).subtype,
        g * x * g⁻¹ ∈ K J hJ := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => σ.toFun)
    (fun σ τ h => by apply RingEquiv.ext; intro x; exact congrFun h x)
  let _ : Finite ((Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F)) :=
    Finite.of_injective (fun x => (x.left, x.right)) (by intro x y h; cases x; cases y; simp_all)
  let _ : Finite (Hpre J hJ U) := Finite.of_injective (fun x => x.1) Subtype.val_injective
  let f := fU J hJ U
  have hf : Function.Surjective f := fU_surjective J hJ U hdiag
  let htop : IsPGroup 2 (⊤ : Subgroup U) := hU.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup U) ≃* U).symm
  let PU : Sylow 2 U := htop.toSylow (by simp)
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective hf 2 PU
  let QH : Subgroup ((Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F)) := (Q : Subgroup (Hpre J hJ U)).map (Hpre J hJ U).subtype
  have hQH : IsPGroup 2 QH := Q.isPGroup'.map (Hpre J hJ U).subtype
  obtain ⟨S, hS⟩ := hQH.exists_le_sylow
  let S₀ : Sylow 2 ((Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F)) := (K_isPGroup J hJ hp ho hcard hmod hc).toSylow
    (K_not_two_dvd J hJ hp ho hcard hmod hc)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ((Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F)) S S₀
  have hpre : ∀ (a) (ha : a ∈ U), ∃ q ∈ Q, fU J hJ U q = ⟨a, ha⟩ := by
    intro a ha
    have haPU : (⟨a, ha⟩ : U) ∈ (PU : Subgroup U) := by
      rw [show (PU : Subgroup U) = ⊤ by simp [PU]]
      trivial
    have hm : (⟨a, ha⟩ : U) ∈ (Sylow.mapSurjective hf Q : Subgroup U) := by
      rw [hQ]
      exact haPU
    change (⟨a, ha⟩ : U) ∈ (Q : Subgroup (Hpre J hJ U)).map (fU J hJ U)
      at hm
    rcases hm with ⟨q, hq, hqa⟩
    exact ⟨q, hq, hqa⟩
  refine ⟨g, Q, hpre, ?_⟩
  intro x hx
  have hxS : x ∈ (S : Subgroup ((Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F))) := hS hx
  have hx' : (MulAut.conj (G := (Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F)) g) x ∈
      (MulAut.conj (G := (Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F)) g) •
      (S : Subgroup ((Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F))) :=
    Subgroup.smul_mem_pointwise_smul x
      (MulAut.conj (G := (Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F)) g)
      (S : Subgroup ((Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F))) hxS
  have hx'' : (MulAut.conj g) x ∈ ((g • S : Sylow 2 ((Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F))) : Subgroup ((Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F))) := by
    rw [Sylow.coe_subgroup_smul]
    exact hx'
  rw [hg] at hx''
  exact hx''

omit [Finite F] in
private theorem sign_coefficients
    (J : HermitianForm 3 F) (h2 : (2 : F) ≠ 0)
    {d : Fin 3 → normOne J} (hd : d ∈ dTwo J) :
    ∃ ε : Fin 3 → Bool, ∀ i, (d i : Fˣ) = if ε i then -1 else 1 := by
  classical
  let ε : Fin 3 → Bool := fun i =>
    if h : d i = 1 then false else true
  refine ⟨ε, ?_⟩
  intro i
  have hsq : (((d i : normOne J) : Fˣ) : F) ^ 2 = 1 := by
    exact congrArg (fun z : normOne J => (((z : Fˣ) : F))) (by simpa using hd i)
  obtain h | h := sq_eq_one_iff.mp hsq
  · have hu : (d i : Fˣ) = 1 := by apply Units.ext; exact h
    by_cases h1 : d i = 1
    · simp [ε, h1]
    · have hd1 : d i = 1 := by apply Subtype.ext; apply Units.ext; exact h
      exact (h1 hd1).elim
  · have hu : (d i : Fˣ) = -1 := by apply Units.ext; exact h
    by_cases h1 : d i = 1
    · exfalso
      apply h2
      have h1F : (((d i : normOne J) : Fˣ) : F) = 1 := by rw [h1]; simp
      linear_combination h1F.symm.trans h
    · simpa [ε, h1] using hu

private theorem coverHom_sign_of_K
    (J : HermitianForm 3 F) (hJ : J.form = 1)
    (r : (Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F))
    (h2 : (2 : F) ≠ 0) (hr : r ∈ K J hJ) (hσ : r.right = 1 ∨ r.right = J.conj) :
    HasSignSemilinearForm J (coverHom J hJ r) := by
  obtain ⟨ε, hε⟩ := sign_coefficients J h2 hr
  refine ⟨ε, r.right, hσ, ?_⟩
  intro x
  rw [coverHom_apply]
  simp only [diagHom_apply]
  change (J.unitaryConj (diagonalUnitary' J hJ r.left)
      ((fieldActor J hJ r.right) x)).val = _
  rw [J.unitaryConj_apply_val, fieldActor_apply_val]
  have hmat :
      UnitaryThree.OddTorusNormalizer.diagonalHom
          (fun i => ((r.left i : normOne J) : Fˣ)) = signGL ε := by
    apply Units.ext
    ext i j
    by_cases hij : i = j
    · subst j
      simp [signGL, UnitaryThree.OddTorusNormalizer.diagonalHom, hε]
    · simp [signGL, UnitaryThree.OddTorusNormalizer.diagonalHom, hij]
  have hmat' : (diagonalUnitary' J hJ r.left).val = signGL ε := by
    dsimp [diagonalUnitary']
    exact hmat
  have hmk : ProjGenLinGroup.mk (diagonalUnitary' J hJ r.left).val =
      ProjGenLinGroup.mk (signGL ε) := congrArg ProjGenLinGroup.mk hmat'
  rw [hmk]

private theorem coverHom_diagonal
    (J : HermitianForm 3 F) (hJ : J.form = 1)
    (g : (Fin 3 → normOne J) ⋊[fieldDHom J] (F ≃+* F))
    (hσ : g.right = 1 ∨ g.right = J.conj) :
    HasDiagonalSemilinearForm J (coverHom J hJ g) := by
  refine ⟨fun i => (g.left i : Fˣ), g.right, ?_, hσ, ?_⟩
  · intro i
    rw [(g.left i).property]
    simp
  · intro x
    rw [coverHom_apply]
    simp only [diagHom_apply]
    change (J.unitaryConj (diagonalUnitary' J hJ g.left)
      ((fieldActor J hJ g.right) x)).val = _
    rw [J.unitaryConj_apply_val, fieldActor_apply_val]
    rfl

/-- One diagonal semilinear conjugator simultaneously puts every member of a
finite two-subgroup into the literal sign-and-Frobenius coordinates. -/
theorem exists_sign_conjugator_of_diagonal
    (J : HermitianForm 3 F) (hJ : J.form = 1) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hmod : p % 4 = 1)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (U : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hU : IsPGroup 2 U)
    (hdiag : ∀ a ∈ U, HasDiagonalSemilinearForm J a) :
    ∃ c : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      HasDiagonalSemilinearForm J c ∧
      ∀ a ∈ U, HasSignSemilinearForm J (MulAut.congr c a) := by
  obtain ⟨g, Q, hpre, hg⟩ := exists_sylow_conjugator J hJ hp ho hcard hmod hc U hU hdiag
  refine ⟨coverHom J hJ g, coverHom_diagonal J hJ g (field_aut_cases J hp hcard hc g.right), ?_⟩
  intro a ha
  obtain ⟨q, hq, hqa⟩ := hpre a ha
  have hqa' : coverHom J hJ q.val = a := congrArg Subtype.val hqa
  have hqmap : q.val ∈ (Q : Subgroup (Hpre J hJ U)).map (Hpre J hJ U).subtype :=
    Subgroup.mem_map_of_mem _ hq
  have h2 : (2 : F) ≠ 0 := Field.two_ne_zero_of_odd_card F (by rw [hcard]; exact ho.pow)
  have hs := coverHom_sign_of_K J hJ (g * q.val * g⁻¹) h2 (hg q.val hqmap)
    (field_aut_cases J hp hcard hc _)
  have he : coverHom J hJ (g * q.val * g⁻¹) = MulAut.congr (coverHom J hJ g) a := by
    rw [map_mul, map_mul, map_inv, hqa']
    rfl
  rwa [he] at hs

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus.StandardFixer
