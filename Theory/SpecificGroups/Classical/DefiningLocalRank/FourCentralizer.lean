module
public import Theory.Representation.DefiningCentralizerDegreeThree
public import Theory.SpecificGroups.OddThreeRank
public import Theory.Quasithin.Rank

/-!
# Four-group centralizers in the actual projective degree-three models

Lift the four-group and its full centralizer through the central odd kernel.
The determinant-one character-line calculation excludes defining-prime torsion
in the covering centralizer. Thus the actual projective centralizer has order
coprime to the defining prime. Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Module Subgroup
namespace Theory.SpecificGroups.DefiningLocalRank
open Matrix Representation
open scoped MatrixGroups

/-- A projective quotient of a faithful special degree-three matrix group
has defining-prime-free four-group centralizers. The quotient is the actual
surjection with a central kernel of odd order. -/
theorem not_dvd_card_four_centralizer_of_cover
    {F R Q : Type*} [Field F] [Group R] [Finite R] [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime] [CharP F p] (h2 : (2 : F) ≠ 0)
    (j : R →* GL (Fin 3) F) (hj : Function.Injective j)
    (hdet : ∀ x, GeneralLinearGroup.det (j x) = 1)
    (f : R →* Q) (hf : Function.Surjective f) (hcent : f.ker ≤ center R)
    (hodd : Nat.Coprime 2 (Nat.card f.ker))
    (B : Subgroup Q) (hB : IsElementaryAbelian 2 B) (hB4 : Nat.card B = 4) :
    ¬ p ∣ Nat.card (centralizer (B : Set Q)) := by
  let : IsElementaryAbelian 2 B := hB
  obtain ⟨A,_,hmap,_,hcentral,hinj⟩ :=
    B.exists_prime_lift_of_central_coprime f hf hcent hodd
      (IsElementaryAbelian.isPGroup 2 B)
  let fA := f.comp A.subtype
  let g : A →* B := fA.codRestrict B (fun x => by
    rw [← hmap]
    exact mem_map_of_mem f x.property)
  have hgi : Function.Injective g := fun x y hh => hinj (congrArg Subtype.val hh)
  have hgs : Function.Surjective g := by
    intro y
    obtain ⟨x,hx,he⟩ := show (y : Q) ∈ A.map f from hmap.symm ▸ y.property
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let eA : A ≃* B := MulEquiv.ofBijective g ⟨hgi,hgs⟩
  let : IsMulCommutative A := IsMulCommutative.of_comm (fun x y => by
    apply hgi
    rw [map_mul,map_mul]
    exact hB.toIsMulCommutative.is_comm.comm _ _)
  have hA4 : Nat.card A = 4 := (Nat.card_congr eA.toEquiv).trans hB4
  have hn : ¬ IsCyclic A := by
    intro hc
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq
      (p := 2) (by simpa using hB4) (eA.isCyclic.mp hc)
  let E := AlgebraicClosure F
  let fE : GL (Fin 3) F →* GL (Fin 3) E := GeneralLinearGroup.map (algebraMap F E)
  have hfE : Function.Injective fE := by
    intro a b hh
    apply Units.ext
    ext i k
    apply (algebraMap F E).injective
    exact congrArg (fun c : GL (Fin 3) E => c i k) hh
  let rho : Representation E R (Fin 3 → E) :=
    (generalLinearNatural 3).comp (fE.comp j)
  have hrho : Function.Injective rho :=
    (generalLinearNatural_injective 3).comp (hfE.comp hj)
  have horder : (Nat.card A : E) ≠ 0 := by
    have hAF : (Nat.card A : F) ≠ 0 := by
      rw [hA4]
      norm_num only [Nat.cast_ofNat]
      rw [show (4 : F) = 2 ^ 2 by norm_num]
      exact pow_ne_zero 2 h2
    intro hh
    apply hAF
    apply (algebraMap F E).injective
    simpa using hh
  have hdet' (a : A) : LinearMap.det (rho (a : R)) = 1 := by
    change LinearMap.det (Matrix.toLin' (fE (j a)).val) = 1
    rw [LinearMap.det_toLin']
    change Matrix.det ((algebraMap F E).mapMatrix (j a).val) = 1
    rw [← RingHom.map_det]
    have hd : (j a).val.det = 1 := congrArg Units.val (hdet a)
    rw [hd,map_one]
  have hfree : ¬ p ∣ Nat.card (centralizer (A : Set R)) := by
    intro hd
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' p hd
    have he : (x : R) = 1 :=
      eq_one_of_centralizes_noncyclic_det_one_three rho A hrho horder
        (by simp only [Module.finrank_pi,Fintype.card_fin]) hn hdet' x x.property
        (by simpa only [Subgroup.coe_pow,Subgroup.coe_one,hx] using congrArg Subtype.val (pow_orderOf_eq_one x))
    have hx1 : x = 1 := Subtype.ext he
    have hp := (Fact.out : p.Prime).one_lt
    simp only [hx1,orderOf_one] at hx
    omega
  have hmapC : (centralizer (A : Set R)).map f = centralizer (B : Set Q) := by
    rw [← hcentral,map_comap_eq,MonoidHom.range_eq_top.mpr hf]
    simp
  intro hd
  exact hfree (hd.trans (hmapC ▸ (centralizer (A : Set R)).card_map_dvd f))

private theorem primeRank_zero_of_not_dvd_card
    {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hp : ¬ p ∣ Nat.card K) : primeRank p K = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (primeRank_le_iff_elementary_card_le K).mpr
  intro A hA
  let : IsElementaryAbelian p A := hA
  have hc : Nat.card A = 1 := (IsElementaryAbelian.isPGroup p A).card_eq_or_dvd.resolve_right
    (fun hd => hp (hd.trans A.card_subgroup_dvd_card))
  simp only [hc,pow_zero,le_refl]

/-- Actual PSL₃ four-group centralizers have defining-prime rank zero. -/
theorem psl3_four_centralizer_rank_zero
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (h2 : (2 : F) ≠ 0) (A : Subgroup PSL(3,F))
    (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 4) :
    primeRank p (centralizer (A : Set PSL(3,F))) = 0 := by
  apply primeRank_zero_of_not_dvd_card
  apply not_dvd_card_four_centralizer_of_cover h2 SpecialLinearGroup.toGL
    SpecialLinearGroup.toGL_injective SpecialLinearGroup.coeToGL_det
    (PSL3.projection F) (PSL3.projection_surjective F)
    (by rw [PSL3.projection_ker])
    (by simpa only [PSL3.projection_ker] using (SL3.odd_card_center F).coprime_two_left)
    A hA hcard

/-- The same calculation applies to every stored ternary Hermitian form and
its literal projective image. -/
theorem psu3_four_centralizer_rank_zero
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F) (h2 : (2 : F) ≠ 0)
    (A : Subgroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J))
    (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 4) :
    primeRank p (centralizer (A : Set
      (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J))) = 0 := by
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  apply primeRank_zero_of_not_dvd_card
  exact not_dvd_card_four_centralizer_of_cover h2 J.specialSubgroup.subtype
    J.specialSubgroup.subtype_injective (fun x => x.property.2)
    J.specialToProjective J.specialToProjective_surjective J.specialToProjective_ker_le_center
    J.odd_card_specialToProjective_ker.coprime_two_left A hA hcard

/-- Uniform odd-characteristic two-rank bound for the actual linear quotient. -/
theorem psl3_two_rank_le
    {F : Type*} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) :
    primeRank 2 PSL(3,F) ≤ 2 := by
  apply (_root_.primeRank_quotient_le_of_coprime 2 (center SL(3,F))
    (SL3.odd_card_center F).coprime_two_left).trans
  exact OddThreeRank.special_primeRank_two_le (MulEquiv.refl _) h2

/-- Uniform odd-characteristic two-rank bound for the actual unitary image. -/
theorem psu3_two_rank_le
    {F : Type*} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F) (h2 : (2 : F) ≠ 0) :
    primeRank 2 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) ≤ 2 := by
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  apply (_root_.primeRank_le_of_surjective_of_coprime 2 J.specialToProjective
    J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left).trans
  exact OddThreeRank.hermitian_special_primeRank_two_le J h2

end Theory.SpecificGroups.DefiningLocalRank
