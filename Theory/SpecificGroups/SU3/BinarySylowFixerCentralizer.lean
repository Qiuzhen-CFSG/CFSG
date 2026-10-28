module
public import Theory.SpecificGroups.SU3.NormalizedRootCentralizers
public import Theory.SpecificGroups.SU3.BinaryInvolutionTable
public import Theory.SpecificGroups.SU3.SylowPointwiseInner.Full
public import Theory.GroupTheory.ComponentLocalPrimeFree
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.NumberTheory.BinaryTorusParity
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Cubic-free fixed subgroups in binary PSU₃ of even field degree

Huppert's actual root and torus coordinates identify the root normalizer
with the projective Borel. Centralizing a nonidentity central root forces
the torus parameter to have norm one. Thus the full involution centralizer
lies in the root group joined with the projective norm-one torus.
At even binary field degree neither factor has order divisible by three.

An actual Hermitian basis change transports the full centralizer to any
form. Pointwise Sylow fixers are inner, so an involutory Sylow fixer has
no cubic fixed subgroup. Simplicity is inherited from its source caller;
no order or simplicity certification is added to the model catalogue.

Source: Huppert II.10.12 and Aschbacher--Smith, proof of 12.6.26, printed p.833.
-/

public section
open Subgroup Matrix BenderSuzuki.External
open scoped Pointwise
namespace BenderSuzuki.MatrixGroups.HermitianForm.BinaryFixedCubic
open BorelTorus BorelTorus.EvenCenterAction OddPrimeSylow.NormalizedOuter.Coverage
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private theorem root_normalizer_eq_borel {q : ℕ} (hq : 1 < q)
    (hcard : Nat.card F = q^2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    normalizer (projectiveRoot J hJ : Set _) = projectiveBorel J hJ := by
  obtain ⟨_,rho,p,_,_,_,hr,_⟩ := huppert_II_10_12 J q hcard hfixed hJ
  obtain ⟨R,T,hRU,_,hn,_,hRT,_,hRc,_,_,_,hreg,⟨coord,hcoord⟩,hT,hTall⟩ := hr
  have hcoord_eq (w : hermitianUnipotentCoord J) :
      (coord w).val = hermitianUnipotentPSU J hJ w := by
    obtain ⟨M,hM,he⟩ := hcoord w
    have hh : M = hermitianUnipotentGL J w := Units.ext hM
    apply Subtype.ext
    simpa only [hh,hermitianUnipotentPSU_val] using he
  have heR : R = projectiveRoot J hJ := by
    apply le_antisymm
    · intro r hr
      obtain ⟨w,hw⟩ := coord.surjective ⟨r,hr⟩
      exact ⟨w,(hcoord_eq w).symm.trans (congrArg Subtype.val hw)⟩
    · rintro _ ⟨w,rfl⟩
      rw [←hcoord_eq w]
      exact (coord w).property
  have heT : T = projectiveTorus J hJ := by
    apply le_antisymm
    · intro t ht
      obtain ⟨k,M,hM,he⟩ := hT ⟨t,ht⟩
      refine ⟨k,?_⟩
      apply Subtype.ext
      have hh : M = hermitianTorusGL J k := Units.ext hM
      simpa only [hh,hermitianTorusPSU_val] using he.symm
    · rintro _ ⟨k,rfl⟩
      obtain ⟨t,M,hM,he⟩ := hTall k
      have hh : (t : ProjectiveSpecialUnitaryMatrixGroup J) = hermitianTorusPSU J hJ k := by
        apply Subtype.ext
        have hM' : M = hermitianTorusGL J k := Units.ext hM
        simpa only [hM',hermitianTorusPSU_val] using he
      exact hh ▸ t.property
  have hne : R ≠ ⊥ := by
    intro hb
    rw [hb,card_bot] at hRc
    have := one_lt_pow₀ hq (by decide : (3 : ℕ) ≠ 0)
    omega
  let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) (BinaryInvolutionTable.IsotropicPoint J) :=
    MulAction.compHom _ rho
  have heN := BenderSuzuki.normalizer_eq_stabilizer_of_regular_compl
    R p (fun _ hx => hRU hx) hne hreg hn
  rw [←heR,projectiveBorel,←heR,←heT,hRT]
  exact heN

variable [CharP F 2]

omit [CharP F 2] in
private theorem root_torus_normalizes {q : ℕ} (hq : 1 < q)
    (hcard : Nat.card F = q^2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    projectiveTorus J hJ ≤ normalizer (projectiveRoot J hJ : Set _) := by
  rw [root_normalizer_eq_borel J hJ hq hcard hfixed]
  exact le_sup_right

private theorem central_borel_le_rootTorus {q : ℕ} (hq : 1 < q)
    (hcard : Nat.card F = q^2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q)
    (r : ProjectiveSpecialUnitaryMatrixGroup J)
    (hr : r ∈ centralImage J hJ) (hne : r ≠ 1) :
    projectiveBorel J hJ ⊓ centralizer ({r} : Set _) ≤ EvenInner.rootTorus J hJ := by
  rw [NormalizedRootCentralizers.uniform_centralImage J hJ r hr hne]
  rintro g ⟨hg,hc⟩
  have hgprod : g ∈ (projectiveRoot J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) *
      (projectiveTorus J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ (root_torus_normalizes J hJ hq hcard hfixed)]
    exact hg
  obtain ⟨u,hu,_,⟨k,rfl⟩,rfl⟩ := hgprod
  have hk : hermitianTorusPSU J hJ k ∈ centralizer (centralImage J hJ : Set _) := by
    let C : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
      centralizer (centralImage J hJ : Set _)
    have hh : u⁻¹ * (u * hermitianTorusPSU J hJ k) ∈ C :=
      C.mul_mem (C.inv_mem (root_centralizes J hJ hu)) hc
    simpa only [inv_mul_cancel_left] using hh
  have hnorm := (torus_centralizer_iff J hJ k).mp hk
  have hnormval := congrArg (fun x : (fixedField J)ˣ => ((x : fixedField J) : F)) hnorm
  change ((k : F) * J.conj (k : F))⁻¹ = 1 at hnormval
  have hkone : k ∈ EvenInner.normOne J := by
    change J.conj (k : F) = (k : F)⁻¹
    exact (eq_inv_of_mul_eq_one_right (inv_eq_one.mp hnormval))
  exact (EvenInner.rootTorus J hJ).mul_mem
    ((show EvenInner.rootImage J hJ ≤ EvenInner.rootTorus J hJ from le_sup_left) hu)
    ((show EvenInner.normOneImage J hJ ≤ EvenInner.rootTorus J hJ from le_sup_right) ⟨⟨k,hkone⟩,rfl⟩)

omit [CharP F 2] in
private theorem rootTorus_three_free {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card F = (2^n)^2)
    (hc : ∀ x : F, J.conj x = x^(2^n)) (heven : Even n) :
    ¬ 3 ∣ Nat.card (EvenInner.rootTorus J hJ) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hc
  have hmod : 2^n % 3 = 1 := by
    rw [Nat.BinaryTorusParity.two_pow_mod_three,if_pos (Nat.even_iff.mp heven)]
  apply Theory.GroupTheory.not_dvd_card_sup_of_normalizes Nat.prime_three
  · apply le_trans _ (root_torus_normalizes J hJ
      (one_lt_pow₀ (by decide) (by omega : n ≠ 0)) hcard hfixed)
    rintro _ ⟨k,rfl⟩
    exact ⟨k.val,rfl⟩
  · rw [EvenInner.rootImage_card J hJ hcard hfixed]
    intro hd
    have hd' := Nat.prime_three.dvd_of_dvd_pow hd
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd')
  · intro hd
    have hh := hd.trans (Subgroup.card_range_dvd (EvenInner.normOneMap J hJ))
    rw [EvenInner.normOne_card J hcard hc,Nat.dvd_iff_mod_eq_zero] at hh
    omega

include hJ in
/-- The full centralizer of an involution has no cubic subgroup at even binary degree. -/
private theorem involution_centralizer_three_free_standard {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2^n)^2)
    (hc : ∀ x : F, J.conj x = x^(2^n)) (heven : Even n)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) (hx : orderOf x = 2) :
    ¬ 3 ∣ Nat.card (centralizer ({x} : Set _)) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hc
  obtain ⟨g,z,hz,he,hC,_⟩ := BinaryInvolutionTable.involution_root_geometry
    J hJ hn hcard hfixed x hx
  let f := MulAut.conj g
  have hzfixed : J.conj z.val.2 = z.val.2 := by
    have hh := z.property
    rw [hz,zero_mul,add_zero] at hh
    exact (eq_neg_of_add_eq_zero_right hh).trans (CharTwo.neg_eq _)
  have hr : root J hJ z ∈ centralImage J hJ := by
    refine ⟨.ofAdd ⟨z.val.2,hzfixed⟩,?_⟩
    change hermitianUnipotentPSU J hJ (centralCoord J (.ofAdd ⟨z.val.2,hzfixed⟩)) =
      hermitianUnipotentPSU J hJ z
    apply congrArg (hermitianUnipotentPSU J hJ)
    exact Subtype.ext (Prod.ext hz.symm rfl)
  have hne : root J hJ z ≠ 1 := by
    rw [←he]
    intro hh
    have hx1 : x = 1 := f.injective (hh.trans (map_one f).symm)
    simp [hx1] at hx
  have hmap : (centralizer ({x} : Set _)).map f.toMonoidHom ≤ EvenInner.rootTorus J hJ := by
    rintro _ ⟨u,hu,rfl⟩
    apply central_borel_le_rootTorus J hJ
      (one_lt_pow₀ (by decide) (by omega : n ≠ 0)) hcard hfixed _ hr hne
    refine ⟨?_,?_⟩
    · have hh := hC hu
      change f u ∈ normalizer (projectiveRoot J hJ : Set _) at hh
      rwa [root_normalizer_eq_borel J hJ
        (one_lt_pow₀ (by decide) (by omega : n ≠ 0)) hcard hfixed] at hh
    · change f u ∈ centralizer ({root J hJ z} : Set _)
      rw [mem_centralizer_singleton_iff,←he]
      exact (show Commute u x from mem_centralizer_singleton_iff.mp hu).map f
  intro hd
  apply rootTorus_three_free J hJ (by omega) hcard hc heven
  apply dvd_trans _ (card_dvd_of_le hmap)
  rwa [card_map_of_injective f.injective]

/-- The same full-centralizer exclusion for any actual Hermitian form. -/
theorem involution_centralizer_three_free {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2^n)^2)
    (hc : ∀ x : F, J.conj x = x^(2^n)) (heven : Even n)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) (hx : orderOf x = 2) :
    ¬ 3 ∣ Nat.card (centralizer ({x} : Set _)) := by
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hc
  obtain ⟨e⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^n) hcard hfixed
  rw [Nat.card_congr
    (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv e x).toEquiv]
  exact involution_centralizer_three_free_standard
    (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J) rfl hn hcard hc heven
    (e x) ((e.orderOf_eq x).trans hx)

/-- A Sylow-fixing involution of PSU₃ at even binary degree fixes no cubic subgroup. -/
theorem sylow_fixer_three_free [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hc : ∀ x : F, J.conj x = x^(2^n)) (heven : Even n)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : orderOf a = 2)
    (hfix : ∀ x ∈ P, a x = x) : ¬ 3 ∣ Nat.card a.fixedSubgroup := by
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hc
  obtain ⟨t,_,rfl⟩ := SylowPointwiseInner.fixing_sylow_eq_mem_conj J hn hcard hc P a hfix
  have hz := BinaryInvolutionTable.center_eq_bot J hn hcard hfixed
  have ht : orderOf t = 2 := (orderOf_injective MulAut.conj
    (MulAut.conj_injective_of_center_eq_bot hz) t).symm.trans ha
  rw [MulAut.fixedSubgroup_conj]
  exact involution_centralizer_three_free J hn hcard hc heven t ht

end BenderSuzuki.MatrixGroups.HermitianForm.BinaryFixedCubic
