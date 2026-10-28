module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ActionBounds
public import Theory.SpecificGroups.SU3.NoncubicFieldActors
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank.MatrixWitnesses
public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Fixed cubic planes in the actual binary unitary component

A cubic field automorphism fixes the scalar cube roots. In a binary
orthonormal basis the diagonal cubic and a coordinate cycle give an
independent commuting pair in PSU₃. Their actual fixed subgroup therefore
has rank two. Its faithful inner image and the outside field actor force
rank three. These are the literal unitary matrices and their field action.
Source: Aschbacher–Smith A.3.18, printed pp.51–53.
-/

@[expose] public noncomputable section
open Subgroup Matrix Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.SpecificGroups
open Theory.SpecificGroups.SignedThreeCubicRank
open BenderSuzuki.MatrixGroups.HermitianForm
open ExtensionBorel UnitaryThree.OddTorusNormalizer EvenInner
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.UnitaryField
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private def binaryBasis : GL (Fin 3) F := {
  val := !![1,0,1;1,1,1;0,1,1]
  inv := !![0,1,1;1,1,0;1,1,1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_three,CharTwo.add_self_eq_zero]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_three,CharTwo.add_self_eq_zero] }

private def binaryFrame : OrthogonalFrame J := ⟨binaryBasis, by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryBasis,HermitianForm.conjTranspose,hJ,Matrix.mul_apply,
      Fin.sum_univ_three,CharTwo.add_self_eq_zero]⟩

omit [Finite F] in
private theorem binaryBasis_map (σ : F ≃+* F) :
    GeneralLinearGroup.map σ.toRingHom (binaryBasis (F := F)) = binaryBasis := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [binaryBasis,GeneralLinearGroup.map]

private theorem fixes_cubic_scalar {F : Type*} [Field F] (σ : F ≃+* F) (hs : σ ^ 3 = 1)
    (u : F) (hu : u ^ 3 = 1) (hne : u ≠ 1) : σ u = u := by
  have hp : IsPrimitiveRoot u 3 := IsPrimitiveRoot.iff_orderOf.mpr
    (orderOf_eq_prime hu hne)
  obtain ⟨k, hk, he⟩ := hp.eq_pow_of_pow_eq_one (show σ u ^ 3 = 1 by rw [← map_pow, hu, map_one])
  have hne' : σ u ≠ 1 := by simpa using hne
  have hs' : σ (σ (σ u)) = u := DFunLike.congr_fun hs u
  interval_cases k
  · exact (hne' (by simpa using he.symm)).elim
  · simpa using he.symm
  · have h2 : σ u = u ^ 2 := he.symm
    rw [h2, map_pow, h2, map_pow, map_pow, h2] at hs'
    have h8 : ((u ^ 2) ^ 2) ^ 2 = u ^ 2 := by
      calc ((u ^ 2) ^ 2) ^ 2 = u ^ 3 * u ^ 3 * u ^ 2 := by ring
           _ = u ^ 2 := by rw [hu]; simp
    rw [h8] at hs'
    have hu0 : u ≠ 0 := by intro he; simp [he] at hu
    have h1 : u = 1 := by
      apply mul_right_cancel₀ hu0
      simpa only [pow_two, one_mul] using hs'
    exact (hne h1).elim

omit [Finite F] [CharP F 2] in
private theorem diagonal_unitary (u : F) (hu : u ^ 3 = 1)
    (J : HermitianForm 3 F) (hJ : J.form = 1) (hnorm : J.conj u * u = 1) :
    SpecialLinearGroup.toGL (diagonal u hu) ∈ J.specialSubgroup := by
  rw [J.mem_specialSubgroup_iff]
  refine ⟨?_, SpecialLinearGroup.coeToGL_det _⟩
  rw [hJ, mul_one]
  change J.conjTranspose (diagonal u hu).val * (diagonal u hu).val = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SignedThreeCubicRank.diagonal, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, hnorm]
  calc J.conj u ^ 2 * u ^ 2 = (J.conj u * u) ^ 2 := by ring
       _ = 1 := by rw [hnorm]; simp

omit [Finite F] [CharP F 2] in
private theorem cycle_unitary (J : HermitianForm 3 F) (hJ : J.form = 1) :
    SpecialLinearGroup.toGL (cycle (F := F)) ∈ J.specialSubgroup := by
  rw [J.mem_specialSubgroup_iff]
  refine ⟨?_, SpecialLinearGroup.coeToGL_det _⟩
  rw [hJ, mul_one]
  change J.conjTranspose (cycle (F := F)).val * (cycle (F := F)).val = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycle, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three]

/-- The diagonal cubic and coordinate cycle lie in the literal fixed subgroup. -/
theorem fixed_rank {n : ℕ} (hn : Odd n) (hF : Nat.card F = (2 ^ n) ^ 2)
    (hc : ∀ x, J.conj x = x ^ (2 ^ n))
    (σ : F ≃+* F) (hσ : σ ^ 3 = 1) :
    2 ≤ primeRank 3 (fieldActorHom J hJ σ).fixedSubgroup := by
  let : Finite (ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := normOne J) 3 (by
    rw [normOne_card J hF hc]
    apply Nat.dvd_of_mod_eq_zero
    have hh : 2 ^ n % 3 = 2 := by
      rw [Nat.BinaryTorusParity.two_pow_mod_three, if_neg]
      have hh := Nat.odd_iff.mp hn
      omega
    omega)
  have hu3 : (u.val : F) ^ 3 = 1 := congrArg (fun t : normOne J => (t.val : F))
    (hu ▸ pow_orderOf_eq_one u)
  have hu1 : (u.val : F) ≠ 1 := by
    intro he
    have he' : u = 1 := Subtype.ext (Units.ext he)
    rw [he', orderOf_one] at hu
    omega
  have hnorm : J.conj (u.val : F) * (u.val : F) = 1 := by
    rw [show J.conj (u.val : F) = (u.val : F)⁻¹ from u.property]
    exact inv_mul_cancel₀ (Units.ne_zero _)
  have hfix := fixes_cubic_scalar σ hσ (u.val : F) hu3 hu1
  let D := SpecialLinearGroup.toGL (diagonal (u.val : F) hu3)
  let C := SpecialLinearGroup.toGL (cycle (F := F))
  let P := binaryFrame J hJ
  let x : J.specialSubgroup := ⟨P.val * D * P.val⁻¹,
    (HermitianForm.IdentityGram.special_conjugate_iff J P.val D P.property).mpr
      (diagonal_unitary (u.val : F) hu3 (HermitianForm.IdentityGram.identityGram J) rfl hnorm)⟩
  let y : J.specialSubgroup := ⟨P.val * C * P.val⁻¹,
    (HermitianForm.IdentityGram.special_conjugate_iff J P.val C P.property).mpr
      (cycle_unitary (HermitianForm.IdentityGram.identityGram J) rfl)⟩
  have hD : GeneralLinearGroup.map σ.toRingHom D = D := by
    apply Units.ext
    ext i j
    change σ ((diagonal (u.val : F) hu3).val i j) = (diagonal (u.val : F) hu3).val i j
    fin_cases i <;> fin_cases j <;> simp [SignedThreeCubicRank.diagonal,hfix]
  have hC : GeneralLinearGroup.map σ.toRingHom C = C := by
    apply Units.ext
    ext i j
    change σ ((cycle (F := F)).val i j) = (cycle (F := F)).val i j
    fin_cases i <;> fin_cases j <;> simp [cycle]
  have fixed (z : J.specialSubgroup)
      (hz : GeneralLinearGroup.map σ.toRingHom z.val = z.val) :
      J.specialToProjective z ∈ (fieldActorHom J hJ σ).fixedSubgroup := by
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply Subtype.ext
    simp only [fieldActorHom,MonoidHom.coe_mk,OneHom.coe_mk,fieldActor_apply_val]
    rw [J.specialToProjective_apply_val,ProjGenLinGroup.map_mk,hz]
  let X : (fieldActorHom J hJ σ).fixedSubgroup := ⟨J.specialToProjective x, fixed x (by
    change GeneralLinearGroup.map σ.toRingHom (binaryBasis * D * binaryBasis⁻¹) = _
    rw [map_mul,map_mul,map_inv,binaryBasis_map,hD]
    rfl)⟩
  let Y : (fieldActorHom J hJ σ).fixedSubgroup := ⟨J.specialToProjective y, fixed y (by
    change GeneralLinearGroup.map σ.toRingHom (binaryBasis * C * binaryBasis⁻¹) = _
    rw [map_mul,map_mul,map_inv,binaryBasis_map,hC]
    rfl)⟩
  let f : (fieldActorHom J hJ σ).fixedSubgroup →* ProjGenLinGroup (Fin 3) F :=
    (MulAut.conj (ProjGenLinGroup.mk P.val)⁻¹).toMonoidHom.comp
      ((ProjectiveSpecialUnitaryMatrixGroup J).subtype.comp
        (fieldActorHom J hJ σ).fixedSubgroup.subtype)
  apply projective_rank (u.val : F) hu3 hu1 f
    ((MulAut.conj _).injective.comp (Subtype.val_injective.comp Subtype.val_injective)) X Y
  · simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_subtype, X, J.specialToProjective_apply_val]
    change (ProjGenLinGroup.mk P.val)⁻¹ * ProjGenLinGroup.mk (P.val * D * P.val⁻¹) *
        ((ProjGenLinGroup.mk P.val)⁻¹)⁻¹ = _
    simp only [map_mul,map_inv,inv_inv]
    group
    rfl
  · simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_subtype, Y, J.specialToProjective_apply_val]
    change (ProjGenLinGroup.mk P.val)⁻¹ * ProjGenLinGroup.mk (P.val * C * P.val⁻¹) *
        ((ProjGenLinGroup.mk P.val)⁻¹)⁻¹ = _
    simp only [map_mul,map_inv,inv_inv]
    group
    rfl
theorem actor_rank_three {n : ℕ} (hn : 2 ≤ n) (ho : Odd n)
    (hcard : Nat.card F = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hinner : MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) ≤ A)
    (σ : F ≃+* F) (hσ : orderOf σ=3) (hσA : fieldActorHom J hJ σ ∈ A)
    : 3 ≤ primeRank 3 A := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hr := fixed_rank J hJ ho hcard hconj σ (hσ ▸ pow_orderOf_eq_one σ)
  obtain ⟨B,hB,hcB⟩ := exists_elementaryAbelian_card_primeRank
    (G := (fieldActorHom J hJ σ).fixedSubgroup) (p := 3)
  let := hB
  obtain ⟨C,hC⟩ := Sylow.exists_subgroup_card_pow_prime (G := B) 3
    (n := 2) (by rw [hcB]; exact pow_dvd_pow 3 hr)
  let : IsElementaryAbelian 3 C := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun c => by
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 B) c.val) }
  let j := (fieldActorHom J hJ σ).fixedSubgroup.subtype.comp B.subtype
  let E := C.map j
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.map j
  have hj : Function.Injective j :=
    (fieldActorHom J hJ σ).fixedSubgroup.subtype_injective.comp B.subtype_injective
  have hEc : Nat.card E = 3^2 := by rw [card_map_of_injective hj,hC]
  have hfix : E ≤ (fieldActorHom J hJ σ).fixedSubgroup := by
    rintro _ ⟨c,_,rfl⟩
    exact c.val.property
  let f : ProjectiveSpecialUnitaryMatrixGroup J →* A :=
    MulAut.conj.codRestrict A (fun g => hinner ⟨g,rfl⟩)
  have hf : Function.Injective f := by
    intro x y hh
    exact (MulAut.conj_injective_of_center_eq_bot
      (EvenProjectiveComparison.center_eq_bot J (by omega) hcard hconj))
      (congrArg Subtype.val hh)
  let U := E.map f
  let : IsElementaryAbelian 3 U := IsElementaryAbelian.map f
  let x : A := ⟨fieldActorHom J hJ σ,hσA⟩
  have hx : orderOf x=3 := by
    rw [←orderOf_injective A.subtype A.subtype_injective]
    exact (orderOf_injective (fieldActorHom J hJ)
      (NoncubicFieldActors.fieldActor_injective J hJ hn hcard hconj) σ).trans hσ
  have hxU : x ∉ U := by
    rintro ⟨g,_,he⟩
    have hs := NoncubicFieldActors.field_eq_one_of_inner J hJ hn hcard hconj σ ⟨g,congrArg Subtype.val he⟩
    rw [hs,orderOf_one] at hσ
    exact Nat.prime_three.ne_one hσ.symm
  have hUfix : U ≤ centralizer ({x} : Set A) := by
    rintro _ ⟨g,hg,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    have hgfix := (MulAut.mem_fixedSubgroup _ _).mp (hfix hg)
    change g * (fieldActorHom J hJ σ) y * g⁻¹ = (fieldActorHom J hJ σ) (g*y*g⁻¹)
    rw [map_mul,map_mul,map_inv,hgfix]
  have hcU : Nat.card U = 3^2 := by rw [card_map_of_injective hf,hEc]
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join U x hx hxU hUfix hcU


end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.UnitaryField
