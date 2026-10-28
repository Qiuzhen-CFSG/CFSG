module
public import Theory.SpecificGroups.OddThreePerfectLifts
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Cyclic two-subgroups centralizing perfect odd ternary subgroups

A perfect subgroup of a cubic central quotient of a faithful degree-two
linear group lifts inside the determinant kernel. That kernel meets the
cubic central kernel trivially. An element centralizing the perfect image
therefore centralizes its lift, so its matrix is scalar. The resulting
centralizer is cyclic over a finite field.

For a two-subgroup centralizing a nontrivial perfect subgroup of an odd
PSL₃ or PSU₃, choose an involution in its center. The actual involution
centralizer is a cubic central quotient of GL₂ or GU₂. Applying the scalar
calculation there proves that the original two-subgroup is cyclic.
Both projective scalar kernels and the original subgroup inclusions are
retained. This is used on the literal secondary image in the corrected
nonblock sieve.
Source: Aschbacher--Smith A.3.21(a), p.55, and the proper two-local
inspection in 4.3.16, p.618. Matrix and unitary transports come from the
attributed results in OddThreePerfectLifts.
-/

public section
noncomputable section

open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SpecificGroups.OddThreeLevi
variable {F A H : Type*} [Field F] [Finite F] [Group A] [Group H]

/-- Perfect subgroups of a cubic central degree-two quotient have cyclic centralizer. -/
theorem centralizer_perfect_isCyclic
    (ρ : A →* GL (Fin 2) F) (hρ : Function.Injective ρ)
    (f : A →* H) (hf : Function.Surjective f)
    (hc : f.ker ≤ center A) (h3 : ∀ a ∈ f.ker, a ^ 3 = 1)
    (B : Subgroup H) [Group.IsPerfect B] (hB : B ≠ ⊥) :
    IsCyclic (centralizer (B : Set H)) := by
  let : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).mpr hB
  have hA : ¬ IsMulCommutative A := by
    intro ha
    have hh : IsMulCommutative H := IsMulCommutative.of_comm (fun x y => by
      obtain ⟨x,rfl⟩ := hf x
      obtain ⟨y,rfl⟩ := hf y
      rw [←map_mul,←map_mul,ha.is_comm.comm x y])
    exact Group.IsPerfect.not_isMulCommutative B (IsMulCommutative.of_comm
      (fun x y => Subtype.ext (hh.is_comm.comm x y)))
  let D := (GeneralLinearGroup.det.comp ρ).ker
  have hinj := determinant_kernel_injective ρ hρ hA f hc h3
  have hBD : B ≤ D.map f := perfect_subgroup_le_det_kernel_image ρ f hf B
  let P := D ⊓ B.comap f
  let q : P →* B := (f.comp P.subtype).codRestrict B (fun x => x.property.2)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨a,ha,he⟩ := hBD x.property
    refine ⟨⟨a,ha,?_⟩,Subtype.ext he⟩
    change f a ∈ B
    simpa only [he] using x.property
  have hP : ¬ IsMulCommutative (P.map ρ) := by
    intro hh
    apply Group.IsPerfect.not_isMulCommutative B
    apply IsMulCommutative.of_comm
    intro x y
    obtain ⟨x,rfl⟩ := hq x
    obtain ⟨y,rfl⟩ := hq y
    rw [←map_mul,←map_mul]
    congr 1
    apply Subtype.ext
    apply hρ
    change ρ ((x : A)*(y : A)) = ρ ((y : A)*(x : A))
    rw [map_mul,map_mul]
    exact congrArg Subtype.val (hh.is_comm.comm
      (ρ.subgroupMap P x) (ρ.subgroupMap P y))
  let Z := (GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F).range
  let C := Z.comap ρ
  let : IsCyclic Z := isCyclic_of_surjective
    (GeneralLinearGroup.scalar (Fin 2)).rangeRestrict
    (GeneralLinearGroup.scalar (Fin 2)).rangeRestrict_surjective
  let j : C →* Z := (ρ.comp C.subtype).codRestrict Z (fun x => x.property)
  let : IsCyclic C := isCyclic_of_injective j (fun x y h =>
    Subtype.ext (hρ (congrArg Subtype.val h)))
  let : IsCyclic (C.map f) := isCyclic_of_surjective (f.subgroupMap C)
    (f.subgroupMap_surjective C)
  apply isCyclic_of_le (show centralizer (B : Set H) ≤ C.map f from ?_)
  intro x hx
  obtain ⟨a,rfl⟩ := hf x
  refine ⟨a,?_,rfl⟩
  apply GeneralLinearGroup.centralizer_le_scalar_of_noncommutative (P.map ρ) hP
  rintro _ ⟨b,hb,rfl⟩
  have he : a*b*a⁻¹ = b := by
    apply congrArg Subtype.val (hinj (a₁ := ⟨a*b*a⁻¹,
      (inferInstance : D.Normal).conj_mem b hb.1 a⟩) (a₂ := ⟨b,hb.1⟩) ?_)
    apply Subtype.ext
    change f (a*b*a⁻¹) = f b
    rw [map_mul,map_mul,map_inv,←hx (f b) hb.2,mul_inv_cancel_right]
  have hab := mul_inv_eq_iff_eq_mul.mp he
  simpa only [map_mul] using congrArg ρ hab.symm
end Theory.SpecificGroups.OddThreeLevi

namespace Theory.GroupTheory
variable {H : Type*} [Group H] [Finite H]

/-- Local cyclic centralizers control any centralizing two-subgroup. -/
theorem twoGroup_centralizing_perfect_isCyclic
    (hlocal : ∀ (t : H), orderOf t = 2 → ∀ B : Subgroup (centralizer ({t} : Set H)),
      Group.IsPerfect B → B ≠ ⊥ → IsCyclic (centralizer (B : Set (centralizer ({t} : Set H)))))
    (B R : Subgroup H) [Group.IsPerfect B] (hB : B ≠ ⊥)
    (hR : IsPGroup 2 R) (hRB : R ≤ centralizer (B : Set H)) : IsCyclic R := by
  by_cases hzero : R = ⊥
  · subst R
    infer_instance
  let : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hzero
  let := hR.center_nontrivial
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center R) 2
    ((hR.to_subgroup (center R)).card_eq_or_dvd.resolve_left
      (by have hh : 1 < Nat.card (center R) := Finite.one_lt_card
          omega))
  let t : H := z.val.val
  have ht : orderOf t = 2 := by
    exact (Subgroup.orderOf_coe z.val).trans ((Subgroup.orderOf_coe z).trans hz)
  let C := centralizer ({t} : Set H)
  have hRC : R ≤ C := by
    intro r hr
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_center_iff.mp z.property ⟨r,hr⟩)
  have hBC : B ≤ C := by
    intro b hb
    apply mem_centralizer_singleton_iff.mpr
    exact hRB z.val.property b hb
  let X := B.subgroupOf C
  let a : X ≃* B := subgroupOfEquivOfLe hBC
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := a.symm.toMonoidHom) a.symm.surjective
  have hX : X ≠ ⊥ := by
    intro hx
    apply hB
    have hh := congrArg (Subgroup.map C.subtype) hx
    simpa only [X,map_subgroupOf_eq_of_le hBC,Subgroup.map_bot] using hh
  let := hlocal t ht X inferInstance hX
  let j : R →* centralizer (X : Set C) :=
    (inclusion hRC).codRestrict _ (by
      intro r x hx
      exact Subtype.ext (hRB r.property x hx))
  exact isCyclic_of_injective j (fun x y h =>
    Subtype.ext (congrArg (fun k : centralizer (X : Set C) => (k.val.val : H)) h))
end Theory.GroupTheory

namespace Theory.SpecificGroups.OddThreeLevi
open BenderSuzuki.MatrixGroups

/-- The cyclicity conclusion for actual odd projective linear-three subgroups. -/
theorem linear_twoGroup_centralizing_perfect_isCyclic
    {F : Type*} [Field F] [Finite F] (hF : (2 : F) ≠ 0)
    (B R : Subgroup PSL(3,F)) [Group.IsPerfect B] (hB : B ≠ ⊥)
    (hR : IsPGroup 2 R) (hRB : R ≤ centralizer (B : Set PSL(3,F))) : IsCyclic R := by
  apply twoGroup_centralizing_perfect_isCyclic (fun t ht X hX hne => ?_) B R hB hR hRB
  let := hX
  obtain ⟨f,hf,hc,h3⟩ := PSL3.OddInvolutionFixed.exists_gl2_cubic_central_surjection t ht hF
  exact centralizer_perfect_isCyclic (MonoidHom.id _) Function.injective_id f hf hc h3 X hne

/-- The cyclicity conclusion retains every allowed odd-prime Hermitian marking. -/
theorem unitary_twoGroup_centralizing_perfect_isCyclic
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p^2)
    (hc : ∀ x, J.conj x = x^p)
    (B R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) [Group.IsPerfect B]
    (hB : B ≠ ⊥) (hR : IsPGroup 2 R)
    (hRB : R ≤ centralizer (B : Set (ProjectiveSpecialUnitaryMatrixGroup J))) : IsCyclic R := by
  let : Fact p.Prime := ⟨hp⟩
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  apply twoGroup_centralizing_perfect_isCyclic (fun t ht X hX hne => ?_) B R hB hR hRB
  let := hX
  obtain ⟨f,hf,hker,h3⟩ := Matrix.SU3.OddCubicCentralizer.surjection p ho F J hF hc t ht
  exact centralizer_perfect_isCyclic (ABG.unitaryForm 2 p 1 one_ne_zero).unitarySubgroup.subtype
    Subtype.val_injective f hf hker h3 X hne
end Theory.SpecificGroups.OddThreeLevi
