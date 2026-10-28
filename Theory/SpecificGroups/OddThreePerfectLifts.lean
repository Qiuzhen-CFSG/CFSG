module
public import Theory.SpecificGroups.GL2.CubicCentralQuotientComponent
public import Theory.SpecificGroups.GL2.NoncommutativeCentralizer
public import Theory.SpecificGroups.SU3.UnitaryTwoResidual
public import Theory.SpecificGroups.OddThreePerfectCentralizers

/-!
# Perfect full-Sylow lifts through ternary centralizer scalar kernels

The actual GL₂ representation makes a central determinant-one kernel
have exponent two. A cubic scalar kernel therefore meets it trivially.
The determinant-kernel image contains every perfect subgroup of the
quotient. Pulling back that subgroup inside the determinant kernel gives
an isomorphic subgroup normalized by a full Sylow of the covering group.

The unitary exporter supplies the actual GU₂ surjection onto every odd
PSU₃ involution centralizer, retaining its central exponent-three kernel.
These maps provide the rank-one reduction in A.3.12(9), pp.47–48, and
the natural larger-span branch of C.5.12, p.163.
-/

public section
open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SpecificGroups.OddThreeLevi
variable {F G H : Type*} [Field F] [Group G] [Group H]

/-- A cubic central quotient is injective on the determinant kernel of any
faithful noncommutative degree-two linear group. -/
theorem determinant_kernel_injective
    (ρ : G →* GL (Fin 2) F) (hρ : Function.Injective ρ) (hG : ¬ IsMulCommutative G)
    (f : G →* H) (hc : f.ker ≤ center G) (h3 : ∀ g ∈ f.ker, g ^ 3 = 1) :
    Function.Injective (f.subgroupMap (GeneralLinearGroup.det.comp ρ).ker) := by
  have hr : ¬ IsMulCommutative ρ.range := by
    intro hh
    let := hh
    exact hG (IsMulCommutative.of_comm (fun x y => hρ (by
      have h := hh.is_comm.comm (ρ.rangeRestrict x) (ρ.rangeRestrict y)
      rw [map_mul,map_mul]
      exact congrArg Subtype.val h)))
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have hxf : (x : G) ∈ f.ker := congrArg Subtype.val hx
  have hs : ρ x ∈ (GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F).range :=
    GeneralLinearGroup.centralizer_le_scalar_of_noncommutative ρ.range hr (by
      rintro y ⟨z,rfl⟩
      simpa only [map_mul] using congrArg ρ (mem_center_iff.mp (hc hxf) z))
  obtain ⟨a,ha⟩ := hs
  have ha2 : a ^ 2 = 1 := by
    have hd : GeneralLinearGroup.det (ρ x) = 1 := x.property
    rw [← ha,GeneralLinearGroup.det_scalar,Fintype.card_fin] at hd
    exact hd
  have hx2 : (x : G) ^ 2 = 1 := hρ (by
    rw [map_pow,← ha,← map_pow,ha2,map_one,map_one])
  have hx1 : (x : G) = 1 := by
    simpa only [pow_succ,hx2,one_mul] using h3 x hxf
  exact Subtype.ext hx1

/-- The actual determinant-kernel image contains the derived subgroup
of every surjective cubic central quotient. -/
theorem commutator_le_det_kernel_image
    (ρ : G →* GL (Fin 2) F) (f : G →* H) (hf : Function.Surjective f) :
    commutator H ≤ ((GeneralLinearGroup.det.comp ρ).ker).map f := by
  have hmap : (commutator G).map f = commutator H := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hf]
    rfl
  rw [← hmap]
  exact map_mono (Abelianization.commutator_subset_ker (GeneralLinearGroup.det.comp ρ))

/-- Every perfect smaller subgroup lifts uniquely inside the determinant
kernel, retaining its literal group structure through the cubic quotient. -/
theorem perfect_subgroup_le_det_kernel_image
    (ρ : G →* GL (Fin 2) F) (f : G →* H) (hf : Function.Surjective f)
    (B : Subgroup H) [Group.IsPerfect B] :
    B ≤ ((GeneralLinearGroup.det.comp ρ).ker).map f := by
  apply le_trans ?_ (commutator_le_det_kernel_image ρ f hf)
  have hm : (commutator B).map B.subtype ≤ commutator H := by
    rw [map_commutator_eq]
    exact commutator_mono le_top le_top
  rw [Group.IsPerfect.commutator_eq_top,← MonoidHom.range_eq_map,range_subtype] at hm
  exact hm

/-- Lift a perfect smaller subgroup and the full Sylow normalizing it
through the cubic central kernel. The lifted subgroup lies literally in
the determinant kernel and maps isomorphically onto the original subgroup. -/
theorem exists_perfect_sylow_normalized_lift [Finite G] [Finite H]
    (ρ : G →* GL (Fin 2) F) (hρ : Function.Injective ρ) (hG : ¬ IsMulCommutative G)
    (f : G →* H) (hf : Function.Surjective f)
    (hc : f.ker ≤ center G) (h3 : ∀ g ∈ f.ker, g ^ 3 = 1)
    (T : Sylow 2 H) (B : Subgroup H) [Group.IsPerfect B]
    (hTB : (T : Subgroup H) ≤ normalizer (B : Set H)) :
    ∃ (S : Sylow 2 G) (A : Subgroup G) (e : A ≃* B),
      S.mapSurjective hf = T ∧
      A ≤ (GeneralLinearGroup.det.comp ρ).ker ∧
      (S : Subgroup G) ≤ normalizer (A : Set G) ∧ ∀ a : A, f a = e a := by
  let D := (GeneralLinearGroup.det.comp ρ).ker
  let A := D ⊓ B.comap f
  have hB : B ≤ D.map f := perfect_subgroup_le_det_kernel_image ρ f hf B
  let a : A →* B := (f.comp A.subtype).codRestrict B (fun x => x.property.2)
  have ha : Function.Injective a := by
    intro x y he
    have hd := determinant_kernel_injective ρ hρ hG f hc h3
    have he' : f.subgroupMap D ⟨x,x.property.1⟩ = f.subgroupMap D ⟨y,y.property.1⟩ :=
      Subtype.ext (congrArg (fun b : B => (b : H)) he)
    exact Subtype.ext (congrArg (fun d : D => (d : G)) (hd he'))
  have has : Function.Surjective a := by
    intro b
    obtain ⟨g,hg,he⟩ := hB b.property
    exact ⟨⟨g,hg,by change f g ∈ B; rw [he]; exact b.property⟩,Subtype.ext he⟩
  let e := MulEquiv.ofBijective a ⟨ha,has⟩
  obtain ⟨S,hS⟩ := Sylow.mapSurjective_surjective hf 2 T
  refine ⟨S,A,e,hS,inf_le_left,?_,fun _ => rfl⟩
  have hn : (S : Subgroup G) ≤ normalizer (B.comap f : Set G) := by
    apply le_trans ?_ (B.le_normalizer_comap f)
    apply map_le_iff_le_comap.mp
    change (S.mapSurjective hf : Subgroup H) ≤ normalizer (B : Set H)
    rw [hS]
    exact hTB
  apply le_trans (le_inf ?_ hn) inf_normalizer_le_normalizer_inf
  rw [D.normalizer_eq_top]
  exact le_top

end Theory.SpecificGroups.OddThreeLevi

namespace Matrix.SU3.OddCubicCentralizer
open Subgroup Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups

private theorem prime_conj (n p : ℕ) [Fact p.Prime]
    (x : GaloisField p (2 * 1)) :
    (ABG.unitaryForm n p 1 one_ne_zero).conj x = x ^ p := by
  simp only [ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]

/-- The full standard PSU₃ involution centralizer is the actual cubic
central quotient of GU₂, with its matrix group retained as the source. -/
theorem standard_surjection (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (t : ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 p 1 one_ne_zero))
    (ht : orderOf t = 2) :
    ∃ f : ABG.GU2 p 1 one_ne_zero →* centralizer ({t} : Set
        (ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 p 1 one_ne_zero))),
      Function.Surjective f ∧ f.ker ≤ center (ABG.GU2 p 1 one_ne_zero) ∧
        ∀ g ∈ f.ker, g ^ 3 = 1 := by
  let J3 := ABG.unitaryForm 3 p 1 one_ne_zero
  let J2 := ABG.unitaryForm 2 p 1 one_ne_zero
  let q := J3.specialToProjective
  have hcube : ∀ x ∈ q.ker, x ^ 3 = 1 := by
    intro x hx
    exact congrArg Subtype.val (J3.specialToProjective_ker_cube ⟨x,hx⟩)
  obtain ⟨z,hz,rfl⟩ := InnerThreeRank.exists_involution_lift_of_cube_kernel q
    J3.specialToProjective_surjective hcube t ht
  let C := centralizer ({z} : Set J3.specialSubgroup)
  have hmap : C.map q = centralizer ({q z} : Set (ProjectiveSpecialUnitaryMatrixGroup J3)) :=
    InnerThreeRank.map_centralizer_of_central_cube_kernel q J3.specialToProjective_surjective
      J3.specialToProjective_ker_le_center hcube z (by simpa only [hz] using pow_orderOf_eq_one z)
  let ep := MulEquiv.subgroupCongr hmap
  let g := ep.toMonoidHom.comp (q.subgroupMap C)
  have hg : Function.Surjective g := ep.surjective.comp (q.subgroupMap_surjective C)
  have hgker : g.ker ≤ center C := by
    intro x hx
    have hxq : (x : J3.specialSubgroup) ∈ q.ker := congrArg Subtype.val hx
    exact mem_center_iff.mpr fun y =>
      Subtype.ext (mem_center_iff.mp (J3.specialToProjective_ker_le_center hxq) y)
  have hgcube : ∀ x ∈ g.ker, x ^ 3 = 1 := by
    intro x hx
    exact Subtype.ext (hcube x (congrArg Subtype.val hx))
  have hp2 : p ≠ 2 := by have := Nat.odd_iff.mp hp; omega
  let e : J2.unitarySubgroup ≃* C :=
    involutionCentralizerEquiv hp2 (GaloisField.card p (2 * 1) (by decide))
      J3 J2 rfl rfl (prime_conj 3 p) (prime_conj 2 p) z hz
  let f := g.comp e.toMonoidHom
  refine ⟨f,hg.comp e.surjective,?_,?_⟩
  · intro x hx
    exact mem_center_iff.mpr fun y => e.injective (by
      simpa only [map_mul,MulEquiv.coe_toMonoidHom] using mem_center_iff.mp (hgker hx) (e y))
  · intro x hx
    exact e.injective (by simpa only [map_pow,map_one] using hgcube (e x) hx)

/-- All allowed Hermitian forms retain the cubic central GU₂ cover. -/
theorem surjection (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (F : Type*) [Field F] [Finite F] (J : HermitianForm 3 F)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2) :
    ∃ f : ABG.GU2 p 1 one_ne_zero →* centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
      Function.Surjective f ∧ f.ker ≤ center (ABG.GU2 p 1 one_ne_zero) ∧
        ∀ g ∈ f.ker, g ^ 3 = 1 := by
  obtain ⟨e⟩ := InnerThreeRank.exists_projective_equiv_standard p F J hcard hc
  let c := InnerThreeRank.centralizerEquiv e t
  obtain ⟨f,hf,hk,h3⟩ := standard_surjection p hp (e t) ((e.orderOf_eq t).trans ht)
  refine ⟨c.symm.toMonoidHom.comp f,c.symm.surjective.comp hf,?_,?_⟩
  · intro x hx
    apply hk
    exact c.symm.injective (hx.trans c.symm.map_one.symm)
  · intro x hx
    exact h3 x (c.symm.injective (hx.trans c.symm.map_one.symm))

end Matrix.SU3.OddCubicCentralizer

namespace Theory.SpecificGroups.OddThreeLevi

/-- A cubic central kernel is disjoint from a subgroup whose center has
order two. In particular, projectivization preserves an SL₂(5) subgroup. -/
theorem injective_on_subgroup_of_center_two
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hk : f.ker ≤ center G) (h3 : ∀ g ∈ f.ker, g ^ 3 = 1)
    (B : Subgroup G) (hB : Nat.card (center B) = 2) :
    Function.Injective (f.subgroupMap B) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have hxf : (x : G) ∈ f.ker := congrArg Subtype.val hx
  have hxZ : x ∈ center B := mem_center_iff.mpr fun y =>
    Subtype.ext (mem_center_iff.mp (hk hxf) y)
  have hx2 : x ^ 2 = 1 := by
    have hd := orderOf_dvd_natCard (⟨x,hxZ⟩ : center B)
    rw [hB] at hd
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp hd)
  have hx3 : x ^ 3 = 1 := Subtype.ext (h3 x hxf)
  simpa only [pow_succ,hx2,one_mul] using hx3

end Theory.SpecificGroups.OddThreeLevi
