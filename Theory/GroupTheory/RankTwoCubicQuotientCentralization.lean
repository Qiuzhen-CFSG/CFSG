module

public import Theory.GroupTheory.OddPrimeSectionCentralizers.FullCentralizer
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.GroupTheory.PGroup.Omega

/-!
# Involutions fixing a noncyclic image of a normal three-group

In a quotient of a group of three-rank at most two, an involution fixing
a noncyclic homomorphic image of a normal three-subgroup centralizes that
whole three-subgroup. Odd-order fixed-point lifting makes its fixed subgroup
surject onto the image. A.1.31 makes the fixed subgroup cyclic if the
involution moves the normal three-subgroup, which is impossible.

The prime-rank hypothesis stays on the original covering group. Neither
solvability nor a rank bound on an arbitrary quotient is assumed.
-/

public section
open Subgroup
namespace Theory.GroupTheory

variable {B A D : Type*} [Group B] [Finite B] [Group A] [Finite A] [Group D]

/-- An involution in the displayed kernel centralizes a normal three-group
whenever its actual quotient image is noncyclic. -/
theorem involution_centralizes_normal_three_of_noncyclic_image
    (cover : B →* A) (hcover : Function.Surjective cover) (hrank : primeRank 3 B ≤ 2)
    (q : A →* D) (P : Subgroup A) [P.Normal] (hP : IsPGroup 3 P)
    (himage : ¬ IsCyclic (P.map q))
    (t : A) (ht : t ^ 2 = 1) (hqt : q t = 1) : t ∈ centralizer (P : Set A) := by
  classical
  by_contra hmove
  have htne : t ≠ 1 := by
    intro he
    exact hmove (he ▸ (centralizer (P : Set A)).one_mem)
  have hto : orderOf t = 2 := orderOf_eq_prime ht htne
  let a : MulAut P := MulAut.conjNormal t
  have ha : Function.Involutive a := by
    intro x
    have h : a ^ 2 = 1 := by
      change (MulAut.conjNormal : A →* MulAut P) t ^ 2 = 1
      rw [←map_pow,ht,map_one]
    exact DFunLike.congr_fun h x
  let F := a.fixedSubgroup
  let C := F.map P.subtype
  have hCF : C ≤ centralizer ({t} : Set A) := by
    rintro _ ⟨x,hx,rfl⟩
    have hh := congrArg Subtype.val ((MulAut.mem_fixedSubgroup a x).mp hx)
    change t * (x : A) * t⁻¹ = x at hh
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hcyc : IsCyclic C :=
    cyclic_pSubgroup_in_involution_centralizer_of_surjective_rank_two
      (by decide : Odd 3) cover hcover hrank P hP t hto hmove C
      ((hP.to_subgroup F).map P.subtype) hCF
  let : IsCyclic F := (F.equivMapOfInjective P.subtype P.subtype_injective).isCyclic.mpr hcyc
  let f : P →* P.map q := q.subgroupMap P
  let : Finite (P.map q) := Finite.of_surjective f (q.subgroupMap_surjective P)
  let fF : F →* P.map q := f.comp F.subtype
  have hodd : Odd (Nat.card P) := by
    obtain ⟨n,hn⟩ := hP.exists_card_eq
    rw [hn]
    exact (by decide : Odd 3).pow
  have hoddIm : Odd (Nat.card (P.map q)) := by
    obtain ⟨n,hn⟩ := (hP.map q).exists_card_eq
    rw [hn]
    exact (by decide : Odd 3).pow
  have hfF : Function.Surjective fF := by
    intro y
    obtain ⟨x,hx,hxy⟩ := MulAut.exists_fixed_preimage_of_odd_card hodd hoddIm a 1 ha
      (fun _ => rfl) f (q.subgroupMap_surjective P) (by
        intro x
        apply Subtype.ext
        change q (t * (x : A) * t⁻¹) = q x
        rw [map_mul,map_mul,map_inv,hqt,one_mul,inv_one,mul_one]) y rfl
    exact ⟨⟨x,(MulAut.mem_fixedSubgroup a x).mpr hx⟩,hxy⟩
  exact himage (isCyclic_of_surjective fF hfF)

/-- The first omega subgroup of the kernel centralizes the same normal
three-group; this applies to every elementary subgroup of that kernel. -/
theorem omega_kernel_centralizes_normal_three_of_noncyclic_image
    (cover : B →* A) (hcover : Function.Surjective cover) (hrank : primeRank 3 B ≤ 2)
    (q : A →* D) (P : Subgroup A) [P.Normal] (hP : IsPGroup 3 P)
    (himage : ¬ IsCyclic (P.map q)) :
    (omega₁ q.ker (p := 2)).map q.ker.subtype ≤ centralizer (P : Set A) := by
  rw [map_le_iff_le_comap]
  apply (closure_le _).mpr
  intro t ht
  apply involution_centralizes_normal_three_of_noncyclic_image
    cover hcover hrank q P hP himage t _ t.property
  exact congrArg Subtype.val (by simpa only [Set.mem_ofPred_eq,pow_one] using ht)

end Theory.GroupTheory
