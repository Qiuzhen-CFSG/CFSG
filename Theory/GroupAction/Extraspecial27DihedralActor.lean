module
public import Theory.GroupAction.Extraspecial27ElementaryActor
public import Theory.GroupTheory.WreathTwoSylowModel
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.ElementaryAbelian.Injective
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
/-!
# The center kernel of a faithful dihedral actor on an extraspecial 27-group

A faithful D₈ actor has a center-action kernel of index at most two. It is
proper because a four-group cannot act faithfully while fixing the center.
Its order is therefore four, and the same elementary-actor bound excludes
the elementary case. The kernel is cyclic. An actual S₃ or S₃≀C₂ quotient
modulo the extraspecial center selects the wreath case and supplies the
original Sylow's dihedral coordinates through the odd kernel.

Source: Aschbacher–Smith, original 13.2.9, final paragraph, printed p.881.
-/
@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Extraspecial27Dihedral
private def four : Subgroup (DihedralGroup 4) where
  carrier x := x=1 ∨ x=.r 2 ∨ x=.sr 0 ∨ x=.sr 2
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro x y
    exact (show ∀ x y : DihedralGroup 4,
      (x=1 ∨ x=.r 2 ∨ x=.sr 0 ∨ x=.sr 2) →
      (y=1 ∨ y=.r 2 ∨ y=.sr 0 ∨ y=.sr 2) →
      (x*y=1 ∨ x*y=.r 2 ∨ x*y=.sr 0 ∨ x*y=.sr 2) by decide +kernel) x y
  inv_mem' := by
    intro x
    exact (show ∀ x : DihedralGroup 4,
      (x=1 ∨ x=.r 2 ∨ x=.sr 0 ∨ x=.sr 2) →
      (x⁻¹=1 ∨ x⁻¹=.r 2 ∨ x⁻¹=.sr 0 ∨ x⁻¹=.sr 2) by decide +kernel) x
private instance : DecidablePred (· ∈ four) := fun x =>
  inferInstanceAs (Decidable (x=1 ∨ x=.r 2 ∨ x=.sr 0 ∨ x=.sr 2))
private instance : IsElementaryAbelian 2 four where
  toIsMulCommutative := ⟨⟨by decide +kernel⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (by decide +kernel)
private theorem four_card : Nat.card four = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem cyclic_of_card_four_not_elementary {B : Type*} [Group B] [Finite B]
    (hB : Nat.card B = 4) (hne : ¬ IsElementaryAbelian 2 B) : IsCyclic B := by
  by_contra hn
  apply hne
  let : IsMulCommutative B := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hB
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro b
  have hd := orderOf_dvd_natCard b
  rw [hB] at hd
  have h4 : orderOf b ≠ 4 := fun h => hn (isCyclic_of_orderOf_eq_card b (h.trans hB.symm))
  have hdiv : orderOf b ∣ 2 := by
    have hs := (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf b ∣ 2^2 by simpa using hd)
    obtain ⟨i,hi,he⟩ := hs
    rw [he]
    interval_cases i <;> norm_num at he h4 ⊢; omega
  exact orderOf_dvd_iff_pow_eq_one.mp hdiv

theorem center_kernel_cyclic_four
    {P S : Type*} [Group P] [Finite P] [IsExtraspecial 3 P]
    [Group S] [Finite S] (hP : Nat.card P = 27) (e : S ≃* DihedralGroup 4)
    (a : S →* MulAut P) (hf : Function.Injective a) :
    let b := (MulAut.characteristic (center P)).comp a
    IsCyclic b.ker ∧ Nat.card b.ker = 4 := by
  let b := (MulAut.characteristic (center P)).comp a
  have hcenter : Nat.card (MulAut (center P)) = 2 := by
    let : IsCyclic (center P) := isCyclic_of_prime_card (by simpa using IsExtraspecial.center_order_p 3 P)
    rw [IsCyclic.card_mulAut,IsExtraspecial.center_order_p 3 P]
    decide
  have hS : Nat.card S = 8 := by rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
  have hbound (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : B ≤ b.ker) : Nat.card B ≤ 2 := by
    apply MulAut.elementary_two_center_preserving_card_le_two hP
      (a.comp B.subtype) (hf.comp B.subtype_injective)
    intro x z hz
    have hh := congrArg (fun f : MulAut (center P) => (f ⟨z,hz⟩ : P)) (hB x.property)
    exact hh
  have hproper : b.ker ≠ ⊤ := by
    intro he
    let E := four.map e.symm.toMonoidHom
    let f : E ≃* four := (four.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm
    let : IsElementaryAbelian 2 E := IsElementaryAbelian.map e.symm.toMonoidHom
    have hc := hbound E (by rw [he]; exact le_top)
    rw [Nat.card_congr f.toEquiv,four_card] at hc
    omega
  have hc : Nat.card b.ker = 4 := by
    have hm := b.ker.card_mul_index
    have hi : b.ker.index ≤ 2 := by
      rw [index_ker]
      exact (Nat.le_of_dvd (by rw [hcenter]; decide) b.range.card_subgroup_dvd_card).trans_eq hcenter
    have hilt : 1 < b.ker.index := by
      have hp : 0 < b.ker.index := Nat.card_pos (α := S ⧸ b.ker)
      have hn : b.ker.index ≠ 1 := fun h => hproper (index_eq_one.mp h)
      omega
    rw [hS] at hm
    have hi2 : b.ker.index=2 := by omega
    rw [hi2] at hm
    omega
  refine ⟨cyclic_of_card_four_not_elementary hc ?_,hc⟩
  intro he
  let := he
  have hh := hbound b.ker le_rfl
  omega
end Extraspecial27Dihedral

namespace Extraspecial27Dihedral
open Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem sylow_center_centralizer (P : Subgroup G) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hcentral : centralizer (P : Set G) ≤ P)
    (S : Sylow 2 G) (e : S ≃* DihedralGroup 4) :
    IsCyclic ((S : Subgroup G) ⊓ centralizer ((center P).map P.subtype : Set G) : Subgroup G) ∧
      Nat.card ((S : Subgroup G) ⊓ centralizer ((center P).map P.subtype : Set G) : Subgroup G) = 4 := by
  let a : S →* MulAut P := (MulAut.conjNormal : G →* MulAut P).comp (S : Subgroup G).subtype
  have hf : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff a).mp
    apply bot_unique
    intro s hs
    have hc : (s : G) ∈ centralizer (P : Set G) := by
      intro p hp
      have hh := congrArg (fun f : MulAut P => (f ⟨p,hp⟩ : G)) hs
      change (s : G)*p*(s : G)⁻¹=p at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hd := S.isPGroup'.disjoint_of_coprime (IsExtraspecial.isPGroup 3 P)
      (by decide : Nat.Coprime 2 3)
    exact Subtype.ext (hd.le_bot ⟨s.property,hcentral hc⟩)
  let b := (MulAut.characteristic (center P)).comp a
  have hk : b.ker = (centralizer ((center P).map P.subtype : Set G)).subgroupOf S := by
    ext s
    change b s = 1 ↔ (s : G) ∈ centralizer ((center P).map P.subtype : Set G)
    constructor
    · intro hs z hz
      obtain ⟨z,hz,rfl⟩ := hz
      have hh := congrArg (fun f : MulAut (center P) => ((f ⟨z,hz⟩ : P) : G)) hs
      change (s : G)*(z : G)*(s : G)⁻¹=z at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hs
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      apply Subtype.ext
      change (s : G) * ((z : P) : G) * (s : G)⁻¹ = ((z : P) : G)
      rw [← hs z (mem_map_of_mem P.subtype z.property),mul_inv_cancel_right]
  let D := (S : Subgroup G) ⊓ centralizer ((center P).map P.subtype : Set G)
  have hm : b.ker.map (S : Subgroup G).subtype = D := by
    rw [hk,subgroupOf_map_subtype,inf_comm]
  let eD : b.ker ≃* D :=
    (b.ker.equivMapOfInjective (S : Subgroup G).subtype (S : Subgroup G).subtype_injective).trans
      (MulEquiv.subgroupCongr hm)
  obtain ⟨hcyc,hcard⟩ := center_kernel_cyclic_four hP e a hf
  let := hcyc
  exact ⟨isCyclic_of_surjective eD.toMonoidHom eD.surjective,
    (Nat.card_congr eD.toEquiv).symm.trans hcard⟩
end Extraspecial27Dihedral

namespace Extraspecial27Dihedral
open Subgroup
variable {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
theorem sylow_model_of_wreath (S : Sylow 2 G) (f : G →* A) (hf : Function.Surjective f)
    (hk : Nat.card f.ker = 3)
    (e : A ≃* RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
      (Multiplicative (ZMod 2))) : Nonempty (S ≃* DihedralGroup 4) := by
  have hi := injective_comp_subtype_of_coprime_ker f (by rw [hk]; decide : Nat.Coprime 2 (Nat.card f.ker))
    (S : Subgroup G) S.isPGroup'
  let S' := S.mapSurjective hf
  let eS : S ≃* S' := MulEquiv.ofBijective (f.subgroupMap (S : Subgroup G))
    ⟨fun x y h => hi (congrArg Subtype.val h),f.subgroupMap_surjective _⟩
  let S'' := S'.mapSurjective (f := e.toMonoidHom) e.surjective
  let eS' : S' ≃* S'' := (S' : Subgroup A).equivMapOfInjective e.toMonoidHom e.injective
  obtain ⟨ed⟩ := wreath_two_sylow_mulEquiv_dihedral_four S''
  exact ⟨eS.trans (eS'.trans ed)⟩

theorem centerSylow_cyclic_of_small_quotient
    (P : Subgroup G) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hcentral : centralizer (P : Set G) ≤ P)
    (S : Sylow 2 G) (f : G →* A) (hf : Function.Surjective f)
    (hk : f.ker = (center P).map P.subtype)
    (ha : Nonempty (A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) ∨
      Nonempty (A ≃* RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
        (Multiplicative (ZMod 2)))) :
    IsCyclic ((S : Subgroup G) ⊓ centralizer ((center P).map P.subtype : Set G) : Subgroup G) ∧
      Nat.card ((S : Subgroup G) ⊓ centralizer ((center P).map P.subtype : Set G) : Subgroup G) = 4 := by
  have hkerCard : Nat.card f.ker = 3 := by
    rw [hk,card_map_of_injective P.subtype_injective,IsExtraspecial.center_order_p 3 P]
  rcases ha with he | he
  · obtain ⟨e⟩ := he
    have hcA : Nat.card A = 6 := by
      rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card]
      decide +kernel
    have hm := f.ker.card_mul_index
    have hi : f.ker.index = Nat.card A := by
      exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
    rw [hkerCard,hi,hcA] at hm
    have hd := P.card_subgroup_dvd_card
    rw [hP,← hm] at hd
    norm_num at hd
  · obtain ⟨e⟩ := he
    obtain ⟨eS⟩ := sylow_model_of_wreath S f hf hkerCard e
    exact sylow_center_centralizer P hP hcentral S eS
end Extraspecial27Dihedral
