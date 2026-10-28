module
public import Theory.Representation.BinaryAlternatingFiveExtension.MarkedAlternating
public import Theory.SpecificGroups.AlternatingFiveSquareGeneratorKernel
public import Theory.SpecificGroups.SymmetricFive.OuterFourCommutator

/-!
# A residual four-group detected by a Sylow-normal elementary subgroup

Let q map onto S₅, with kernel O₂(D) and residual image A₅. Suppose an
elementary subgroup B is normalized by the prescribed Sylow and has outer
four-group image. An even Sylow element lifts into O²(D); its commutator
with B is an involution in B intersect O²(D) with nontrivial even image.
If the kernel commutators with B lie in the prescribed normal natural
module U, the A₅ cover theorem identifies the residual kernel with U.
The marked natural extension splits and supplies an elementary residual
subgroup with image four under the same q. There is no kernel-order bound.

Source application: Aschbacher--Smith 13.2.8(1), p.880; the central-cover
input is C.5.6(7), p.159, and natural splitting is the A₅ case of 2.4.29.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace BinaryPermutation.AlternatingFiveExtension
variable {D : Type*} [Group D] [Finite D]

theorem residual_kernel_eq_of_normal_elementary
    (S : Sylow 2 D) (q : D →* Equiv.Perm (Fin 5))
    (hq : Function.Surjective q) (hk : q.ker=pCore 2 D)
    (hr : (pResidual 2 D).map q=alternatingGroup (Fin 5))
    (U B : Subgroup D) [U.Normal] [IsElementaryAbelian 2 B]
    (hU : U≤q.ker) (hUR : U≤pResidual 2 D)
    (hBS : B≤(S:Subgroup D)) (hSB : (S:Subgroup D)≤normalizer (B:Set D))
    (hBcard : Nat.card (B.map q)=4) (hout : ¬ B.map q≤alternatingGroup (Fin 5))
    (hcomm : ⁅q.ker,B⁆≤U) : pResidual 2 D⊓q.ker=U := by
  let R := pResidual 2 D
  let f : R →* alternatingGroup (Fin 5) :=
    (q.comp R.subtype).codRestrict _ (fun x => hr ▸ mem_map_of_mem q x.property)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨x,hx,he⟩ := hr.ge a.property
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  have hfk : f.ker=q.ker.subgroupOf R := by
    ext x
    exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
  let A := U.subgroupOf R
  let C := B.subgroupOf R
  let : A.Normal := normal_subgroupOf_of_le_normalizer (U.normalizer_eq_top ▸ le_top)
  have hA : A≤f.ker := by rw [hfk];exact fun x hx=>hU hx
  have hC : C.map f≠⊥ := by
    let : IsElementaryAbelian 2 (B.map q) := IsElementaryAbelian.map q
    obtain ⟨a,ha,haeven,b,hb,hab⟩ :=
      Theory.SpecificGroups.SymmetricFive.OuterFourCommutator.exists_even_commutator
        (S.mapSurjective hq) (B.map q) hBcard (map_mono hBS) hout
    obtain ⟨r,hrR,hra⟩ := hr.ge haeven
    have hrS : r∈(S:Subgroup D) := by
      have hpre : r ∈ ((S:Subgroup D).map q).comap q := by
        change q r ∈ (S:Subgroup D).map q
        rwa [hra]
      rw [comap_map_eq,sup_eq_left.mpr (hk.symm ▸ pCore_isPGroup.le_sylow_of_normal S)] at hpre
      exact hpre
    obtain ⟨v,hv,hvb⟩ := hb
    have hvr : ⁅r,v⁆∈R := (commutator_le_left R B) (commutator_mem_commutator hrR hv)
    have hvB : ⁅r,v⁆∈B := by
      have hh := le_normalizer_iff_commutator_le_left.mp hSB
      rw [commutator_comm] at hh
      exact hh (commutator_mem_commutator hrS hv)
    intro hz
    have hh := mem_map_of_mem f (show (⟨⁅r,v⁆,hvr⟩:R)∈C from hvB)
    rw [hz,mem_bot] at hh
    have he := congrArg Subtype.val hh
    change q ⁅r,v⁆=1 at he
    rw [map_commutatorElement,hra,hvb] at he
    exact hab he
  have hCA : ⁅f.ker,C⁆≤A := by
    intro x hx
    have hh := mem_map_of_mem R.subtype hx
    rw [map_commutator,hfk,subgroupOf_map_subtype,subgroupOf_map_subtype] at hh
    exact hcomm ((commutator_mono inf_le_left inf_le_left) hh)
  have hsq : ∀r∈C,r^2∈A := by
    intro r hr
    have hh : (r:D)^2=1 := elemPow_eq_one_of_isElementaryAbelian (r:D) hr
    have he : r^2=1 := Subtype.ext hh
    rw [he]
    exact A.one_mem
  have he := alternatingGroup.kernel_eq_of_square_normal_generator f hf
    (hfk ▸ (hk.symm ▸ pCore_isPGroup).comap_subtype) (isPPerfect_pResidual 2)
    A C hA hC hCA hsq
  have hm := congrArg (map R.subtype) he
  rw [hfk,subgroupOf_map_subtype,map_subgroupOf_eq_of_le hUR] at hm
  exact (inf_comm _ _).trans hm
end BinaryPermutation.AlternatingFiveExtension

namespace BinaryPermutation.AlternatingFiveExtension
variable {D : Type*} [Group D] [Finite D]
theorem exists_residual_four_of_normal_elementary
    (S : Sylow 2 D) (q : D →* Equiv.Perm (Fin 5))
    (hq : Function.Surjective q) (hk : q.ker=pCore 2 D)
    (hr : (pResidual 2 D).map q=alternatingGroup (Fin 5))
    (U B : Subgroup D) [U.Normal] [IsElementaryAbelian 2 B]
    (hU : U≤q.ker) (hUR : U≤pResidual 2 D)
    (hBS : B≤(S:Subgroup D)) (hSB : (S:Subgroup D)≤normalizer (B:Set D))
    (hBcard : Nat.card (B.map q)=4) (hout : ¬ B.map q≤alternatingGroup (Fin 5))
    (hcomm : ⁅q.ker,B⁆≤U)
    (i : Multiplicative (BinaryPermutation.core (Fin 5)) →* D)
    (hi : Function.Injective i) (hir : i.range = U)
    (he : ∀ (g : D) (v : Multiplicative (BinaryPermutation.core (Fin 5))),
      i (BinaryPermutation.AlternatingFiveExtension.coreAction (q g) v) = g * i v * g⁻¹) :
    ∃ A : Subgroup D, IsElementaryAbelian 2 A ∧ A ≤ pResidual 2 D ∧
      Nat.card (A.map q) = 4 := by
  have hRU := residual_kernel_eq_of_normal_elementary S q hq hk hr U B hU hUR hBS hSB hBcard hout hcomm
  let R := pResidual 2 D
  let f : R →* alternatingGroup (Fin 5) :=
    (q.comp R.subtype).codRestrict _ (fun x => hr ▸ mem_map_of_mem q x.property)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨x,hx,he⟩ := hr.ge a.property
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  have hfk : f.ker = q.ker.subgroupOf R := by
    ext x
    exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
  have hkm : f.ker.map R.subtype = i.range := by
    rw [hfk,subgroupOf_map_subtype,inf_comm,hRU,hir]
  let a := f.ker.equivMapOfInjective R.subtype R.subtype_injective
  let b := MonoidHom.ofInjective hi
  let E : f.ker ≃* Multiplicative (BinaryPermutation.core (Fin 5)) :=
    a.trans ((MulEquiv.subgroupCongr hkm).trans b.symm)
  have hcoord (v : f.ker) : i (E v) = ((v : R) : D) :=
    MonoidHom.apply_ofInjective_symm hi _
  have hact (g : R) (v : f.ker) : E (MulAut.conjNormal g v) =
      Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (f g).val (E v).toAdd) := by
    apply hi
    rw [hcoord]
    change (g : D) * (v.val : D) * (g : D)⁻¹ = _
    change (g : D) * (v.val : D) * (g : D)⁻¹ =
      i (BinaryPermutation.AlternatingFiveExtension.coreAction (q g.val) (E v))
    rw [he,hcoord]
  obtain ⟨F,hF,_⟩ := BinaryPermutation.AlternatingFiveExtension.exists_marked_equiv f hf E hact
  let s : alternatingGroup (Fin 5) →* D :=
    R.subtype.comp (F.symm.toMonoidHom.comp SemidirectProduct.inr)
  have hsq : q.comp s = (alternatingGroup (Fin 5)).subtype := by
    apply MonoidHom.ext
    intro g
    have hh := hF (F.symm (SemidirectProduct.inr g))
    rw [F.apply_symm_apply] at hh
    exact congrArg Subtype.val hh.symm
  let P := BinaryPermutation.AlternatingFiveFlag.four
  have hp : ∀ x : P, x ^ 2 = 1 := by decide +kernel
  let : IsMulCommutative P := ⟨⟨fun a b => by
    have hh : ∀ a b : P, a * b = b * a := by decide +kernel
    exact hh a b⟩⟩
  let : IsElementaryAbelian 2 P := ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp⟩
  let P' := P.subgroupOf (alternatingGroup (Fin 5))
  let : IsElementaryAbelian 2 P' := IsElementaryAbelian.subgroupOf BinaryPermutation.AlternatingFiveFlag.four_even
  refine ⟨P'.map s,IsElementaryAbelian.map s,?_,?_⟩
  · rintro x ⟨p,hp,rfl⟩
    exact (F.symm (SemidirectProduct.inr p)).property
  · rw [map_map,hsq,map_subgroupOf_eq_of_le BinaryPermutation.AlternatingFiveFlag.four_even]
    exact BinaryPermutation.AlternatingFiveFlag.four_card
end BinaryPermutation.AlternatingFiveExtension
