module
public import Theory.Representation.BinaryAlternatingFiveExtension.MarkedAlternating
public import Theory.SpecificGroups.AlternatingFiveSquareGeneratorKernel
public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# Residual lifts over a small extension of the natural five-point kernel

Suppose a group acts onto S₅, its two-residual maps onto A₅, and its
normal natural sixteen lies in that residual. If the kernel has order at
most thirty-two and an elementary subgroup has image four, then the
residual kernel is exactly the natural sixteen. Indeed, a larger residual
kernel would be the full kernel. Its quotient by the natural sixteen is
central of order two, while the elementary four-image supplies a nontrivial
even involution. The perfect A₅ central-cover theorem rules this out.

The marked natural A₅ extension then splits. Its even four-group gives an
actual elementary subgroup of the original residual, retaining the same
quotient map. This uses a four-image subgroup in addition to the kernel
bound; it does not assert lifting through an arbitrary two-core.

Source application: Aschbacher--Smith 13.2.8(1), printed p.880, through the
original two-component comparison; the cover input is C.5.6(7), p.159.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace BinaryPermutation.AlternatingFiveExtension
variable {D : Type*} [Group D] [Finite D]

private theorem commutator_le_of_small_quotient (N W : Subgroup D) [N.Normal] [W.Normal]
    (hW : W ≤ N) (hWcard : Nat.card W = 16) (hNcard : Nat.card N ≤ 32) :
    ⁅N,⊤⁆ ≤ W := by
  let π := QuotientGroup.mk' W
  have hh := IsElementaryAbelian.card_inf_ker_mul_card_map N π
  rw [QuotientGroup.ker_mk', inf_of_le_right hW, hWcard] at hh
  have hp : 0 < Nat.card (N.map π) := Nat.card_pos
  have hc : Nat.card (N.map π) = 1 ∨ Nat.card (N.map π) = 2 := by omega
  have hcent : N.map π ≤ center (D ⧸ W) := by
    rcases hc with hc | hc
    · rw [Subgroup.card_eq_one.mp hc]
      exact bot_le
    · exact central_of_normal_card_two (N.map π) hc
  have hz : ⁅N.map π,⊤⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hcent.trans (center_le_centralizer _))
  have hm : (⁅N,(⊤ : Subgroup D)⁆).map π = ⊥ := by
    rw [map_commutator, map_top_of_surjective _ (QuotientGroup.mk'_surjective W)]
    exact hz
  simpa only [π,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hm

/-- A four-image elementary subgroup detects the whole residual kernel
when the prescribed natural sixteen has index at most two in the kernel. -/
theorem residual_kernel_eq_of_small_kernel
    (q : D →* Equiv.Perm (Fin 5))
    (hk : IsPGroup 2 q.ker)
    (hr : (pResidual 2 D).map q = alternatingGroup (Fin 5))
    (U : Subgroup D) [U.Normal] (hU : U ≤ q.ker)
    (hUR : U ≤ pResidual 2 D) (hUcard : Nat.card U = 16)
    (hsmall : Nat.card q.ker ≤ 32)
    (B : Subgroup D) [IsElementaryAbelian 2 B] (hBcard : Nat.card (B.map q) = 4) :
    pResidual 2 D ⊓ q.ker = U := by
  let R := pResidual 2 D
  have hURQ : U ≤ R ⊓ q.ker := le_inf hUR hU
  by_cases hsmallR : Nat.card (R ⊓ q.ker : Subgroup D) ≤ 16
  · exact (eq_of_le_of_card_ge hURQ (by rwa [hUcard])).symm
  have hRQcard : Nat.card (R ⊓ q.ker : Subgroup D) = 32 := by
    have hd := card_dvd_of_le hURQ
    rw [hUcard] at hd
    obtain ⟨n,hn⟩ := hd
    have hb := (card_le_of_le (show R ⊓ q.ker ≤ q.ker from inf_le_right)).trans hsmall
    omega
  have hQR : q.ker ≤ R := by
    have he : R ⊓ q.ker = q.ker := eq_of_le_of_card_ge inf_le_right (by rwa [hRQcard])
    exact he.ge.trans inf_le_left
  have hRc : (alternatingGroup (Fin 5)).comap q = R := by
    rw [←hr,comap_map_eq,sup_eq_left.mpr hQR]
  let f : R →* alternatingGroup (Fin 5) :=
    (q.comp R.subtype).codRestrict _ (fun x => hr ▸ mem_map_of_mem q x.property)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨x,hx,he⟩ := hr.ge a.property
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  have hfk : f.ker = q.ker.subgroupOf R := by
    ext x
    exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
  let A := U.subgroupOf R
  let : A.Normal := normal_subgroupOf_of_le_normalizer (U.normalizer_eq_top ▸ le_top)
  have hA : A ≤ f.ker := by rw [hfk]; exact fun x hx => hU hx
  let C := B.subgroupOf R
  have hC : C.map f ≠ ⊥ := by
    intro hz
    have hmap : (B.map q) ⊓ alternatingGroup (Fin 5) = ⊥ := by
      apply bot_unique
      rintro x ⟨⟨b,hb,rfl⟩,heven⟩
      have hbR : b ∈ R := hRc.le heven
      have hbc : (⟨b,hbR⟩ : R) ∈ C := hb
      have hh := mem_map_of_mem f hbc
      rw [hz,mem_bot] at hh
      exact congrArg Subtype.val hh
    have hi := (alternatingGroup (Fin 5)).relIndex_dvd_index_of_normal (B.map q)
    rw [alternatingGroup.index_eq_two] at hi
    have he : (alternatingGroup (Fin 5)).relIndex (B.map q) = 4 := by
      rw [←inf_relIndex_left (B.map q) (alternatingGroup (Fin 5)),hmap,relIndex_bot_left,hBcard]
    rw [he] at hi
    norm_num at hi
  have hcomm := commutator_le_of_small_quotient q.ker U hU hUcard hsmall
  have hCA : ⁅f.ker,C⁆ ≤ A := by
    intro x hx
    have hh := mem_map_of_mem R.subtype hx
    rw [map_commutator,hfk,map_subgroupOf_eq_of_le hQR] at hh
    exact hcomm ((commutator_mono le_rfl le_top) hh)
  have hsq : ∀ r ∈ C, r ^ 2 ∈ A := by
    intro r hr
    have hh : (r : D)^2 = 1 := elemPow_eq_one_of_isElementaryAbelian (r : D) hr
    have he : r^2 = 1 := Subtype.ext hh
    rw [he]
    exact A.one_mem
  have he := alternatingGroup.kernel_eq_of_square_normal_generator f hf
    (hfk ▸ hk.comap_subtype) (isPPerfect_pResidual 2) A C hA hC hCA hsq
  have hm := congrArg (map R.subtype) he
  rw [hfk,map_subgroupOf_eq_of_le hQR,map_subgroupOf_eq_of_le hUR] at hm
  exact (inf_eq_right.mpr hQR).trans hm


/-- Split the identified natural residual kernel and retain an elementary
four-group under the original symmetric-five quotient map. -/
theorem exists_residual_four_of_small_kernel
    (q : D →* Equiv.Perm (Fin 5))
    (hk : IsPGroup 2 q.ker)
    (hr : (pResidual 2 D).map q = alternatingGroup (Fin 5))
    (U : Subgroup D) [U.Normal] (hU : U ≤ q.ker)
    (hUR : U ≤ pResidual 2 D) (hUcard : Nat.card U = 16)
    (hsmall : Nat.card q.ker ≤ 32)
    (B : Subgroup D) [IsElementaryAbelian 2 B] (hBcard : Nat.card (B.map q) = 4)
    (i : Multiplicative (BinaryPermutation.core (Fin 5)) →* D)
    (hi : Function.Injective i) (hir : i.range = U)
    (he : ∀ (g : D) (v : Multiplicative (BinaryPermutation.core (Fin 5))),
      i (BinaryPermutation.AlternatingFiveExtension.coreAction (q g) v) = g * i v * g⁻¹) :
    ∃ A : Subgroup D, IsElementaryAbelian 2 A ∧ A ≤ pResidual 2 D ∧
      Nat.card (A.map q) = 4 := by
  have hRU := residual_kernel_eq_of_small_kernel q hk hr U hU hUR hUcard hsmall B hBcard
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
