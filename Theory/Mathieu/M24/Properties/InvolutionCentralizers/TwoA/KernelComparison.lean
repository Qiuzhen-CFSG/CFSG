module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.KernelSections
public import Theory.Representation.PSL3Two.ResidualFFForms.ConstituentBudget.DualBounds
public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.GroupTheory.PGroup.NormalExtraspecialDerivedCenter

/-!
# Comparing a subgroup with the literal native kernel

Counting the natural and dual sections bounds every subgroup whose
commutators lie in the marked involution. The two fixed spaces refer to
the same actual quotient image. This is the same-kernel comparison needed
for an extraspecial subgroup transported into the full point centralizer.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace Sporadic.Mathieu.M24InvolutionCentralizers.TwoA.KernelComparison
open KernelSections

private abbrev mark : centralizer2A :=
  ⟨involution2A,mem_centralizer_singleton_iff.mpr rfl⟩

private theorem mark_le_translation : zpowers mark≤translationKernel :=
  zpowers_le.mpr markedElement_mem_core

private theorem mark_card : Nat.card (zpowers mark)=2 := by
  rw [Nat.card_zpowers]
  exact (orderOf_injective centralizer2A.subtype centralizer2A.subtype_injective mark).symm.trans involution2A_order

private theorem natural_image_bound (P : Subgroup centralizer2A)
    (hc : ⁅P,P⁆≤zpowers mark) :
    Nat.card ((P.subgroupOf translationKernel).map natural) ≤
      Nat.card (fixedSpace BinaryLinearThree.W (P.map actor)) := by
  let f : (P.subgroupOf translationKernel).map natural →
      fixedSpace BinaryLinearThree.W (P.map actor) := fun v => ⟨v.val.toAdd,by
    obtain ⟨u,hu,huv⟩ := v.property
    rw [←huv]
    intro a
    obtain ⟨g,hg,hga⟩ := a.property
    change BinaryLinearThree.W a.val (natural u).toAdd = _
    rw [←hga]
    have hm : natural (MulAut.conjNormal g u*u⁻¹)=1 := by
      apply (natural_ker _).mpr
      exact hc (commutator_mem_commutator hg hu)
    rw [map_mul,map_inv,mul_inv_eq_one] at hm
    exact (natural_conjugation g u).symm.trans
      (congrArg Multiplicative.toAdd hm)⟩
  exact Nat.card_le_card_of_injective f (fun x y h =>
    Subtype.ext (Multiplicative.toAdd.injective
      (show x.val.toAdd=y.val.toAdd from
        congrArg (fun v : fixedSpace BinaryLinearThree.W (P.map actor) => v.val) h)))

private theorem dual_image_bound (P : Subgroup centralizer2A)
    (hc : ⁅P,P⁆≤zpowers mark) :
    Nat.card ((P.subgroupOf kernel).map dual) ≤
      Nat.card (fixedSpace BinaryLinearThree.W.dual (P.map actor)) := by
  let : Finite (Module.Dual (ZMod 2) BinaryLinearThree.Vector) := Module.finite_of_finite (ZMod 2)
  let f : (P.subgroupOf kernel).map dual →
      fixedSpace BinaryLinearThree.W.dual (P.map actor) := fun v => ⟨v.val.toAdd,by
    obtain ⟨q,hq,hqv⟩ := v.property
    rw [←hqv]
    intro a
    obtain ⟨g,hg,hga⟩ := a.property
    change BinaryLinearThree.W.dual a.val (dual q).toAdd = _
    rw [←hga]
    have hm : dual (MulAut.conjNormal g q*q⁻¹)=1 := by
      apply (dual_ker _).mpr
      exact mark_le_translation (hc (commutator_mem_commutator hg hq))
    rw [map_mul,map_inv,mul_inv_eq_one] at hm
    exact (dual_conjugation g q).symm.trans
      (congrArg Multiplicative.toAdd hm)⟩
  exact Nat.card_le_card_of_injective f (fun x y h =>
    Subtype.ext (Multiplicative.toAdd.injective
      (show x.val.toAdd=y.val.toAdd from
        congrArg (fun v : fixedSpace BinaryLinearThree.W.dual (P.map actor) => v.val) h)))

/-- Both literal sections contribute to the bound, without a splitting premise. -/
theorem card_le_paired_fixed (P : Subgroup centralizer2A)
    (hc : ⁅P,P⁆≤zpowers
      (⟨involution2A,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer2A)) :
    Nat.card P ≤ 2 * Nat.card (P.map actor) *
      Nat.card (fixedSpace BinaryLinearThree.W (P.map actor)) *
      Nat.card (fixedSpace BinaryLinearThree.W.dual (P.map actor)) := by
  have hn := IsElementaryAbelian.card_inf_ker_mul_card_map
    (P.subgroupOf translationKernel) natural
  have hnk : Nat.card ((P.subgroupOf translationKernel)⊓natural.ker : Subgroup translationKernel)≤2 := by
    let f : ((P.subgroupOf translationKernel)⊓natural.ker : Subgroup translationKernel) →
        zpowers mark := fun u => ⟨u.val.val,(natural_ker u.val).mp u.property.2⟩
    exact (Nat.card_le_card_of_injective f (fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun v : zpowers mark => v.val) h)))).trans_eq mark_card
  have ht : Nat.card (P.subgroupOf translationKernel)≤
      2*Nat.card (fixedSpace BinaryLinearThree.W (P.map actor)) := by
    rw [←hn]
    exact Nat.mul_le_mul hnk (natural_image_bound P hc)
  have hd := IsElementaryAbelian.card_inf_ker_mul_card_map (P.subgroupOf kernel) dual
  let e : ((P.subgroupOf kernel)⊓dual.ker : Subgroup kernel)≃*
      P.subgroupOf translationKernel := {
    toFun x := ⟨⟨x.val.val,(dual_ker x.val).mp x.property.2⟩,x.property.1⟩
    invFun x := ⟨⟨x.val.val,translationKernel_le_kernel x.val.property⟩,
      x.property,(dual_ker _).mpr x.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  rw [Nat.card_congr e.toEquiv] at hd
  have hk : Nat.card (P.subgroupOf kernel) ≤
      (2*Nat.card (fixedSpace BinaryLinearThree.W (P.map actor))) *
        Nat.card (fixedSpace BinaryLinearThree.W.dual (P.map actor)) := by
    rw [←hd]
    exact Nat.mul_le_mul ht (dual_image_bound P hc)
  have ha := IsElementaryAbelian.card_inf_ker_mul_card_map P actor
  rw [actor_ker] at ha
  let eK : (P⊓kernel : Subgroup centralizer2A)≃*P.subgroupOf kernel := {
    toFun x := ⟨⟨x.val,x.property.2⟩,x.property.1⟩
    invFun x := ⟨x.val.val,x.property,x.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  rw [Nat.card_congr eK.toEquiv] at ha
  rw [←ha]
  calc
    _≤((2*Nat.card (fixedSpace BinaryLinearThree.W (P.map actor)))*
      Nat.card (fixedSpace BinaryLinearThree.W.dual (P.map actor)))*Nat.card (P.map actor) :=
        Nat.mul_le_mul_right _ hk
    _=_ := by ac_rfl

private theorem paired_fixed_lt (A : Subgroup BinaryLinearThree.Group)
    (hA : IsElementaryTwo A) :
    Nat.card A * Nat.card (fixedSpace BinaryLinearThree.W A) *
      Nat.card (fixedSpace BinaryLinearThree.W.dual A) < 64 := by
  have hs := BinaryLinearThree.ResidualFFForms.ConstituentBudget.rank_lt_natural_add_dual_fixedCodim A hA
  have hn := fixedCodim_add_finrank BinaryLinearThree.W A
  have hd := fixedCodim_add_finrank BinaryLinearThree.W.dual A
  have hdim : Module.finrank (ZMod 2) BinaryLinearThree.Vector=3 := by
    rw [Module.finrank_pi,Fintype.card_fin]
  rw [hdim] at hn
  rw [Subspace.dual_finrank_eq,hdim] at hd
  have hlt : rank A+Module.finrank (ZMod 2) (fixedSpace BinaryLinearThree.W A)+
      Module.finrank (ZMod 2) (fixedSpace BinaryLinearThree.W.dual A)<6 := by omega
  rw [hA.card_eq_two_pow_rank,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace BinaryLinearThree.W A),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace BinaryLinearThree.W.dual A),
    Nat.card_zmod,←pow_add,←pow_add]
  exact (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mpr hlt

/-- Every subgroup of order at least 128 with the original central commutator
and square marking is contained in the specified kernel. -/
theorem le_kernel_of_marked_class_two (P : Subgroup centralizer2A)
    (hc : ⁅P,P⁆≤zpowers
      (⟨involution2A,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer2A))
    (hs : ∀ x∈P, x^2∈zpowers
      (⟨involution2A,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer2A))
    (hcard : 128≤Nat.card P) : P≤kernel := by
  let A := P.map actor
  have hz : zpowers mark≤actor.ker := by
    rw [actor_ker]
    exact mark_le_translation.trans translationKernel_le_kernel
  have hp (x : A) : x^2=1 := by
    apply Subtype.ext
    obtain ⟨g,hg,hgx⟩ := x.property
    change x.val^2=1
    rw [←hgx,←map_pow]
    exact hz (hs g hg)
  have hi (x : A) : x⁻¹=x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hp x)
  have he : IsElementaryAbelian 2 A := {
    toIsMulCommutative := ⟨⟨fun x y => by
      calc x*y=(x*y)⁻¹ := (hi _).symm
           _=y*x := by rw [mul_inv_rev,hi,hi]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }
  have hbot : A=⊥ := by
    by_contra hn
    have hlt := paired_fixed_lt A ⟨hn,he⟩
    have hb := card_le_paired_fixed P hc
    change Nat.card P≤2*Nat.card A*Nat.card (fixedSpace BinaryLinearThree.W A)*
      Nat.card (fixedSpace BinaryLinearThree.W.dual A) at hb
    nlinarith
  rw [←actor_ker]
  intro x hx
  have ha : actor x∈A := mem_map_of_mem _ hx
  rw [hbot] at ha
  exact ha

/-- An extraspecial subgroup of the same order and with the same embedded
center is the original native kernel, not merely an isomorphic subgroup. -/
theorem extraspecial_eq_kernel (P : Subgroup centralizer2A) [IsExtraspecial 2 P]
    (hcard : Nat.card P=128)
    (hcenter : (center P).map P.subtype=zpowers
      (⟨involution2A,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer2A)) : P=kernel := by
  have hc : ⁅P,P⁆≤zpowers mark := by
    rw [←map_subtype_commutator,IsExtraspecial.commutator_eq_center_two,hcenter]
  let : IsElementaryAbelian 2 (P⧸center P) := IsExtraspecial.quotient_elementary_abelian 2 P
  have hs (x : centralizer2A) (hx : x∈P) : x^2∈zpowers mark := by
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (P⧸center P))
      (QuotientGroup.mk' (center P) ⟨x,hx⟩)
    rw [←map_pow] at hh
    have hh : (⟨x,hx⟩ : P)^2∈center P := (QuotientGroup.eq_one_iff _).mp hh
    rw [←hcenter]
    exact mem_map_of_mem _ hh
  exact eq_of_le_of_card_ge (le_kernel_of_marked_class_two P hc hs hcard.ge)
    (by rw [hcard,kernel_card])

end Sporadic.Mathieu.M24InvolutionCentralizers.TwoA.KernelComparison
