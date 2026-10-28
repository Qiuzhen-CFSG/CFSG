module
public import Theory.Representation.AlternatingFiveInnerDisplacement
public import Theory.SpecificGroups.Alternating.FiveExtensionAction
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.Representation.PerfectInvolutionExtension
public import Theory.Representation.PSL3Two.ResidualFFForms.ConstituentBudget.InvolutionBound
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.Representation.BinaryIrreducibleCentralizer
public import Theory.Representation.BinaryOffender.ThreeConjugateNormalizer
public import Theory.Representation.BinaryFullLinearRecognition
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Theory.ElementaryAbelian.Injective

/-!
# Simple normal factors with a rank-two fixed-hyperplane actor

A faithful elementary actor on a normal A₅ which fixes a hyperplane has
order at most two: its sign kernel would contain an inner involution, whose
order-five commutator forces displacement at least two. For a normal SL₃(2),
small displacement preserves every perfect-group constituent. The rank-two
actor has a nontrivial inner involution, since the outer group has order two.
Schur's lemma identifies its operator with the inner representative. Three
conjugate involutions generate SL₃(2), forcing dimension three and an actual
natural-action equivalence.

These results retain the original representation, relative normal subgroup,
and actor; no irreducible-module classification is assumed.
Source: Aschbacher--Smith 13.1.9, printed p.871, after equality in (*).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.Alternating.FiveExtensionAction
namespace Representation.AlternatingFiveHyperplane
variable {G V : Type*} [Group G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem actor_card_le_two (ρ : Representation (ZMod 2) G V)
    (K A : Subgroup G) [K.Normal] [IsElementaryAbelian 2 A]
    (e : K ≃* alternatingGroup (Fin 5))
    (hf : Function.Injective (ρ.comp K.subtype))
    (hc : A ⊓ centralizer (K : Set G) = ⊥)
    (hd : fixedCodim ρ A ≤ 1) : Nat.card A ≤ 2 := by
  let b : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))
  let f : G →* Equiv.Perm (Fin 5) := b.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal)
  let q : A →* ℤˣ := Equiv.Perm.sign.comp (f.comp A.subtype)
  have hq : Function.Injective q := by
    apply (injective_iff_map_eq_one q).mpr
    intro a ha
    have heven : f a ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.mpr ha
    let k : K := e.symm ⟨f a,heven⟩
    have hk0 : f k = e k := by
      apply b.injective
      change b (b.symm _) = MulAut.conjNormal (e k).val
      rw [b.apply_symm_apply]
      apply MulEquiv.ext
      intro y
      apply Subtype.ext
      change (e (k * e.symm y * k⁻¹)).val = (e k).val * y.val * (e k).val⁻¹
      simp
    have hk : f k = f a := hk0.trans (congrArg Subtype.val (e.apply_symm_apply _))
    have hconj : (MulAut.conjNormal (a : G) : MulAut K) = MulAut.conj k := by
      apply (MulAut.congr e).injective
      apply b.symm.injective
      simpa only [f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
        MulAut.conjNormal_val] using hk.symm
    have hz : center K = ⊥ := by
      apply bot_unique
      intro x hx
      apply mem_bot.mpr
      apply e.injective
      have hec : e x ∈ center (alternatingGroup (Fin 5)) := by
        rw [mem_center_iff]
        intro y
        obtain ⟨z,rfl⟩ := e.surjective y
        exact (map_mul e _ _).symm.trans ((congrArg e (mem_center_iff.mp hx z)).trans (map_mul e _ _))
      simpa only [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 5)),mem_bot,map_one] using hec
    have hk2 : k ^ 2 = 1 := by
      apply MulAut.conj_injective_of_center_eq_bot hz
      rw [map_pow,←hconj,←map_pow,
        elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : G) a.property,map_one,map_one]
    let σ : Representation (ZMod 2) (alternatingGroup (Fin 5)) V := ρ.comp (K.subtype.comp e.symm.toMonoidHom)
    have hσ : Function.Injective σ := hf.comp e.symm.injective
    have hinner (b : alternatingGroup (Fin 5)) :
        ρ.asGroupHom a * σ.asGroupHom b * (ρ.asGroupHom a)⁻¹ =
          σ.asGroupHom (e k * b * (e k)⁻¹) := by
      have hh := congrArg (fun α : MulAut K => (α (e.symm b) : G)) hconj
      change (a : G) * (e.symm b : G) * (a : G)⁻¹ =
        (k : G) * (e.symm b : G) * (k : G)⁻¹ at hh
      apply Units.ext
      change ρ (a : G) * ρ (e.symm b : G) * ρ (a : G)⁻¹ =
        ρ (e.symm (e k * b * (e k)⁻¹) : G)
      rw [←map_mul,←map_mul,hh]
      simp only [map_mul,map_inv,e.symm_apply_apply,Subgroup.coe_mul,Subgroup.coe_inv]
    have hr : Module.finrank (ZMod 2) (ρ (a : G) - LinearMap.id).range ≤ 1 := by
      rw [←fixedCodim_zpowers_eq_displacement_rank]
      exact (NaturalTensor.fixedCodim_mono ρ (zpowers_le.mpr a.property)).trans hd
    have he1 := AlternatingFiveInvolutionDisplacement.inner_involution_eq_one_of_rank_le_one
      σ hσ (ρ.asGroupHom a) (e k) (by rw [←map_pow,hk2,map_one]) hinner hr
    have hk1 : k = 1 := e.injective (he1.trans e.map_one.symm)
    have haC : (a : G) ∈ centralizer (K : Set G) := by
      rw [←MulAut.conjNormal_ker_eq_centralizer]
      change MulAut.conjNormal (H := K) (a : G) = 1
      simpa only [hk1,map_one] using hconj
    apply Subtype.ext
    exact mem_bot.mp (hc ▸ (show (a : G) ∈ A ⊓ centralizer (K : Set G) from ⟨a.property,haC⟩))
  exact (Nat.card_le_card_of_injective q hq).trans (by simp [Nat.card_eq_fintype_card])

variable {Q : Type*} [Group Q]
theorem actor_card_le_two_in_join (K A : Subgroup Q) [K.Normal]
    (σ : Representation (ZMod 2) ↥(K ⊔ A) V)
    (he : IsElementaryAbelian 2 A)
    (hfK₀ : Function.Injective (σ.comp (inclusion (show K ≤ K ⊔ A from le_sup_left))))
    (hf : A ⊓ centralizer (K : Set Q) = ⊥)
    (e : K ≃* alternatingGroup (Fin 5))
    (hd : fixedCodim σ (A.subgroupOf (K ⊔ A)) ≤ 1) : Nat.card A ≤ 2 := by
  let E := K ⊔ A
  let KE := K.subgroupOf E
  let AE := A.subgroupOf E
  let := he
  let : IsElementaryAbelian 2 AE := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe (show A ≤ E from le_sup_right)).toMonoidHom
    (subgroupOfEquivOfLe (show A ≤ E from le_sup_right)).injective
  have hfK : Function.Injective (σ.comp KE.subtype) :=
    hfK₀.comp (subgroupOfEquivOfLe (show K ≤ E from le_sup_left)).injective
  have hfA : AE ⊓ centralizer (KE : Set E) = ⊥ := by
    apply bot_unique
    intro a ha
    apply mem_bot.mpr
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hf]
    refine ⟨ha.1,?_⟩
    intro k hk
    exact congrArg Subtype.val (ha.2 ⟨k,mem_sup_left hk⟩ hk)
  have hb := actor_card_le_two σ KE AE
    ((subgroupOfEquivOfLe (show K ≤ E from le_sup_left)).trans e)
    hfK hfA hd
  rwa [Nat.card_congr (subgroupOfEquivOfLe (show A ≤ E from le_sup_right)).toEquiv] at hb
end Representation.AlternatingFiveHyperplane

namespace Representation.PerfectInvolutionExtension
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem supplement_restriction_irreducible (ρ : Representation (ZMod 2) G V)
    (hρ : ρ.IsIrreducible) (K A : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (hn : ¬ K ≤ ρ.ker) (hgen : K ⊔ A = ⊤) (hd : fixedCodim ρ A ≤ 2) :
    IsIrreducible (ρ.comp K.subtype) := by
  let := hρ
  let := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨J,hJ⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp K.subtype)
  have hK : K ≤ subspaceStabilizer ρ J.toSubmodule :=
    le_subspaceStabilizer ρ J.toSubmodule
      (fun k hk w hw => J.apply_mem_toSubmodule ⟨k,hk⟩ hw)
  have hA : A ≤ subspaceStabilizer ρ J.toSubmodule := by
    intro a ha
    have hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 2 := by
      rw [←fixedCodim_zpowers_eq_displacement_rank]
      exact (NaturalTensor.fixedCodim_mono ρ (zpowers_le.mpr ha)).trans hd
    have hi : J.toSubmodule.map (ρ a) = J.toSubmodule :=
      map_constituent_eq_self_of_displacement_lt ρ K a J hJ
        (lt_of_le_of_lt hr (by have := constituent_dimension ρ hρ K hn J hJ; omega))
    intro w
    constructor
    · intro hw
      obtain ⟨x,hx,he⟩ := hi.ge hw
      exact (ρ.apply_bijective a).injective he ▸ hx
    · intro hw
      exact hi.le (Submodule.mem_map_of_mem hw)
  have hall : ⊤ ≤ subspaceStabilizer ρ J.toSubmodule := hgen ▸ sup_le hK hA
  let B : Subrepresentation ρ := {
    toSubmodule := J.toSubmodule
    apply_mem_toSubmodule g w hw := (hall (mem_top g) w).mpr hw }
  have hB : B ≠ ⊥ := fun he =>
    ((Subrepresentation.irreducible_iff_isAtom J).mp hJ).ne_bot
      (Subrepresentation.toSubmodule_injective (congrArg (fun C : Subrepresentation ρ => C.toSubmodule) he))
  have ht : B = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top B).resolve_left hB
  have hJtop : J = ⊤ := Subrepresentation.toSubmodule_injective
    (congrArg (fun C : Subrepresentation ρ => C.toSubmodule) ht)
  exact isSimpleOrder_iff_isAtom_top.mpr
    (hJtop ▸ (Subrepresentation.irreducible_iff_isAtom J).mp hJ)
end Representation.PerfectInvolutionExtension

namespace Representation.BinaryHyperplane
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Irreducibility determines the operator of an inner involution. -/
theorem inner_operator_eq (ρ : Representation (ZMod 2) G V)
    (K : Subgroup G) [K.Normal] [IsIrreducible (ρ.comp K.subtype)]
    (a : G) (k : K) (ha : a ^ 2 = 1) (hk : k ^ 2 = 1)
    (hi : MulAut.conjNormal (H := K) a = MulAut.conj k) : ρ a = ρ k := by
  let σ : Representation (ZMod 2) K V := ρ.comp K.subtype
  let τ : Representation (ZMod 2) (Module.End (ZMod 2) V)ˣ V := Units.coeHom _
  let : IsIrreducible (τ.comp (actionImage σ).subtype) :=
    imageRepresentation_isIrreducible σ inferInstance
  let t := ρ.asGroupHom a
  let u := ρ.asGroupHom k
  have hu2 : u ^ 2 = 1 := by
    change ρ.asGroupHom (k : G) ^ 2 = 1
    rw [←map_pow,show (k : G)^2=1 from congrArg Subtype.val hk,map_one]
  have ht2 : t ^ 2 = 1 := by rw [←map_pow,ha,map_one]
  have hconj (b : K) : t * σ.asGroupHom b * t⁻¹ = u * σ.asGroupHom b * u⁻¹ := by
    have hh := congrArg (fun α : MulAut K => (α b : G)) hi
    change a * (b : G) * a⁻¹ = (k : G) * (b : G) * (k : G)⁻¹ at hh
    change ρ.asGroupHom a * ρ.asGroupHom (b : G) * (ρ.asGroupHom a)⁻¹ =
      ρ.asGroupHom (k : G) * ρ.asGroupHom (b : G) * (ρ.asGroupHom (k : G))⁻¹
    simpa only [map_mul,map_inv] using congrArg ρ.asGroupHom hh
  have htuc : Commute t u := by
    have hh := hconj k
    change t * u * t⁻¹ = u * u * u⁻¹ at hh
    rw [mul_inv_cancel_right] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hx2 : (t * u⁻¹)^2 = 1 := by
    rw [htuc.inv_right.mul_pow,ht2,inv_pow,hu2,inv_one,mul_one]
  have hxc : t * u⁻¹ ∈ centralizer (actionImage σ : Set (Module.End (ZMod 2) V)ˣ) := by
    rintro b ⟨k',rfl⟩
    have hh := hconj k'
    rw [htuc.inv_right.eq]
    apply (mul_inv_eq_iff_eq_mul.mp ?_).symm
    calc
      (u⁻¹ * t) * σ.asGroupHom k' * (u⁻¹ * t)⁻¹ =
          u⁻¹ * (t * σ.asGroupHom k' * t⁻¹) * u := by group
      _ = σ.asGroupHom k' := by rw [hh]; group
  have he := BinaryIrreducibleCentralizer.centralizing_square_one_eq_one τ (actionImage σ)
    (fun _ _ h => Units.ext h) hx2 hxc
  exact congrArg Units.val (mul_inv_eq_one.mp he)
end Representation.BinaryHyperplane

namespace Representation.BinaryHyperplane
variable {G V : Type*} [Group G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem linear_three_degree (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
    (K A : Subgroup G) [K.Normal] [IsElementaryAbelian 2 A]
    (e : K ≃* Matrix.PSL3Two.SL)
    (hf : Function.Injective (ρ.comp K.subtype))
    (hc : A ⊓ centralizer (K : Set G) = ⊥) (hr : 2 < Nat.card A)
    (hgen : K ⊔ A = ⊤) (hd : fixedCodim ρ A ≤ 1) :
    Module.finrank (ZMod 2) V = 3 := by
  let : Group.IsPerfect Matrix.PSL3Two.SL := Atlas.sl_perfect 3 (by decide)
  let : Nontrivial Matrix.PSL3Two.SL := ⟨⟨Matrix.SpecialLinearGroup.transvection
    (by decide : (0 : Fin 3) ≠ 1) (1 : ZMod 2),1,by decide⟩⟩
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Nontrivial K := e.symm.injective.nontrivial
  have hn : ¬ K ≤ ρ.ker := by
    intro hh
    obtain ⟨k,hk⟩ := exists_ne (1 : K)
    exact hk (hf ((hh k.property).trans (ρ.comp K.subtype).map_one.symm))
  let hiK := PerfectInvolutionExtension.supplement_restriction_irreducible
    ρ inferInstance K A hn hgen (hd.trans (by decide))
  let σ : Representation (ZMod 2) Matrix.PSL3Two.SL V :=
    ρ.comp (K.subtype.comp e.symm.toMonoidHom)
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp K.subtype)).mpr hiK
  have hfσ : Function.Injective σ := hf.comp e.symm.injective
  let q : A →* MulAut.Outer Matrix.PSL3Two.SL :=
    (QuotientGroup.mk' (MulAut.innerSubgroup Matrix.PSL3Two.SL)).comp
      ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal.comp A.subtype))
  have hqn : ¬ Function.Injective q := by
    intro hh
    have hb := Nat.card_le_card_of_injective q hh
    rw [Matrix.PSL3Two.Automorphisms.card_outer_sl] at hb
    omega
  obtain ⟨a,ha,ha1⟩ : ∃ a : A, q a = 1 ∧ a ≠ 1 := by
    by_contra! hh
    exact hqn ((injective_iff_map_eq_one q).mpr hh)
  have hinner : (MulAut.congr e) (MulAut.conjNormal (H := K) (a : G)) ∈
      MulAut.innerSubgroup Matrix.PSL3Two.SL := (QuotientGroup.eq_one_iff _).mp ha
  obtain ⟨s,hs⟩ := hinner
  let k := e.symm s
  have hk : MulAut.conjNormal (H := K) (a : G) = MulAut.conj k := by
    apply (MulAut.congr e).injective
    rw [MulAut.congr_conj,e.apply_symm_apply]
    exact hs.symm
  have hs2 : s ^ 2 = 1 := by
    apply MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot
    rw [map_pow,hs,←map_pow,←map_pow,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : G) a.property,map_one,map_one,map_one]
  have hk2 : k ^ 2 = 1 := by rw [←map_pow,hs2,map_one]
  have hs1 : s ≠ 1 := by
    intro h1
    have haC : (a : G) ∈ centralizer (K : Set G) := by
      rw [←MulAut.conjNormal_ker_eq_centralizer]
      change MulAut.conjNormal (H := K) (a : G) = 1
      simpa only [k,h1,map_one] using hk
    apply ha1
    apply Subtype.ext
    exact mem_bot.mp (hc ▸ (show (a : G) ∈ A ⊓ centralizer (K : Set G) from ⟨a.property,haC⟩))
  have hact := inner_operator_eq ρ K (a : G) k
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : G) a.property) hk2 hk
  have hds : fixedCodim σ (zpowers s) ≤ 1 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    change Module.finrank (ZMod 2) (ρ (k : G) - LinearMap.id).range ≤ 1
    rw [←hact,←fixedCodim_zpowers_eq_displacement_rank]
    exact (NaturalTensor.fixedCodim_mono ρ (zpowers_le.mpr a.property)).trans hd
  have hfull := subspaceCommutator_top_eq_top_of_faithful_irreducible σ hfσ inferInstance
  have hb := BinaryLinearThree.ResidualFFForms.ConstituentBudget.finrank_le_three_mul_involution_fixedCodim
    σ hfull s hs2 hs1
  have hlo : 3 ≤ Module.finrank (ZMod 2) V := by
    by_contra! hdim
    apply hs1
    apply hfσ
    apply LinearMap.ext
    intro v
    exact (PerfectInvolutionExtension.small_action_trivial σ (by omega) s v).trans (by simp)
  omega
end Representation.BinaryHyperplane
open scoped MatrixGroups
namespace Representation.BinaryHyperplane
variable {Q V : Type*} [Group Q] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem linear_three_natural_in_join (K A : Subgroup Q) [K.Normal]
    (σ : Representation (ZMod 2) ↥(K ⊔ A) V) [IsIrreducible σ]
    (he : IsElementaryAbelian 2 A)
    (hfK₀ : Function.Injective (σ.comp (inclusion (show K ≤ K ⊔ A from le_sup_left))))
    (hf : A ⊓ centralizer (K : Set Q) = ⊥) (hr : 2 < Nat.card A)
    (e : K ≃* Matrix.PSL3Two.SL)
    (hd : fixedCodim σ (A.subgroupOf (K ⊔ A)) ≤ 1) :
    ∃ (e' : K ≃* SL(3,ZMod 2)) (f : V ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)),
      ∀ k v, f (σ (inclusion (show K ≤ K ⊔ A from le_sup_left) k) v) =
        (e' k).val.mulVec (f v) := by
  let E := K ⊔ A
  let KE := K.subgroupOf E
  let AE := A.subgroupOf E
  let := he
  let : IsElementaryAbelian 2 AE := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe (show A ≤ E from le_sup_right)).toMonoidHom
    (subgroupOfEquivOfLe (show A ≤ E from le_sup_right)).injective
  have hfK : Function.Injective (σ.comp KE.subtype) :=
    hfK₀.comp (subgroupOfEquivOfLe (show K ≤ E from le_sup_left)).injective
  have hfA : AE ⊓ centralizer (KE : Set E) = ⊥ := by
    apply bot_unique
    intro a ha
    apply mem_bot.mpr
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hf]
    refine ⟨ha.1,?_⟩
    intro k hk
    exact congrArg Subtype.val (ha.2 ⟨k,mem_sup_left hk⟩ hk)
  have hr' : 2 < Nat.card AE := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe (show A ≤ E from le_sup_right)).toEquiv]
  have hgen : KE ⊔ AE = ⊤ := by
    rw [←subgroupOf_sup le_sup_left le_sup_right]
    exact subgroupOf_self E
  have hdim := linear_three_degree σ KE AE
    ((subgroupOfEquivOfLe (show K ≤ E from le_sup_left)).trans e) hfK hfA hr' hgen hd
  let : Finite K := Finite.of_equiv Matrix.PSL3Two.SL e.symm.toEquiv
  exact BinaryFullLinearRecognition.exists_natural_equiv
    (σ.comp (inclusion (show K ≤ K ⊔ A from le_sup_left))) hfK₀ e hdim
end Representation.BinaryHyperplane

