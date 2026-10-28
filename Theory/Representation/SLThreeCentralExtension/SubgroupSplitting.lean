module

public import Theory.Representation.SLThreeCentralExtension.SylowSplitting
public import Theory.Representation.BinaryConjugationSection.CentralKernel
public import Theory.GroupTheory.NormalFourCentralizer
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Splitting an original elementary subgroup with a marked natural action

An invariant four-group U₀ in the original two-subgroup B₀ has centralizer
of index at most two. Restriction to A ≤ B₀ and passage to the marked
SL₃(2) quotient retain that index bound in the actual Sylow image of A.
Descended conjugation
and the original natural coordinates therefore satisfy the Sylow splitting
criterion. Transport back gives R = V × C_R(L), with |C_R(L)| = 2.

The kernel-centralization, rank-four, and commutator-containment hypotheses
are explicit; the theorem does not infer an action from group orders.
Source: Aschbacher–Smith 14.7.72, printed p.1076, manuscript of 1 March 2004.
-/

public section

open Subgroup Representation
open scoped IsMulCommutative
namespace BinaryLinearThree.NaturalExtension
variable {G : Type*} [_root_.Group G] [Finite G]

theorem natural_four_space_splits
    (L R V A B₀ U₀ : Subgroup G) [IsElementaryAbelian 2 R]
    (hVR : V ≤ R) (hAL : A ≤ L) (hAB : A ≤ B₀) (hU₀B : U₀ ≤ B₀)
    (hU₀R : U₀ ≤ R) (hNB : B₀ ≤ normalizer U₀)
    (hNR : L ≤ normalizer R) (hB : IsPGroup 2 B₀)
    (hfour : Nat.card U₀ = 4) (hRcard : Nat.card R = 16)
    (q : L →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (hk : ∀ l ∈ q.ker, (l : G) ∈ centralizer (R : Set G))
    (hNV : L ≤ normalizer V)
    (cV : V →* Multiplicative BinaryLinearThree.Vector)
    (hcV : Function.Bijective cV)
    (hcn : ∀ (l : L) (v : V),
      (cV ⟨l * v * (l : G)⁻¹,
        (mem_normalizer_iff.mp (hNV l.property) v).mp v.property⟩).toAdd =
      BinaryLinearThree.W (q l) (cV v).toAdd)
    (P : Sylow 2 BinaryLinearThree.Group)
    (hP : (q.comp (Subgroup.inclusion hAL)).range = (P : Subgroup _))
    (hcomm : ⁅R,L⁆ ≤ V) (u : U₀) (hu : (u : G) ∉ V) :
    R = V ⊔ (R ⊓ centralizer (L : Set G)) ∧
      Disjoint V (R ⊓ centralizer (L : Set G)) ∧
      Nat.card (R ⊓ centralizer (L : Set G) : Subgroup G) = 2 := by
  obtain ⟨ρ,hact⟩ := BinaryConjugationSection.exists_action_of_central_kernel L R hNR q hq hk
  let N : Subrepresentation ρ := {
    toSubmodule := AddSubgroup.toZModSubmodule 2 (V.subgroupOf R).toAddSubgroup
    apply_mem_toSubmodule := by
      intro g r hr
      obtain ⟨l,rfl⟩ := hq g
      change ((ρ (q l) r).toMul : G) ∈ V
      rw [hact l r]
      exact (mem_normalizer_iff.mp (hNV l.property) r.toMul).mp hr }
  let f₀ : N.toSubmodule →+ BinaryLinearThree.Vector := {
    toFun := fun r => (cV ⟨r.val.toMul,r.property⟩).toAdd
    map_zero' := congrArg Multiplicative.toAdd cV.map_one
    map_add' r s := congrArg Multiplicative.toAdd
      (cV.map_mul ⟨r.val.toMul,r.property⟩ ⟨s.val.toMul,s.property⟩) }
  let f := f₀.toZModLinearMap 2
  have hni := hcV.1
  have hf : Function.Bijective f := by
    constructor
    · intro r s hrs
      have hh : (⟨r.val.toMul,r.property⟩ : V) = ⟨s.val.toMul,s.property⟩ := hni hrs
      exact Subtype.ext (congrArg (fun v : V => Additive.ofMul (⟨v,hVR v.property⟩ : R)) hh)
    · intro v
      obtain ⟨x,hx⟩ := hcV.2 (Multiplicative.ofAdd v)
      exact ⟨⟨Additive.ofMul ⟨x,hVR x.property⟩,x.property⟩, hx⟩
  let e : Representation.Equiv N.toRepresentation BinaryLinearThree.W := {
    toLinearEquiv := LinearEquiv.ofBijective f hf
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro r
      obtain ⟨l,rfl⟩ := hq g
      have hh := hcn l (⟨r.val.toMul,r.property⟩ : V)
      change (cV ⟨(ρ (q l) r.val).toMul,_⟩).toAdd = _
      convert hh using 1
      · congr 2
        exact Subtype.ext (hact l r.val)
      · rfl }
  have hdim : Module.finrank (ZMod 2) (Additive R) = 4 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive R)
    rw [Nat.card_zmod] at hh
    have hc : Nat.card (Additive R) = 16 := hRcard
    rw [hc] at hh
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) (hh.symm.trans (by decide : 16 = 2 ^ 4))
  have hquot (g : BinaryLinearThree.Group) (r : Additive R) : ρ g r - r ∈ N := by
    obtain ⟨l,rfl⟩ := hq g
    change (((ρ (q l) r).toMul / r.toMul : R) : G) ∈ V
    rw [Subgroup.coe_div, div_eq_mul_inv, hact l r]
    exact hcomm (by rw [commutator_comm]; exact commutator_mem_commutator l.property r.toMul.property)
  let fA : A →* BinaryLinearThree.Group := q.comp (Subgroup.inclusion hAL)
  let C₀ : Subgroup B₀ := centralizer (U₀.subgroupOf B₀ : Set B₀)
  let C : Subgroup A := C₀.comap (Subgroup.inclusion hAB)
  let B : Subgroup BinaryLinearThree.Group := C.map fA
  let : (U₀.subgroupOf B₀).Normal := normal_subgroupOf_of_le_normalizer hNB
  let : IsElementaryAbelian 2 U₀ := {
    is_comm := ⟨fun x y => Subtype.ext (congrArg (fun r : R => (r : G))
      (mul_comm (⟨x,hU₀R x.property⟩ : R) ⟨y,hU₀R y.property⟩))⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := R) (x : G) (hU₀R x.property))) }
  let : IsElementaryAbelian 2 (U₀.subgroupOf B₀) := IsElementaryAbelian.subgroupOf hU₀B
  have hC₀ : C₀.index ≤ 2 := centralizer_index_le_two_of_normal_four hB (U₀.subgroupOf B₀)
    ((Nat.card_congr (subgroupOfEquivOfLe hU₀B).toEquiv).trans hfour)
  have hC : C.index ≤ 2 := by
    rw [show C.index = C₀.relIndex (Subgroup.inclusion hAB).range from index_comap _ _]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero C₀.index_ne_zero_of_finite)
      (relIndex_dvd_index_of_normal _ _)).trans hC₀
  have hBP : B ≤ P := hP ▸ (map_le_range fA C)
  have hindex : B.relIndex P ≤ 2 := by
    have hh : B.relIndex P = (C ⊔ fA.ker).index := by
      rw [← hP]
      rw [← index_comap, comap_map_eq]
    rw [hh]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero C.index_ne_zero_of_finite)
      (index_dvd_of_le (le_sup_left : C ≤ C ⊔ fA.ker))).trans hC
  let w : Additive R := Additive.ofMul ⟨u,hU₀R u.property⟩
  have hBw (b : BinaryLinearThree.Group) (hb : b ∈ B) : ρ b w = w := by
    obtain ⟨a,ha,rfl⟩ := hb
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((ρ (q (Subgroup.inclusion hAL a)) w).toMul : G) = u
    rw [hact]
    have hh := congrArg Subtype.val (ha ⟨u,hU₀B u.property⟩ u.property)
    change (u : G) * (a : G) = (a : G) * u at hh
    change (a : G) * (u : G) * (a : G)⁻¹ = u
    rw [← hh, mul_inv_cancel_right]
  obtain ⟨hsplit,hfix⟩ := BinaryLinearThree.NaturalExtension.splitting_of_sylow_index
    ρ hdim N e hquot w hu P B hBP hindex hBw
  have hfixed (r : Additive R) : r ∈ ρ.invariants ↔
      (r.toMul : G) ∈ centralizer (L : Set G) := by
    constructor
    · intro hr l hl
      have hh := congrArg (fun x : Additive R => (x.toMul : G)) (hr (q ⟨l,hl⟩))
      rw [hact] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro hr g
      obtain ⟨l,rfl⟩ := hq g
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [hact, hr l l.property, mul_inv_cancel_right]
  have hdecomp (r : R) : ∃ v ∈ V, ∃ c ∈ R ⊓ centralizer (L : Set G), v * c = r := by
    have hr : Additive.ofMul r ∈ N.toSubmodule ⊔ ρ.invariants := by
      rw [hsplit.sup_eq_top]; trivial
    obtain ⟨v,hv,c,hc,he⟩ := Submodule.mem_sup.mp hr
    exact ⟨v.toMul,hv,c.toMul,⟨c.toMul.property,(hfixed c).mp hc⟩,
      congrArg (fun x : Additive R => (x.toMul : G)) he⟩
  refine ⟨le_antisymm ?_ (sup_le hVR inf_le_left), ?_, ?_⟩
  · intro r hr
    obtain ⟨v,hv,c,hc,he⟩ := hdecomp ⟨r,hr⟩
    change v * c = r at he
    rw [← he]
    exact mul_mem (mem_sup_left hv) (mem_sup_right hc)
  · apply Subgroup.disjoint_def.mpr
    intro x hxV hxC
    have hz : (Additive.ofMul (⟨x,hxC.1⟩ : R)) = 0 :=
      Submodule.disjoint_def.mp hsplit.disjoint _ hxV ((hfixed _).mpr hxC.2)
    exact congrArg (fun x : Additive R => (x.toMul : G)) hz
  · let ec : ρ.invariants ≃ (R ⊓ centralizer (L : Set G) : Subgroup G) := {
      toFun := fun r => ⟨r.val.toMul,r.val.toMul.property,(hfixed r.val).mp r.property⟩
      invFun := fun r => ⟨Additive.ofMul ⟨r,r.property.1⟩,(hfixed _).mpr r.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [← Nat.card_congr ec, Module.natCard_eq_pow_finrank (K := ZMod 2), hfix, Nat.card_zmod]
    decide

end BinaryLinearThree.NaturalExtension
