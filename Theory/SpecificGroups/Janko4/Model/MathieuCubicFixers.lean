module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.Janko4.Model.Center
public import Theory.Mathieu.M22.Properties.FixedHexads
public import Theory.Mathieu.M22.Properties.Order
public import Theory.GroupTheory.SimpleSectionSolvableReduction
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Cubic pointwise fixers of a Mathieu section in J4

A cubic subgroup centralizing a subgroup with an M22 quotient lies in the
center of its own centralizer. The nonsolvable simple quotient survives
this central kernel. The product of the cubic subgroup order and |M22|
therefore divides |J4|, forcing the cubic subgroup to have order at most
three. Native automorphism innerness transfers this bound to automorphism
subgroups. A nontrivial elementary cubic actor consequently has image of
order exactly three.

The consumer is the exceptional odd-actor comparison in Aschbacher--Smith
4.4.3, printed p.623. The literal native cardinality and automorphism
certificates retain their imported ATLAS attribution and licenses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.MathieuCubicFixers
open Sporadic.Mathieu
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- A cubic group centralizing an actual M22 section in J4 has order at
most three: the section survives the central quotient, retaining both
factors of three in its order. -/
theorem janko_mathieu_centralizing_threeGroup_card
    (B U : Subgroup Janko4.Model) (hB : IsPGroup 3 B)
    [IsMulCommutative B] (hBU : B ≤ centralizer (U : Set Janko4.Model))
    (g : U →* M22) (hg : Function.Surjective g) : Nat.card B ≤ 3 := by
  let C := centralizer (B : Set Janko4.Model)
  have hUC : U ≤ C := le_centralizer_iff.mp hBU
  have hBC : B ≤ C := (commutator_eq_bot_iff_le_centralizer).mp
    (commutator_self_eq_bot_iff.mpr inferInstance)
  let j : B →* center C := {
    toFun b := ⟨⟨b,hBC b.property⟩,mem_center_iff.mpr (fun c =>
      Subtype.ext ((c.property (b : Janko4.Model) b.property).symm))⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro b c hh
    exact Subtype.ext (congrArg (fun z : center C => ((z : C) : Janko4.Model)) hh)
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  have hns : ¬ Group.IsSolvable M22 := by
    intro hs
    let : IsMulCommutative M22 := ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr hs⟩⟩
    exact bot_ne_top (m22_center_eq_bot.symm.trans center_eq_top)
  let : Group.IsSolvable (center C) := Group.isSolvable_of_comm
    (fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm)
  let W := U.subgroupOf C
  let eU : W ≃* U := subgroupOfEquivOfLe hUC
  let f := g.comp eU.toMonoidHom
  have hf : Function.Surjective f := hg.comp eU.surjective
  obtain ⟨D,q,hq⟩ := simple_section_quotient_of_solvable_kernel hns (center C) W f hf
  have hd : Nat.card B * 443520 ∣ Nat.card Janko4.Model := by
    apply dvd_trans _ C.card_subgroup_dvd_card
    rw [(center C).card_eq_card_quotient_mul_card_subgroup,Nat.mul_comm (Nat.card B)]
    exact Nat.mul_dvd_mul (by
      rw [←m22_order]
      exact (card_dvd_of_surjective q hq).trans D.card_subgroup_dvd_card) (card_dvd_of_injective j hj)
  obtain ⟨n,hn⟩ := hB.exists_card_eq
  have hb : n ≤ 1 := by
    by_contra hh
    have h9 : 9 * 443520 ∣ Nat.card Janko4.Model :=
      (Nat.mul_dvd_mul_right (pow_dvd_pow 3 (by omega : 2 ≤ n)) 443520).trans (hn ▸ hd)
    rw [Janko4.Cardinality.model_card] at h9
    norm_num at h9
  rw [hn]
  exact (Nat.pow_le_pow_right (by decide : 0 < 3) hb).trans_eq (by norm_num)

/-- Innerness transfers the preceding order bound to the actual group of
cubic automorphisms fixing the Mathieu image. -/
theorem cubic_mathieu_fixer_card_le_three
    {S : Type*} [Group S] [Finite S] (e : S ≃* Janko4.Model)
    (U : Subgroup S) (g : U →* M22) (hg : Function.Surjective g)
    (B : Subgroup (MulAut S)) [IsElementaryAbelian 3 B]
    (hfix : ∀ b ∈ B, ∀ u ∈ U, b u = u) : Nat.card B ≤ 3 := by
  let c : Janko4.Model ≃* MulAut Janko4.Model := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot Janko4.model_center_eq_bot,
      Janko4.AdequateLocal.conj_surjective⟩
  let b : MulAut S ≃* Janko4.Model := (MulAut.congr e).trans c.symm
  let B' := B.map b.toMonoidHom
  let U' := U.map e.toMonoidHom
  let : IsElementaryAbelian 3 B' := IsElementaryAbelian.map b.toMonoidHom
  have hc : B' ≤ centralizer (U' : Set Janko4.Model) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨u,hu,rfl⟩
    have he : MulAut.conj (b a) = MulAut.congr e a := c.apply_symm_apply _
    have hh := DFunLike.congr_fun he (e u)
    change b a * e u * (b a)⁻¹ = e (a (e.symm (e u))) at hh
    rw [e.symm_apply_apply,hfix a ha u hu] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  let eU : U ≃* U' := U.equivMapOfInjective e.toMonoidHom e.injective
  have hb := janko_mathieu_centralizing_threeGroup_card B' U'
    (IsElementaryAbelian.isPGroup 3 B') hc (g.comp eU.symm.toMonoidHom)
    (hg.comp eU.symm.surjective)
  rwa [card_map_of_injective b.injective] at hb

/-- A nontrivial full elementary actor image fixing the Mathieu section
has order exactly three. -/
theorem cubic_mathieu_actor_range_card
    {A S : Type*} [Group A] [Group S] [Finite S]
    [IsElementaryAbelian 3 A] (e : S ≃* Janko4.Model)
    (U : Subgroup S) (g : U →* M22) (hg : Function.Surjective g)
    (b : A →* MulAut S) (x : A) (hx : orderOf (b x) = 3)
    (hfix : ∀ a : A, ∀ u ∈ U, b a u = u) : Nat.card b.range = 3 := by
  let : IsElementaryAbelian 3 b.range :=
    IsElementaryAbelian.of_surjective b.rangeRestrict b.rangeRestrict_surjective
  have hb := cubic_mathieu_fixer_card_le_three e U g hg b.range (by
    rintro _ ⟨a,rfl⟩ u hu
    exact hfix a u hu)
  have hd : 3 ∣ Nat.card b.range := by
    have h := orderOf_dvd_natCard (b.rangeRestrict x)
    rw [←orderOf_coe] at h
    change orderOf (b x) ∣ Nat.card b.range at h
    rwa [hx] at h
  exact le_antisymm hb (Nat.le_of_dvd Nat.card_pos hd)

end Janko4.MathieuCubicFixers
