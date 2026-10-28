module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.Torus
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Core
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness

/-!
# The model point group and its self-centralizing two-core

The upper unipotents form a normal subgroup of order sixteen. The literal
point-pair overlap complements it, giving the required split group
2⁴:(3 × D₁₀). Its two-core is exactly the unipotent group. A centralizing
complement element fixes zero and every unipotent translate of zero, hence
all seventeen points; faithfulness forces it to be trivial.

Source: Baumeister, *A geometry for groups of J₃-type* (2007), p.498,
the model instance of Lemma 2.7(ii) used in Corollary 2.10.
-/

@[expose] public noncomputable section
open Subgroup MulAction Matrix
open BenderSuzuki.Converse Theory.PSL2 Theory.PSL2.BinaryFourFieldExtension
open scoped Pointwise IsMulCommutative
namespace Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam

def rootHom : Multiplicative F →* Model :=
  linearInclusion.comp ((quotientMap F).comp (uniHom F))

def root : Subgroup Model := rootHom.range

theorem rootHom_injective : Function.Injective rootHom :=
  SemidirectProduct.inl_injective.comp ((quotientMap_injective F).comp uniHom_injective)

theorem root_card : Nat.card root = 16 :=
  (Nat.card_congr (MonoidHom.ofInjective rootHom_injective).symm.toEquiv).trans field_card

theorem root_le_point : root ≤ point := by
  rintro _ ⟨t, rfl⟩
  rw [mem_point, PBorel_eq_map]
  exact ⟨uni t.toAdd, Unip_le_Borel ⟨t, rfl⟩, rfl⟩

def R : Subgroup point := root.subgroupOf point

def C : Subgroup point := (point ⊓ pair).subgroupOf point

theorem R_card : Nat.card R = 16 :=
  (Nat.card_congr (subgroupOfEquivOfLe root_le_point).toEquiv).trans root_card

def C_equiv : C ≃* Complement :=
  (subgroupOfEquivOfLe inf_le_left).trans overlapEquiv

theorem C_card : Nat.card C = 30 :=
  (Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv).trans overlap_card

theorem R_C_disjoint : Disjoint R C := by
  apply disjoint_def.mpr
  intro x hx hxc
  obtain ⟨t, ht⟩ := hx
  have hp : (rootHom t).left ∈ PTorus F := (mem_overlap _).mp (ht.symm ▸ hxc)
  obtain ⟨g, hg, hge⟩ := hp
  have he : g = uni t.toAdd := quotientMap_injective F hge
  have hz : t.toAdd = 0 := by
    have hh := (mem_stabilizer_pZero_iff g).mp hg.2
    simpa only [he, uni_val, of_apply, cons_val_zero, cons_val_one, cons_val_fin_one] using hh
  apply Subtype.ext
  change (x : Model) = 1
  change rootHom t = (x : Model) at ht
  rw [← ht, show t = 1 from hz, map_one]

theorem pointComplement : R.IsComplement' C :=
  isComplement'_of_card_mul_and_disjoint (by rw [R_card, C_card, point_card]) R_C_disjoint

theorem field_root (a : Actor) (t : F) :
    action a (quotientMap F (uni t)) = quotientMap F (uni (a.val t)) := by
  rw [show action a = fieldAut a.val from rfl, fieldAut_apply_quotientMap]
  apply congrArg (quotientMap F)
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe, uni_val]

theorem inr_root (a : Actor) (t : F) :
    SemidirectProduct.inr a * rootHom (Multiplicative.ofAdd t) *
      (SemidirectProduct.inr a)⁻¹ = rootHom (Multiplicative.ofAdd (a.val t)) := by
  rw [← map_inv]
  change SemidirectProduct.inr a * SemidirectProduct.inl (quotientMap F (uni t)) *
    SemidirectProduct.inr a⁻¹ = SemidirectProduct.inl (quotientMap F (uni (a.val t)))
  rw [← SemidirectProduct.inl_aut, field_root]

theorem diagonal_root (u : Fˣ) (t : F) :
    linearInclusion (torusHom u) * rootHom (Multiplicative.ofAdd t) *
      (linearInclusion (torusHom u))⁻¹ =
      rootHom (Multiplicative.ofAdd ((u : F)^2 * t)) := by
  change linearInclusion (quotientMap F (tor u)) * linearInclusion (quotientMap F (uni t)) *
    (linearInclusion (quotientMap F (tor u)))⁻¹ = linearInclusion (quotientMap F (uni _))
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg linearInclusion
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg (quotientMap F)
  exact Borel_conj_uni (Torus_le_Borel (Torus_eq_range (F := F) ▸ ⟨u,rfl⟩)) t

theorem torusLift_root (x : Fˣ ⋊[unitsAction] Actor) (t : F) :
    torusLift x * rootHom (Multiplicative.ofAdd t) * (torusLift x)⁻¹ =
      rootHom (Multiplicative.ofAdd ((x.left : F)^2 * x.right.val t)) := by
  have hdecomp : torusLift x = linearInclusion (torusHom x.left) * SemidirectProduct.inr x.right := by
    apply SemidirectProduct.ext
    · change torusHom x.left = torusHom x.left * action 1 1
      simp
    · change x.right = 1 * x.right
      simp
  rw [hdecomp]
  calc
    _ = linearInclusion (torusHom x.left) *
        (SemidirectProduct.inr x.right * rootHom (Multiplicative.ofAdd t) *
          (SemidirectProduct.inr x.right)⁻¹) * (linearInclusion (torusHom x.left))⁻¹ := by group
    _ = _ := by rw [inr_root, diagonal_root]

theorem overlap_normalizes_root : point ⊓ pair ≤ normalizer (root : Set Model) := by
  apply le_normalizer_iff.mpr
  intro x hx y hy
  obtain ⟨a, rfl⟩ := torusLift_range.symm ▸ hx
  obtain ⟨t, rfl⟩ := hy
  exact ⟨Multiplicative.ofAdd ((a.left : F)^2 * a.right.val t.toAdd), (torusLift_root a t.toAdd).symm⟩

instance : R.Normal := by
  apply normal_subgroupOf_iff_le_normalizer root_le_point |>.mpr
  intro x hx
  obtain ⟨⟨r,c⟩, he, _⟩ := pointComplement.existsUnique (⟨x,hx⟩ : point)
  have he' : ((r : point) : Model) * ((c : point) : Model) = x := congrArg Subtype.val he
  rw [← he']
  exact (normalizer (root : Set Model)).mul_mem (root.le_normalizer r.property)
    (overlap_normalizes_root c.property)

def fieldPlaneEquiv : Multiplicative F ≃* Plane := by
  have hpow : 2 ^ Module.finrank (ZMod 2) F = 2 ^ 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    simpa only [Nat.card_zmod, field_card, show (2 : ℕ)^4 = 16 by decide] using h.symm
  have hd : Module.finrank (ZMod 2) F = 4 := Nat.pow_right_injective (by decide) hpow
  exact (Module.finBasisOfFinrankEq (ZMod 2) F hd).equivFun.toAddEquiv.toMultiplicative

def rootPlaneEquiv : R ≃* Plane :=
  (subgroupOfEquivOfLe root_le_point).trans
    ((MonoidHom.ofInjective rootHom_injective).symm.trans fieldPlaneEquiv)

def rootConjugation : C →* MulAut R :=
  R.normalizerMonoidHom.comp (inclusion (R.normalizer_eq_top ▸ le_top))

def pointAction : Complement →* MulAut Plane :=
  (MulAut.congr rootPlaneEquiv).toMonoidHom.comp (rootConjugation.comp C_equiv.symm.toMonoidHom)

def pointEquiv : point ≃* Plane ⋊[pointAction] Complement :=
  (SemidirectProduct.mulEquivSubgroup pointComplement).symm.trans
    (SemidirectProduct.congr' rootPlaneEquiv C_equiv)

theorem core_card : Nat.card (pCore 2 point) = 16 := by
  let M := Plane ⋊[pointAction] Complement
  let π : M →* Complement := SemidirectProduct.rightHom
  let : Finite M := Finite.of_equiv point pointEquiv.toEquiv
  have hker : Nat.card π.ker = 16 := by
    rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
    rw [← Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv]
    norm_num [Plane, Nat.card_eq_fintype_card, Fintype.card_multiplicative]
  have hp : IsPGroup 2 π.ker := IsPGroup.of_card (n := 4) hker
  have hc := π.card_pCore_of_ker_isPGroup SemidirectProduct.rightHom_surjective hp
  rw [complement_twoCore, Subgroup.card_bot, mul_one, hker] at hc
  have he := (equivMapOfInjective (pCore 2 point) pointEquiv.toMonoidHom pointEquiv.injective).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 pointEquiv))
  exact (Nat.card_congr he.toEquiv).trans hc

theorem core_eq_root : pCore 2 point = R := by
  have hp : IsPGroup 2 R := IsPGroup.of_card (n := 4) R_card
  have hr : R ≤ pCore 2 point := le_sSup ⟨inferInstance, hp⟩
  exact (eq_of_le_of_card_ge hr (by rw [R_card, core_card])).symm

instance : IsMulCommutative R := ⟨⟨fun x y => rootPlaneEquiv.injective (by
  rw [map_mul, map_mul, mul_comm])⟩⟩

theorem overlap_fixes_zero (c : (point ⊓ pair : Subgroup Model)) : (c : Model) • pZero F = pZero F := by
  have ht := (mem_overlap c.val).mp c.property
  rw [PTorus_eq] at ht
  rw [model_smul, fieldPoint_zero]
  exact ht.2

theorem root_centralizer : centralizer (R : Set point) = R := by
  have hR : R ≤ centralizer (R : Set point) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  apply le_antisymm _ hR
  intro x hx
  obtain ⟨⟨r,c⟩, he, _⟩ := pointComplement.existsUnique x
  have hc : (c : point) ∈ centralizer (R : Set point) := by
    have hh := (centralizer (R : Set point)).mul_mem
      ((centralizer (R : Set point)).inv_mem (hR r.property)) hx
    rw [← he, inv_mul_cancel_left] at hh
    exact hh
  have hc0 : ((c : point) : Model) • pZero F = pZero F :=
    overlap_fixes_zero ⟨_, c.property⟩
  have hc1 : (c : point) = 1 := by
    apply Subtype.ext
    apply permutation_injective
    apply Equiv.ext
    intro p
    change permutation ((c : point) : Model) p = permutation (1 : Model) p
    rw [map_one]
    change ((c : point) : Model) • p = p
    by_cases hp : p = pInf F
    · subst p
      exact (c : point).property
    · obtain ⟨g, hgInf, hgp⟩ := (is_two_pretransitive_iff.mp
        (inferInstance : IsMultiplyPretransitive Model Points 2)) inf_ne_zero (Ne.symm hp)
      have hg : g ∈ point := hgInf
      obtain ⟨⟨v,d⟩, hvd, _⟩ := pointComplement.existsUnique (⟨g,hg⟩ : point)
      have hd0 : ((d : point) : Model) • pZero F = pZero F :=
        overlap_fixes_zero ⟨_, d.property⟩
      have hv : ((v : point) : Model) • pZero F = p := by
        have hvdG := congrArg (fun y : point => (y : Model)) hvd
        change ((v : point) : Model) * ((d : point) : Model) = g at hvdG
        rw [← hvdG, mul_smul, hd0] at hgp
        exact hgp
      have hcomm : ((c : point) : Model) * ((v : point) : Model) =
          ((v : point) : Model) * ((c : point) : Model) :=
        (congrArg (fun y : point => (y : Model))
          ((mem_centralizer_iff.mp hc) (v : point) v.property)).symm
      rw [← hv, ← mul_smul, hcomm, mul_smul, hc0]
  rw [hc1, mul_one] at he
  exact he ▸ r.property

theorem core_centralizer : centralizer (pCore 2 point : Set point) = pCore 2 point := by
  rw [core_eq_root]
  exact root_centralizer

end Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam
