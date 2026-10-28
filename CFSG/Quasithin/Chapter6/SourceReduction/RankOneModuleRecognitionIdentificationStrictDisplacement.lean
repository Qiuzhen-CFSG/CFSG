module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictAction
public import Theory.LinearAlgebra.AlternatingFinrank
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic

/-!
# The rank-two symplectic involution in the strict branch

The square of every element of U lies in the marked line. For v in the
elementary layer, vuv⁻¹u⁻¹ has square one. These identities force u to
commute with vuv⁻¹, so the commutator form satisfies B(x,vx)=0.

The displacement lies in the image of U ∩ V, already a binary plane.
Its nonzero rank is even, by composing the nondegenerate form with the
displacement operator. Therefore its moved space is exactly that plane.
This proves the action assertion of 6.2.16(4) without a model classifier
or an assumed order for the whole involution centralizer.

Source: Aschbacher--Smith, 6.2.16(1),(4), printed p.689. Crossing geometry
and the strict contradiction remain with this owner. Final discharge of
LocalAnalysis stays with qt-d-1222-rankone-recognition-identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G]

@[expose] def strictLayerImage (T L R : Subgroup G) (z : G) :
    Subgroup (StrictActor T L R z) :=
  ((layer L R).subgroupOf (centralizer ({z} : Set G))).map
    (QuotientGroup.mk' (strictQuotientAction T L R z).ker)

@[expose] def strictCentralPlane (T L R : Subgroup G) (z : G)
    [IsElementaryAbelian 2 (StrictVectorQuotient T L R z)] :
    Submodule (ZMod 2) (Additive (StrictVectorQuotient T L R z)) :=
  AddSubgroup.toZModSubmodule 2
    (((sourceClosure T L R z ⊓ layer L R).subgroupOf (sourceClosure T L R z)).map
      (QuotientGroup.mk' (center (sourceClosure T L R z)))).toAddSubgroup

private theorem even_displacement_rank {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (B : LinearMap.BilinForm (ZMod 2) W)
    (hB : B.Nondegenerate) (D : W →ₗ[ZMod 2] W) (hD : ∀ w, B (D w) w = 0) :
    Even (Module.finrank (ZMod 2) D.range) := by
  let C : LinearMap.BilinForm (ZMod 2) W := B.comp D LinearMap.id
  have hC : C.IsAlt := hD
  have hk : C.ker = D.ker := by
    ext x
    constructor
    · intro hx
      exact hB.1 (D x) (fun y => LinearMap.congr_fun hx y)
    · intro hx
      apply LinearMap.ext
      intro y
      change B (D x) y = 0
      rw [show D x = 0 from hx, map_zero]
      rfl
  have he := AlternatingForm.even_finrank_sub_finrank_ker C hC
  rw [hk, ← D.finrank_range_add_finrank_ker, Nat.add_sub_cancel_right] at he
  exact he

private theorem commute_of_square_displacement (a b : G)
    (hs : a ^ 2 = b ^ 2) (hd : (a / b) ^ 2 = 1) : Commute a b := by
  let c := a / b
  have hcb : c * b = a := div_mul_cancel a b
  have hc : c * c = 1 := by simpa only [c, pow_two] using hd
  have he : c * b * c = b := by
    apply mul_right_cancel (b := b)
    calc
      c * b * c * b = (c * b) ^ 2 := by simp only [pow_two, mul_assoc]
      _ = b * b := by rw [hcb, hs, pow_two]
  have hcomm : c * b = b * c := by
    calc
      c * b = (c * b * c) * c := by rw [mul_assoc (c * b), hc, mul_one]
      _ = b * c := by rw [he]
  rw [← hcb]
  exact (show Commute c b from hcomm).mul_left (Commute.refl b)

variable [Finite G] {κ : GroupClass.{u}} {T : Sylow 2 G} {L M R : Subgroup G}
  {n : ℕ} {z : G}

theorem LocalAnalysis.strict_layer_commutes_conjugate
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    (v : centralizer ({z} : Set G)) (hv : (v : G) ∈ layer L R)
    (w : sourceClosure (T : Subgroup G) L R z) :
    Commute w (strictClosureAction (T : Subgroup G) L R z v w) := by
  let U := sourceClosure (T : Subgroup G) L R z
  let a := strictClosureAction (T : Subgroup G) L R z v
  have hp : IsPGroup 2 U :=
    ((centralizer ({z} : Set G)).isPGroup_pCoreIn 2).to_le A.closure_le_core
  let : Fact (IsPGroup 2 U) := ⟨hp⟩
  let := h611.layer_elementary
  have hline := (A.strict_closure_frattini_eq_line h611 hnatural hz horder hstrict).1
  have hwline : (w : G) ^ 2 ∈ zpowers z := hline ▸
    (show (w : G) ^ 2 ∈ (frattini U).map U.subtype from
      ⟨w ^ 2, pth_power_mem_frattini_of_isPGroup (p := 2) w, rfl⟩)
  have hvl : zpowers z ≤ centralizer ({(v : G)} : Set G) := by
    apply zpowers_le.mpr
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp v.property).symm
  have hs : (a w) ^ 2 = w ^ 2 := by
    rw [← map_pow]
    apply Subtype.ext
    change (strictClosureAction (T : Subgroup G) L R z v (w ^ 2) : G) = (w : G) ^ 2
    rw [strictClosureAction_apply, Subgroup.coe_pow,
      ← mem_centralizer_singleton_iff.mp (hvl hwline), mul_inv_cancel_right]
  have hd : (a w / w) ^ 2 = 1 := by
    apply Subtype.ext
    change ((strictClosureAction (T : Subgroup G) L R z v w : G) / (w : G)) ^ 2 = 1
    rw [strictClosureAction_apply, div_eq_mul_inv, ← commutatorElement_def]
    exact elemPow_eq_one_of_isElementaryAbelian _
      (A.layer_closure_commutator (commutator_mem_commutator hv w.property)).1
  exact (commute_of_square_displacement (a w) w hs hd).symm

section Linear
variable [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]

theorem LocalAnalysis.strictCentralPlane_finrank
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    Module.finrank (ZMod 2) (strictCentralPlane (T : Subgroup G) L R z) = 2 := by
  let U := sourceClosure (T : Subgroup G) L R z
  let P := ((U ⊓ layer L R).subgroupOf U).map (QuotientGroup.mk' (center U))
  let e : strictCentralPlane (T : Subgroup G) L R z ≃ P := {
    toFun w := ⟨w.val.toMul, w.property⟩
    invFun w := ⟨Additive.ofMul w.val, w.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hc : Nat.card (strictCentralPlane (T : Subgroup G) L R z) = 4 :=
    (Nat.card_congr e).trans (A.strict_central_quotient_plane_card h611 hnatural hz horder hstrict)
  have hh := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := strictCentralPlane (T : Subgroup G) L R z)
  rw [hc, Nat.card_zmod] at hh
  exact Nat.pow_right_injective (by decide : 1 < 2) (by simpa using hh.symm)

omit [Finite G] in
theorem LocalAnalysis.strict_displacement_le_plane
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (a : StrictActor (T : Subgroup G) L R z)
    (ha : a ∈ strictLayerImage (T : Subgroup G) L R z) :
    Representation.RankTwo.movedSpace (strictRepresentation (T : Subgroup G) L R z) a ≤
      strictCentralPlane (T : Subgroup G) L R z := by
  obtain ⟨v, hv, rfl⟩ := ha
  rintro _ ⟨w, rfl⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective
    (center (sourceClosure (T : Subgroup G) L R z)) w.toMul
  have hw : w = Additive.ofMul (QuotientGroup.mk' _ u) := congrArg Additive.ofMul hu.symm
  rw [hw]
  change Additive.ofMul (strictQuotientAction (T : Subgroup G) L R z v (QuotientGroup.mk' _ u)) -
    Additive.ofMul (QuotientGroup.mk' _ u) ∈ strictCentralPlane (T : Subgroup G) L R z
  have hc := A.layer_closure_commutator (commutator_mem_commutator hv u.property)
  let c : sourceClosure (T : Subgroup G) L R z := ⟨⁅(v : G), (u : G)⁆, hc.2⟩
  change strictQuotientAction (T : Subgroup G) L R z v (QuotientGroup.mk' _ u) /
    (QuotientGroup.mk' _ u) ∈
      (((sourceClosure (T : Subgroup G) L R z ⊓ layer L R).subgroupOf
        (sourceClosure (T : Subgroup G) L R z)).map (QuotientGroup.mk' _))
  have he : strictQuotientAction (T : Subgroup G) L R z v (QuotientGroup.mk' _ u) /
      (QuotientGroup.mk' _ u) = QuotientGroup.mk' _ c := by
    rw [strictQuotientAction_mk, ← map_div]
    congr 1
    apply Subtype.ext
    change (strictClosureAction (T : Subgroup G) L R z v u : G) / (u : G) = _
    rw [strictClosureAction_apply, div_eq_mul_inv]
    rfl
  rw [he]
  exact mem_map_of_mem _ (show c ∈ (sourceClosure (T : Subgroup G) L R z ⊓ layer L R).subgroupOf
    (sourceClosure (T : Subgroup G) L R z) from ⟨hc.2, hc.1⟩)

end Linear

theorem LocalAnalysis.strict_symplectic_layer_action
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    ∃ he : IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z),
      letI := he
      ∃ B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)),
        B.IsAlt ∧ B.Nondegenerate ∧
        4 ≤ Module.finrank (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)) ∧
        (∀ a x y, B (strictRepresentation (T : Subgroup G) L R z a x)
          (strictRepresentation (T : Subgroup G) L R z a y) = B x y) ∧
        ∀ a ∈ strictLayerImage (T : Subgroup G) L R z, a ≠ 1 →
          a ^ 2 = 1 ∧
          Representation.RankTwo.movedSpace (strictRepresentation (T : Subgroup G) L R z) a =
            strictCentralPlane (T : Subgroup G) L R z ∧
          Module.finrank (ZMod 2)
            (Representation.RankTwo.movedSpace (strictRepresentation (T : Subgroup G) L R z) a) = 2 ∧
          ∀ x, B x (strictRepresentation (T : Subgroup G) L R z a x) = 0 := by
  obtain ⟨he, e, B, hBa, hBn, hd, hcomm, hi⟩ :=
    A.strict_symplectic_geometry h611 hnatural hz horder hstrict
  let := he
  let ρ := strictRepresentation (T : Subgroup G) L R z
  have hpres : ∀ a x y, B (ρ a x) (ρ a y) = B x y := by
    intro a x y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (strictQuotientAction (T : Subgroup G) L R z).ker a
    exact hi (strictClosureAction (T : Subgroup G) L R z h) x.toMul y.toMul
  refine ⟨he, B, hBa, hBn, hd, hpres, ?_⟩
  intro a ha hne
  have ha2 : a ^ 2 = 1 := by
    obtain ⟨v, hv, rfl⟩ := ha
    rw [← map_pow]
    have hv2 : v ^ 2 = 1 := by
      apply Subtype.ext
      let := h611.layer_elementary
      exact elemPow_eq_one_of_isElementaryAbelian (A := layer L R) (v : G) hv
    rw [hv2, map_one]
  have hzform : ∀ x, B x (ρ a x) = 0 := by
    obtain ⟨v, hv, rfl⟩ := ha
    intro x
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective
      (center (sourceClosure (T : Subgroup G) L R z)) x.toMul
    have hx : x = Additive.ofMul (QuotientGroup.mk' _ u) := congrArg Additive.ofMul hu.symm
    rw [hx]
    change B (Additive.ofMul (QuotientGroup.mk' _ u))
      (Additive.ofMul (strictQuotientAction (T : Subgroup G) L R z v (QuotientGroup.mk' _ u))) = 0
    rw [strictQuotientAction_mk]
    obtain ⟨c, hc, hb⟩ := hcomm u (strictClosureAction (T : Subgroup G) L R z v u)
    rw [hb]
    have hc1 : c = 1 := by
      apply Subtype.ext
      rw [hc]
      exact commutatorElement_eq_one_iff_commute.mpr
        (A.strict_layer_commutes_conjugate h611 hnatural hz horder hstrict v hv u)
    rw [hc1, map_one]
    rfl
  let D := ρ a - 1
  have hparity : Even (Module.finrank (ZMod 2) D.range) := by
    apply even_displacement_rank B hBn D
    intro w
    change B (ρ a w - w) w = 0
    rw [map_sub, LinearMap.sub_apply, hBa.self_eq_zero, sub_zero]
    exact hBa.eq_iff.mpr (hzform w)
  have hle := A.strict_displacement_le_plane a ha
  have hplane := A.strictCentralPlane_finrank h611 hnatural hz horder hstrict
  have hrank : Module.finrank (ZMod 2) D.range = 2 := by
    have hupper := Submodule.finrank_mono hle
    have hnonzero : Module.finrank (ZMod 2) D.range ≠ 0 := by
      intro hzero
      have hd0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hzero)
      have heq : ρ a = 1 := sub_eq_zero.mp hd0
      exact hne (strictRepresentation_injective _ _ _ _ (heq.trans (map_one _).symm))
    obtain ⟨k, hk⟩ := hparity
    change Module.finrank (ZMod 2) D.range ≤ _ at hupper
    omega
  exact ⟨ha2, Submodule.eq_of_le_of_finrank_eq hle (hrank.trans hplane.symm), hrank, hzform⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
