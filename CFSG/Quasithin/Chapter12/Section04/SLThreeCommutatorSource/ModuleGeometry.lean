module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.Setup
public import Theory.Representation.SLThreeCentralExtension.Involutions

/-!
# The B.4.8 involution plane on the original chosen module

The original marked natural quotient and its nonzero fixed kernel give a
four-dimensional indecomposable module. The three-involution generation
argument, applied to its dual, identifies displacement with the fixed
plane. The actual conjugation equation then identifies this plane with
[V,⟨a⟩] in the original ambient group, including C_V(L) and its order four.
The action of a is marked explicitly; extending this marking from L to
its full normalizer is a separate source input.

Source: Aschbacher–Smith, B.4.8(2), printed p.91, used in 12.4.8–9,
printed pp.815–816. This calculation does not assert fixed-space vanishing.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter12.Section04.SmallFusion

namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

theorem module_finrank_four (E : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥) :
    letI := D.elementary
    Module.finrank (ZMod 2) (Additive V) = 4 := by
  let _ := D.elementary
  let e : fixedSubgroup L V ≃ E.projection.toLinearMap.ker := {
    toFun := fun v => ⟨Additive.ofMul ⟨v, v.property.1⟩, by
      rw [E.kernel]
      exact (E.mem_fixed_iff _).mpr v.property.2⟩
    invFun := fun v => ⟨v.val.toMul, v.val.toMul.property,
      (E.mem_fixed_iff _).mp (E.kernel ▸ v.property)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hc : Nat.card E.projection.toLinearMap.ker = 2 :=
    (Nat.card_congr e).symm.trans (E.fixed_card_eq_two hne)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  have hk : Module.finrank (ZMod 2) E.projection.toLinearMap.ker = 1 :=
    Nat.pow_right_injective (by decide : 2 ≤ 2) (by simpa using hc)
  have hr := E.projection.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr E.surjective, finrank_top, hk,
    Module.finrank_fin_fun] at hr
  exact hr.symm

omit [Finite G] in
theorem action_injective (E : SLThreeExtension D) : letI := D.elementary
    Function.Injective E.action := by
  let _ := D.elementary
  intro a b he
  have hw : BinaryLinearThree.W a = BinaryLinearThree.W b := by
    apply LinearMap.ext
    intro v
    obtain ⟨v, rfl⟩ := E.surjective v
    rw [← E.projection.isIntertwining, ← E.projection.isIntertwining, he]
  apply Subtype.ext
  exact (Matrix.toLin').injective hw

theorem involution_linear_plane (E : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥)
    (a : BinaryLinearThree.Group) (ha : orderOf a = 2) : letI := D.elementary
    LinearMap.range (E.action a - LinearMap.id) =
      BinaryOffender.fixedSpace E.action (zpowers a) ∧
    Module.finrank (ZMod 2) (BinaryOffender.fixedSpace E.action (zpowers a)) = 2 := by
  let _ := D.elementary
  have hc := isCover_of_indecomposable E.projection E.surjective E.kernel.le
    SLThreeCentralExtension.commutator_eq_top E.indecomposable
  exact BinaryLinearThree.NaturalExtension.involution_range_eq_fixed E.action
    (module_finrank_four E hne) a ha
    (BinaryLinearThree.NaturalExtension.involution_codim_of_commutator_top
      E.action (module_finrank_four E hne) hc.2.2 a ha)

/-- Every involution acting through the marked SL₃ group has the actual
ambient displacement/fixed plane of B.4.8. -/
theorem ambient_involution_plane (E : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥) (a : G) (ha : a ^ 2 = 1)
    (hna : a ∉ centralizer (V : Set G))
    (b : BinaryLinearThree.Group)
    (hact : ∀ v : Additive V,
      ((E.action b v).toMul : G) = a * (v.toMul : G) * a⁻¹) :
    fixedSubgroup L V ≤ ⁅V, zpowers a⁆ ∧
      ⁅V, zpowers a⁆ = V ⊓ centralizer ({a} : Set G) ∧
      Nat.card (⁅V, zpowers a⁆ : Subgroup G) = 4 := by
  classical
  let _ := D.elementary
  have hb1 : b ≠ 1 := by
    intro he
    apply hna
    intro v hv
    have hh := hact (Additive.ofMul ⟨v, hv⟩)
    rw [he, map_one] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  have hb2 : b * b = 1 := by
    apply action_injective E
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [map_mul, Module.End.mul_apply, hact, hact, map_one]
    change a * (a * (v.toMul : G) * a⁻¹) * a⁻¹ = (v.toMul : G)
    calc
      _ = (a*a) * (v.toMul : G) * (a*a)⁻¹ := by group
      _ = (v.toMul : G) := by rw [← pow_two, ha]; simp
  have hb : orderOf b = 2 := orderOf_eq_prime (by simpa [pow_two] using hb2) hb1
  obtain ⟨hdis, hdim⟩ := involution_linear_plane E hne b hb
  have hfixed (v : Additive V) :
      v ∈ BinaryOffender.fixedSpace E.action (zpowers b) ↔
      (v.toMul : G) ∈ centralizer ({a} : Set G) := by
    rw [BinaryOffender.mem_fixedSpace_zpowers_iff, mem_centralizer_singleton_iff]
    constructor
    · intro hv
      have hh := hact v
      rw [hv] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    · intro hv
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [hact, hv.symm, mul_inv_cancel_right]
  let C := V ⊓ centralizer ({a} : Set G)
  have hdelta (v : Additive V) : ⁅a, (v.toMul : G)⁆ ∈ C := by
    let w := E.action b v - v
    have hw : w ∈ BinaryOffender.fixedSpace E.action (zpowers b) := by
      rw [← hdis]
      exact ⟨v, rfl⟩
    have he : (w.toMul : G) = ⁅a, (v.toMul : G)⁆ := by
      change ((E.action b v).toMul : G) / (v.toMul : G) = _
      rw [hact, div_eq_mul_inv]
      rfl
    exact he ▸ ⟨w.toMul.property, (hfixed w).mp hw⟩
  have ha1 : a ≠ 1 := by
    intro he
    exact hna (he ▸ (centralizer (V : Set G)).one_mem)
  have hao : orderOf a = 2 := orderOf_eq_prime ha ha1
  have hcomm : ⁅V, zpowers a⁆ = C := by
    apply le_antisymm
    · rw [commutator_comm]
      apply commutator_le.mpr
      intro c hc v hv
      rw [mem_zpowers_iff_mem_range_orderOf, hao] at hc
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hc
      have hnlt : n < 2 := Finset.mem_range.mp hn
      interval_cases n
      · simp
      · simpa using hdelta (Additive.ofMul ⟨v, hv⟩)
    · intro v hv
      let w : Additive V := Additive.ofMul ⟨v, hv.1⟩
      have hw : w ∈ LinearMap.range (E.action b - LinearMap.id) :=
        hdis ▸ (hfixed w).mpr hv.2
      obtain ⟨x, hx⟩ := hw
      have he := congrArg (fun y : Additive V => (y.toMul : G)) hx
      change ((E.action b x).toMul : G) / (x.toMul : G) = v at he
      rw [hact, div_eq_mul_inv] at he
      rw [commutator_comm]
      exact he ▸ commutator_mem_commutator (mem_zpowers a) x.toMul.property
  refine ⟨?_, hcomm, ?_⟩
  · rw [hcomm]
    intro v hv
    refine ⟨hv.1, ?_⟩
    exact (hfixed (Additive.ofMul ⟨v, hv.1⟩)).mp
      (fun c => (E.mem_fixed_iff (Additive.ofMul ⟨v, hv.1⟩)).mpr hv.2 c)
  · rw [hcomm]
    let e : C ≃ BinaryOffender.fixedSpace E.action (zpowers b) := {
      toFun := fun v => ⟨Additive.ofMul ⟨v, v.property.1⟩, (hfixed _).mpr v.property.2⟩
      invFun := fun v => ⟨v.val.toMul, v.val.toMul.property, (hfixed _).mp v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod, hdim]
    norm_num
end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource

