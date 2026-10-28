module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Reduction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Natural.Coordinates

/-!
# Pure actors in the marked natural tensor module

The centralizing element has trivial five-point coordinate and a nonidentity
involution as its three-point coordinate. Elementary abelianness restricts every
actor's first coordinate to that involution or the identity, so its pure second
coordinate also belongs to the actor. A pure actor fixes the normalized vector.
If all second coordinates are even, their marked matrices are upper unipotents.
The actor then embeds in a set of eight pairs; equality of orders makes this
embedding onto and supplies every upper root. Otherwise there is a pure outer
actor. No order-four intersection with the alternating component is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 14.4.10,
first proof paragraph, printed p.1010; the tensor models in 14.4.2(5), p.1006.
-/

public section

open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Intersection
open Representation.SL2FourNatural
variable {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module Bit V] {σ : Representation Bit D V}

private theorem three_involution_centralizer : ∀ t s : Three,
    t ^ 2 = 1 → t ≠ 1 → t * s = s * t → s = 1 ∨ s = t := by
  decide +kernel

/-- Elements of the actual elementary actor commute in the ambient product. -/
theorem actor_commute (d : ComplementIntersectionData σ)
    {a b : Three × D} (ha : a ∈ d.actor) (hb : b ∈ d.actor) : a * b = b * a := by
  let := d.actor_elementary
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : d.actor) ⟨b, hb⟩)

include hAD in
private theorem actor_first_cases (d : ComplementIntersectionData σ)
    {a : Three × D} (ha : a ∈ d.actor) : a.1 = 1 ∨ a.1 = d.element.1 := by
  let := d.actor_elementary
  have ht : d.element.1 ^ 2 = 1 :=
    congrArg Prod.fst (elemPow_eq_one_of_isElementaryAbelian d.element d.element_mem)
  have hne : d.element.1 ≠ 1 := by
    intro he
    exact d.element_ne_one (Prod.ext he (element_second_eq_one hAD d))
  exact three_involution_centralizer _ _ ht hne
    (congrArg Prod.fst (actor_commute d d.element_mem ha))

include hAD in
private theorem pure_actor_mem (d : ComplementIntersectionData σ)
    {a : Three × D} (ha : a ∈ d.actor) : (1, a.2) ∈ d.actor := by
  rcases actor_first_cases (hAD := hAD) d ha with he | he
  · simpa only [← he] using ha
  · have hh := d.actor.mul_mem (d.actor.inv_mem d.element_mem) ha
    have hh' : d.element⁻¹ * a = (1, a.2) := by
      apply Prod.ext
      · change d.element.1⁻¹ * a.1 = 1
        rw [he, inv_mul_cancel]
      · change d.element.2⁻¹ * a.2 = a.2
        rw [element_second_eq_one hAD d, inv_one, one_mul]
    rwa [hh'] at hh

private theorem PointRootCoordinates.small_ne_zero (d : ComplementIntersectionData σ)
    (p : PointRootCoordinates hAD d) : p.small ≠ 0 := by
  intro hz
  apply d.point_ne_zero
  rw [p.point_eq, hz, zero_tmul]

private theorem tmul_cancel {n : Small} (hn : n ≠ 0) {v w : V}
    (h : n ⊗ₜ[Bit] v = n ⊗ₜ[Bit] w) : v = w := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one Bit hn
  have hh := congrArg (fun t => TensorProduct.lid Bit V
    (TensorProduct.map l (LinearMap.id : V →ₗ[Bit] V) t)) h
  simpa only [TensorProduct.map_tmul, LinearMap.id_apply, hl,
    TensorProduct.lid_tmul, one_smul] using hh

/-- A pure actor fixes the first vector of the supplied natural frame. -/
theorem PointRootCoordinates.pure_fixed (d : ComplementIntersectionData σ)
    (p : PointRootCoordinates hAD d) {a : D} (ha : (1, a) ∈ d.actor) :
    p.vector (σ a (p.vector.symm e1)) = e1 := by
  have hh := d.point_fixed (1, a) (d.actor_le_sylow ha)
  rw [p.point_eq, tensor_tmul] at hh
  change smallAction 1 p.small ⊗ₜ[Bit] σ a (p.vector.symm e1) = _ at hh
  rw [map_one, Module.End.one_apply] at hh
  have he := congrArg p.vector (tmul_cancel (p.small_ne_zero d) hh)
  simpa only [p.vector.apply_symm_apply] using he

private theorem special_fixed_e1 (g : Special) (hg : action g e1 = e1) :
    g = upper (g.val 0 1) := by
  have h00 : g.val 0 0 = 1 := by
    simpa [action_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, e1] using
      congrFun hg 0
  have h10 : g.val 1 0 = 0 := by
    simpa [action_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, e1] using
      congrFun hg 1
  have h11 : g.val 1 1 = 1 := by
    have hd := g.property
    rw [Matrix.det_fin_two] at hd
    simpa only [h00, h10, one_mul, mul_zero, sub_zero] using hd
  apply Subtype.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simp [upper, h00, h10, h11]

private theorem PointRootCoordinates.inner_pure_eq_upper (d : ComplementIntersectionData σ)
    (p : PointRootCoordinates hAD d) {a : D} (ha : (1, a) ∈ d.actor)
    (heven : a.val ∈ AltFive) :
    p.group ⟨a.val, heven⟩ = upper ((p.group ⟨a.val, heven⟩).val 0 1) := by
  apply special_fixed_e1
  have hh := p.pure_fixed d ha
  rw [show a = inclusion hAD ⟨a.val, heven⟩ from rfl, p.equivariant,
    p.vector.apply_symm_apply] at hh
  exact hh

/-- Either the full marked root group is present, or a pure outer actor is present. -/
theorem PointRootCoordinates.root_or_outer (d : ComplementIntersectionData σ)
    (p : PointRootCoordinates hAD d) :
    (∀ a : Field, componentActor hAD p.group (upper a) ∈ d.actor) ∨
    ∃ a : D, (1, a) ∈ d.actor ∧ a.val ∉ AltFive := by
  classical
  by_cases hall : ∀ a ∈ d.actor, a.2.val ∈ AltFive
  · left
    let mark (a : d.actor) : Special := p.group ⟨a.val.2.val, hall a.val a.property⟩
    have hm (a : d.actor) : mark a = upper ((mark a).val 0 1) :=
      p.inner_pure_eq_upper d (pure_actor_mem (hAD := hAD) d a.property) _
    let f : d.actor → Bool × Field := fun a => (decide (a.val.1 = 1), (mark a).val 0 1)
    have hf : Function.Injective f := by
      intro a b hab
      have hfirst : a.val.1 = b.val.1 := by
        have hh : (a.val.1 = 1) ↔ (b.val.1 = 1) := by
          simpa only [f, decide_eq_decide] using congrArg Prod.fst hab
        rcases actor_first_cases (hAD := hAD) d a.property with ha | ha
        · exact ha.trans (hh.mp ha).symm
        · rcases actor_first_cases (hAD := hAD) d b.property with hb | hb
          · exact (hh.mpr hb).trans hb.symm
          · exact ha.trans hb.symm
      have hmark : mark a = mark b := by
        rw [hm a, hm b]
        exact congrArg upper (congrArg Prod.snd hab)
      have hsecond : a.val.2 = b.val.2 := by
        apply Subtype.ext
        exact congrArg (fun x : AltFive => x.val) (p.group.injective hmark)
      exact Subtype.ext (Prod.ext hfirst hsecond)
    have hc : Nat.card d.actor = Nat.card (Bool × Field) := by
      rw [d.actor_card, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_bool,
        Nat.card_eq_fintype_card, card_field]
    have hs := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hc⟩).surjective
    intro c
    obtain ⟨a, ha⟩ := hs (true, c)
    have hfirst : a.val.1 = 1 := by
      exact of_decide_eq_true (congrArg Prod.fst ha)
    have hmark : mark a = upper c := (hm a).trans
      (congrArg upper (congrArg Prod.snd ha))
    have he : componentActor hAD p.group (upper c) = a.val := by
      apply Prod.ext
      · exact hfirst.symm
      · apply Subtype.ext
        change (p.group.symm (upper c)).val = a.val.2.val
        rw [← hmark]
        simp [mark]
    rw [he]
    exact a.property
  · push Not at hall
    obtain ⟨a, ha, houter⟩ := hall
    exact Or.inr ⟨a.2, pure_actor_mem (hAD := hAD) d ha, houter⟩
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Intersection
