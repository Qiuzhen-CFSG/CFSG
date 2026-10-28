module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Reduction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Natural.Coordinates
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Natural.Calculation
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Geometry.Model

/-!
# Point and root normalization for the natural tensor intersection

The centralizing actor has trivial five-point coordinate and is a nonidentity
involution in S₃. Its displacement on the binary three-point core has a single
nonzero value. Tensor induction therefore writes the given nonzero point as
that value tensored with a nonzero constituent vector, retaining an actual
small-factor displacement preimage.

The elementary order-eight actor projects to the order-two centralizer in S₃
and the order-two sign group. Its kernel supplies a nonidentity element in the
literal alternating component. Sylow fixation of the tensor point makes this
element fix the constituent vector. The genuine SL₂(4) frame then normalizes
the vector and this root simultaneously, and transports both original markings.
No order-four component intersection or actor dichotomy is assumed here.

`calculation_of_actor_normalization` discharges the point/root premise of the
existing finite calculation. The independent actor dichotomy remains explicit.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 14.4.10,
first proof paragraph, printed p.1010; case 14.4.2(5), p.1006, under Hypothesis
14.3.10, p.993, and the source quotient geometry of 12.8.8–12, pp.851–855.
-/

@[expose] public section

open Subgroup TensorProduct Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Intersection
open Representation.SL2FourNatural

private lemma small_centralizer_card (t : Three) (ht : t ≠ 1) (hs : t ^ 2 = 1) :
    Fintype.card {g : Three // g * t = t * g} = 2 := by
  revert t
  decide +kernel

private lemma small_displacement (t : Three) (ht : t ≠ 1) (hs : t ^ 2 = 1) :
    ∃ u : Small, smallAction t u - u ≠ 0 ∧
      ∀ n : Small, smallAction t n - n = 0 ∨
        smallAction t n - n = smallAction t u - u := by
  let : DecidablePred (· ∈ BinaryPermutation.core (Fin 3)) := fun v =>
    inferInstanceAs (Decidable ((∑ i, v i) = (0 : Bit)))
  let : Fintype Small := Subtype.fintype _
  revert t
  decide

variable {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module Bit V] {σ : Representation Bit D V}

private lemma element_first_ne_one (hAD : AltFive ≤ D) (d : ComplementIntersectionData σ) :
    d.element.1 ≠ 1 := by
  intro h
  exact d.element_ne_one (Prod.ext h (element_second_eq_one hAD d))

private lemma element_first_square (d : ComplementIntersectionData σ) :
    d.element.1 ^ 2 = 1 := by
  let := d.actor_elementary
  exact congrArg Prod.fst (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ d.element_mem)

private lemma component_exists (hAD : AltFive ≤ D) (d : ComplementIntersectionData σ) :
    ∃ a : AltFive, a ≠ 1 ∧ (1, inclusion hAD a) ∈ d.actor := by
  classical
  let := d.actor_elementary
  let φ : d.actor →* Three × ℤˣ :=
    ((MonoidHom.fst Three D).comp d.actor.subtype).prod
      (Equiv.Perm.sign.comp (D.subtype.comp ((MonoidHom.snd Three D).comp d.actor.subtype)))
  have hker : φ.ker ≠ ⊥ := by
    intro hk
    have hinj := φ.ker_eq_bot_iff.mp hk
    let f : d.actor → {g : Three // g * d.element.1 = d.element.1 * g} × ℤˣ :=
      fun a => (⟨a.val.1, congrArg (fun z : d.actor => z.val.1)
        (mul_comm a ⟨d.element, d.element_mem⟩)⟩, Equiv.Perm.sign a.val.2.val)
    have hf : Function.Injective f := by
      intro a b hab
      apply hinj
      have hfirst := congrArg (fun z => z.1.val) hab
      have hsecond := congrArg Prod.snd hab
      exact Prod.ext hfirst hsecond
    have hc := Nat.card_le_card_of_injective f hf
    rw [d.actor_card, Nat.card_prod, Nat.card_eq_fintype_card,
      small_centralizer_card _ (element_first_ne_one hAD d) (element_first_square d)] at hc
    have hz : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card]; decide
    rw [hz] at hc
    omega
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hker
  have hf : a.val.val.1 = 1 := congrArg Prod.fst a.property
  have hs : Equiv.Perm.sign a.val.val.2.val = 1 := congrArg Prod.snd a.property
  let r : AltFive := ⟨a.val.val.2.val, Equiv.Perm.mem_alternatingGroup.mpr hs⟩
  have he : (1, inclusion hAD r) = a.val.val := Prod.ext hf.symm rfl
  refine ⟨r, ?_, he ▸ a.val.property⟩
  intro hr
  apply ha
  apply Subtype.ext
  apply Subtype.ext
  rw [← he, hr, map_one]
  rfl

private def evaluation (i : Fin 3) : Small →ₗ[Bit] Bit :=
  (LinearMap.proj i).comp (BinaryPermutation.core (Fin 3)).subtype

private noncomputable def contract (i : Fin 3) : IntersectionSpace V →ₗ[Bit] V :=
  (TensorProduct.lid Bit V).toLinearMap.comp
    (TensorProduct.map (evaluation i) LinearMap.id)

private lemma contract_tmul (i : Fin 3) (n : Small) (v : V) :
    contract i (n ⊗ₜ[Bit] v) = n.val i • v := rfl

private lemma small_tmul_injective (n : Small) (hn : n ≠ 0) :
    Function.Injective (fun v : V => n ⊗ₜ[Bit] v) := by
  have hi : ∃ i, n.val i ≠ 0 := by
    by_contra! hh
    apply hn
    exact Subtype.ext (funext hh)
  obtain ⟨i, hi⟩ := hi
  have hb : n.val i = 1 := by
    have hh : ∀ a : Bit, a ≠ 0 → a = 1 := by decide
    exact hh _ hi
  intro u v he
  have hc := congrArg (contract (V := V) i) he
  simpa only [contract_tmul, hb, one_smul] using hc

private lemma point_tensor (hAD : AltFive ≤ D) (d : ComplementIntersectionData σ) :
    ∃ (n u : Small) (v : V), n ≠ 0 ∧ v ≠ 0 ∧
      smallAction d.element.1 u - u = n ∧ d.point = n ⊗ₜ[Bit] v := by
  obtain ⟨u, hu, hall⟩ := small_displacement d.element.1
    (element_first_ne_one hAD d) (element_first_square d)
  let n := smallAction d.element.1 u - u
  have hdelta (z : IntersectionSpace V) :
      ∃ v : V, sourceTensorAction σ d.element z - z = n ⊗ₜ[Bit] v := by
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul s v =>
      rw [tensor_tmul, element_second_eq_one hAD d, map_one, Module.End.one_apply,
        ← sub_tmul]
      rcases hall s with hs | hs
      · exact ⟨0, by rw [hs, zero_tmul, tmul_zero]⟩
      · exact ⟨v, by rw [hs]⟩
    | add x y hx hy =>
      obtain ⟨v, hv⟩ := hx
      obtain ⟨w, hw⟩ := hy
      refine ⟨v + w, ?_⟩
      rw [map_add, add_sub_add_comm, hv, hw, tmul_add]
  have hp := d.point_mem_first
  rw [d.first_eq_range] at hp
  obtain ⟨z, hz⟩ := hp
  obtain ⟨v, hv⟩ := hdelta z
  have he : d.point = n ⊗ₜ[Bit] v := hz.symm.trans hv
  refine ⟨n, u, v, hu, ?_, rfl, he⟩
  intro hv0
  exact d.point_ne_zero (by simpa [hv0] using he)

private lemma point_component_fixed (hAD : AltFive ≤ D) (d : ComplementIntersectionData σ)
    (n : Small) (hn : n ≠ 0) (v : V) (hp : d.point = n ⊗ₜ[Bit] v)
    (a : AltFive) (ha : (1, inclusion hAD a) ∈ d.actor) :
    σ (inclusion hAD a) v = v := by
  apply small_tmul_injective n hn
  have hh := d.point_fixed _ (d.actor_le_sylow ha)
  rwa [hp, tensor_tmul, map_one, Module.End.one_apply] at hh

/-- Normalize the actual tensor point and a nonidentity component actor together.
The case hypothesis is retained for the source interface; the construction only
needs the alternating component, elementary actor and displacement data. -/
theorem point_root_normalization (hAD : AltFive ≤ D)
    (_hcase : D = ⊤ ∨ D = AltFive) (σ : Representation Bit D V) :
    PointRootNormalization hAD σ := by
  intro hnatural d
  obtain ⟨e, f, hf⟩ := hnatural
  obtain ⟨n, u, v, hn, hv, hdisp, hp⟩ := point_tensor hAD d
  obtain ⟨a, ha, ham⟩ := component_exists hAD d
  have hfix : action (e a) (f v) = f v := by
    rw [← hf, point_component_fixed hAD d n hn v hp a ham]
  have hf0 : f v ≠ 0 := by simpa using hv
  have he1 : e a ≠ 1 := by simpa using ha
  obtain ⟨b, c, hc, hb, hr⟩ := Geometry.Model.exists_frame (f v) hf0 (e a) hfix he1
  let B := Geometry.Model.rebase b c hc
  let e' : AltFive ≃* Special := e.trans (MulAut.conj b⁻¹)
  let f' : V ≃ₗ[Bit] Vector := f.trans B.symm
  have he'a : e' a = upper 1 := by
    change b⁻¹ * e a * b⁻¹⁻¹ = upper 1
    rw [← hr, inv_inv]
    group
  have hroot : e'.symm (upper 1) = a := by
    apply e'.injective
    rw [e'.apply_symm_apply, he'a]
  refine ⟨{
    group := e'
    vector := f'
    equivariant := ?_
    small := n
    preimage := u
    displacement := hdisp
    point_eq := ?_
    root_mem := ?_ }⟩
  · intro q w
    change B.symm (f (σ (inclusion hAD q) w)) =
      action (b⁻¹ * e q * b⁻¹⁻¹) (B.symm (f w))
    rw [hf, inv_inv]
    apply B.injective
    rw [B.apply_symm_apply]
    change action (e q) (f w) =
      Geometry.Model.rebase b c hc (action (b⁻¹ * e q * b) (B.symm (f w)))
    rw [← Geometry.Model.rebase_equivariant, B.apply_symm_apply]
  · change d.point = n ⊗ₜ[Bit] f.symm (Geometry.Model.rebase b c hc e1)
    rw [hb, f.symm_apply_apply]
    exact hp
  · change (1, inclusion hAD (e'.symm (upper 1))) ∈ d.actor
    rwa [hroot]

/-- Application to the finite natural calculation: point/root normalization is
now discharged, leaving precisely the independent actor dichotomy. -/
theorem calculation_of_actor_normalization (hAD : AltFive ≤ D)
    (hcase : D = ⊤ ∨ D = AltFive) (hnatural : IsNaturalFour hAD σ)
    (hactor : ActorNormalization hAD σ) : ComplementIntersectionCalculation σ :=
  calculation_of_normalization hnatural (point_root_normalization hAD hcase σ) hactor

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Intersection
end
