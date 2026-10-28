module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.NaturalSetup
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CubicCentralizer
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
/-!
# The actual A₃ normalizer action on the binary plane

The full block module has four elements, so its intrinsic binary vector
space gives a plane coordinate equivalence. Every plane automorphism is
SL₂(2), and transport of literal conjugation constructs the full block
normalizer action with exactly the module centralizer as kernel.

Source: Aschbacher–Smith C.5.4, printed p.155, in the A₃ case.
-/
@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G} {F : Type*} [Field F]

noncomputable def cubicNaturalAction : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) →*
    MulAut (Multiplicative (Fin 2 → ZMod 2)) where
  toFun g := (BinaryLinear.OuterCyclic.slEquivLinear 2 g).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro v
    exact congrArg Multiplicative.ofAdd (LinearEquiv.congr_fun (map_one (BinaryLinear.OuterCyclic.slEquivLinear 2)) v.toAdd)
  map_mul' g k := by
    apply MulEquiv.ext
    intro v
    exact congrArg Multiplicative.ofAdd (LinearEquiv.congr_fun (map_mul (BinaryLinear.OuterCyclic.slEquivLinear 2) g k) v.toAdd)

theorem cubicNaturalAction_surjective : Function.Surjective cubicNaturalAction := by
  intro a
  let a₀ : (Fin 2 → ZMod 2) ≃+ (Fin 2 → ZMod 2) :=
    { toFun v := (a (Multiplicative.ofAdd v)).toAdd
      invFun v := (a.symm (Multiplicative.ofAdd v)).toAdd
      left_inv v := congrArg Multiplicative.toAdd (a.symm_apply_apply (Multiplicative.ofAdd v))
      right_inv v := congrArg Multiplicative.toAdd (a.apply_symm_apply (Multiplicative.ofAdd v))
      map_add' v w := congrArg Multiplicative.toAdd (a.map_mul (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
  let l : (Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    { a₀ with map_smul' := ZMod.map_smul a₀ }
  obtain ⟨g,hg⟩ := (BinaryLinear.OuterCyclic.slEquivLinear 2).surjective l
  refine ⟨g,?_⟩
  apply MulEquiv.ext
  intro v
  exact congrArg Multiplicative.ofAdd (LinearEquiv.congr_fun hg v.toAdd)

private theorem four_coordinates (h : Setup R K F) (hA : IsAlternatingBlock K 3) :
    Nonempty (U K ≃* Multiplicative (Fin 2 → ZMod 2)) := by
  let := h.elementary
  have hd : Module.finrank (ZMod 2) (Additive (U K)) = 2 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (U K))
    change Nat.card (U K) = _ at hh
    simpa only [Nat.card_zmod,h.cubic_module_card hA] using hh.symm
  exact ⟨(Module.finBasisOfFinrankEq (ZMod 2) (Additive (U K)) hd).equivFun.toAddEquiv.toMultiplicative⟩

theorem cubic_normalizer_action (h : Setup R K F) (hA : IsAlternatingBlock K 3) :
    ∃ (e : U K ≃* Multiplicative (Fin 2 → ZMod 2))
      (a : normalizer (K : Set G) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
      a.ker = (centralizer (U K : Set G)).subgroupOf (normalizer (K : Set G)) ∧
      ∀ z u, e (normalizerConjugate z u) = cubicNaturalAction (a z) (e u) := by
  obtain ⟨e⟩ := four_coordinates h hA
  have hn : normalizer (K : Set G) ≤ normalizer (U K : Set G) :=
    normalizer_le_normalizer_characteristic_image K (blockU K)
  let β := (MulAut.congr e).toMonoidHom.comp ((U K).normalizerMonoidHom.comp (inclusion hn))
  have hτ : Function.Injective cubicNaturalAction := natural_action_injective cubicNaturalAction (fun _ _ => rfl)
  let a := (MulEquiv.ofBijective cubicNaturalAction ⟨hτ,cubicNaturalAction_surjective⟩).symm.toMonoidHom.comp β
  have ha (z) : cubicNaturalAction (a z) = β z :=
    (MulEquiv.ofBijective cubicNaturalAction ⟨hτ,cubicNaturalAction_surjective⟩).apply_symm_apply _
  refine ⟨e,a,?_,?_⟩
  · ext z
    change a z = 1 ↔ _
    rw [← hτ.eq_iff,cubicNaturalAction.map_one,ha]
    change β z = 1 ↔ _
    constructor
    · intro hz u hu
      have hh := congrArg (fun b : MulAut (Multiplicative (Fin 2 → ZMod 2)) => e.symm (b (e ⟨u,hu⟩))) hz
      have hh' := congrArg (fun u : U K => (u : G)) hh
      dsimp [β] at hh'
      simp only [MulAut.congr_apply,MulEquiv.trans_apply,e.symm_apply_apply] at hh'
      change (z : G) * u * (z : G)⁻¹ = u at hh'
      exact (mul_inv_eq_iff_eq_mul.mp hh').symm
    · intro hz
      apply MulEquiv.ext
      intro v
      apply e.symm.injective
      dsimp [β]
      simp only [MulAut.congr_apply,MulEquiv.trans_apply,e.symm_apply_apply]
      change (⟨(z : G) * (e.symm v : G) * (z : G)⁻¹,_⟩ : U K) = e.symm v
      apply Subtype.ext
      change (z : G) * (e.symm v : G) * (z : G)⁻¹ = (e.symm v : G)
      exact (mul_inv_eq_iff_eq_mul.mpr (hz (e.symm v) (e.symm v).property).symm)
  · intro z u
    rw [ha]
    change e (normalizerConjugate z u) = e (normalizerConjugate z (e.symm (e u)))
    rw [e.symm_apply_apply]

omit [Finite G] in
theorem cubic_module_fixed_eq_one (hA : IsAlternatingBlock K 3) (u : U K)
    (hc : (u : G) ∈ centralizer (K : Set G)) : u = 1 := by
  obtain ⟨v,hv,he⟩ := u.property
  change (v : G) = (u : G) at he
  have hz : (⟨v,hv⟩ : blockU K) ∈ blockFixed K := by
    change v ∈ center K
    rw [mem_center_iff]
    intro k
    apply Subtype.ext
    simpa only [Subgroup.coe_mul,he] using hc k k.property
  rw [alternatingThreeCoverInput K hA,mem_bot] at hz
  apply Subtype.ext
  exact he.symm.trans (congrArg (fun z : blockU K => ((z : K) : G)) hz)
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
