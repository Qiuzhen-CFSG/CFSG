module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.CubicModel
/-!
# The original A₃ module and its normalizer action

The A₃ block has trivial fixed layer and a four-element commutator module.
Its binary plane coordinates transport literal normalizer conjugation into
SL₂(2), retaining exactly the full module centralizer as the kernel.
No previously marked rank-one setup is required.

Source: Aschbacher–Smith C.5.4(2), printed p.155.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.RankOneSetup
open ConjugateSource.RankOne CounterexampleCharacteristic.ReducedMarking
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}

omit [Finite G] in
theorem cubic_module_card (hA : IsAlternatingBlock K 3) : Nat.card (U K) = 4 := by
  have hz : blockFixed K = ⊥ := alternatingThreeCoverInput K hA
  have hq : Function.Bijective (QuotientGroup.mk' (blockFixed K)) :=
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk',hz]),QuotientGroup.mk'_surjective _⟩
  have hc := hA.module_card_odd (by decide : Odd 3)
  rw [U,card_map_of_injective K.subtype_injective,
    Nat.card_congr (MulEquiv.ofBijective _ hq).toEquiv]
  simpa using hc

private theorem four_coordinates (hA : IsAlternatingBlock K 3) :
    Nonempty (U K ≃* Multiplicative (Fin 2 → ZMod 2)) := by
  let : IsElementaryAbelian 2 (U K) := hA.2.1.elementary.map K.subtype
  have hd : Module.finrank (ZMod 2) (Additive (U K)) = 2 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (U K))
    change Nat.card (U K) = _ at hh
    simpa only [Nat.card_zmod,cubic_module_card hA] using hh.symm
  exact ⟨(Module.finBasisOfFinrankEq (ZMod 2) (Additive (U K)) hd).equivFun.toAddEquiv.toMultiplicative⟩

theorem cubic_normalizer_action (hA : IsAlternatingBlock K 3) :
    ∃ (e : U K ≃* Multiplicative (Fin 2 → ZMod 2))
      (a : normalizer (K : Set G) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
      a.ker = (centralizer (U K : Set G)).subgroupOf (normalizer (K : Set G)) ∧
      ∀ z u, e (normalizerConjugate z u) = cubicNaturalAction (a z) (e u) := by
  obtain ⟨e⟩ := four_coordinates hA
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

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.RankOneSetup
