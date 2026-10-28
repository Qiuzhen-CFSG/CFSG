module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import Theory.Representation.TripleSixFixedSpace

/-!
# Fixed vectors in the raw triple-six action

The source coordinates make the literal action linear on F₄³. Faithfulness
makes an element of order four a unipotent of nilpotence index three, whose
fixed space has dimension at most one. Consequently every injected set of
fixed vectors has at most four elements. No block reconstruction is used.

Source: Aschbacher–Smith B.4.2(8), K.1.3 and 15.3.21, pp.86,453,1127.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {L : Subgroup D}

noncomputable def tripleSixFieldAction (a : SourceInduction.ProjectiveLine.TripleSixAction ρ L) :
    Representation BinaryField.four.Carrier L (Fin 3 → BinaryField.four.Carrier) where
  toFun g :=
    { toFun := fun w => a.coordinates (ρ g (a.coordinates.symm w))
      map_add' := by intros; simp only [map_add]
      map_smul' := by
        intro c w
        simpa only [LinearEquiv.apply_symm_apply, RingHom.id_apply] using
          a.scalar_linear g c (a.coordinates.symm w) }
  map_one' := by
    apply LinearMap.ext
    intro w
    change a.coordinates (ρ (1 : D) (a.coordinates.symm w)) = w
    rw [map_one,Module.End.one_apply,LinearEquiv.apply_symm_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro w
    change a.coordinates (ρ ((g*h : L) : D) (a.coordinates.symm w)) =
      a.coordinates (ρ g (a.coordinates.symm (a.coordinates (ρ h (a.coordinates.symm w)))))
    rw [Subgroup.coe_mul,map_mul,Module.End.mul_apply,LinearEquiv.symm_apply_apply]

theorem tripleSix_four_fixed_card
    (a : SourceInduction.ProjectiveLine.TripleSixAction ρ L)
    (hf : Function.Injective (ρ.comp L.subtype)) (t : L) (ht : orderOf t = 4)
    {X : Type*} [Finite X] (j : X → W) (hj : Function.Injective j)
    (hfix : ∀ x, ρ t (j x) = j x) : Nat.card X ≤ 4 := by
  let τ := tripleSixFieldAction a
  have hτ : Function.Injective τ := by
    intro g h he
    apply hf
    apply LinearMap.ext
    intro v
    change ρ g v = ρ h v
    apply a.coordinates.injective
    have hh := LinearMap.congr_fun he (a.coordinates v)
    change a.coordinates (ρ g (a.coordinates.symm (a.coordinates v))) =
      a.coordinates (ρ h (a.coordinates.symm (a.coordinates v))) at hh
    simpa only [LinearEquiv.symm_apply_apply] using hh
  have ht4 : t^4 = 1 := ht ▸ pow_orderOf_eq_one t
  have ht2 : t^2 ≠ 1 := by
    intro hh
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [ht] at hd
    norm_num at hd
  let U := (τ t - 1).ker
  have hr : Module.finrank BinaryField.four.Carrier U ≤ 1 := TripleSixFixedSpace.fixed_rank_le_one
    (by simp) (τ t) (by rw [←map_pow,ht4,map_one])
    (fun hh => ht2 (hτ (by simpa only [map_pow,map_one] using hh)))
  have hc : Nat.card U ≤ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := BinaryField.four.Carrier),BinaryField.four.card_eq]
    exact (Nat.pow_le_pow_right (by decide : 0 < 4) hr).trans_eq (by norm_num)
  let f : X → U := fun x => ⟨a.coordinates (j x),by
    change a.coordinates (ρ t (a.coordinates.symm (a.coordinates (j x)))) - a.coordinates (j x) = 0
    rw [LinearEquiv.symm_apply_apply,hfix,sub_self]⟩
  exact (Nat.card_le_card_of_injective f (fun x y hh =>
    hj (a.coordinates.injective (congrArg Subtype.val hh)))).trans hc

end CFSG.Quasithin.ChapterB.QuasisimpleSource
