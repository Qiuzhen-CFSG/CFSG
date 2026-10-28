module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCoordinates
public import Theory.Representation.PSL3Two.FourGroupGeometry
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.Representation.GeneralLinearNatural

/-!
# Two-rank of a marked binary natural–dual normalizer

The trivial commutant makes conjugation of the full linear normalizer on
its component image faithful. The actual SL₃(2) automorphism-group bound
therefore gives two-rank at most two, including the outer coset. A faithful
ambient actor normalizing a surjectively marked component embeds in this
same normalizer; all maps preserve the original vector action.

The chosen-orbit application is `sourceOrbit_binary_automizer_rank` in
`NonFFSourceDoubledBinaryCoordinates`. This supplies the m₂ = 2 upper bound
used in 7.6; it does not assert the global r > 2 or weak-closure bounds.
Source: Aschbacher–Smith, Table 7.2.1 and 7.6.1, printed pp.698,701–703.
-/

public noncomputable section
open Representation Representation.BinaryOffender Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open BinaryLinearThree

private theorem binary_pair_injective : Function.Injective NaturalDual.action := by
  intro g h he
  apply specialLinearNatural_injective 3
  apply LinearMap.ext
  intro v
  exact congrArg Prod.fst (LinearMap.congr_fun he (v,0))

/-- The full linear normalizer of the actual natural–dual action has two-rank at most two. -/
theorem doubledBinary_normalizer_rank :
    primeRank 2 (linearNormalizer NaturalDual.action) ≤ 2 := by
  let μ := NaturalDual.action
  let f := (actionImage μ).normalizerMonoidHom
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    have ha' : f a = 1 := ha
    let E := LinearMap.GeneralLinearGroup.toLinearEquiv a.val
    have hE : ∀ g x, E (μ g x) = μ g (E x) := by
      intro g x
      have hh := congrArg (fun β : MulAut (actionImage μ) =>
        (β (actionHom μ g)).val) ha'
      change a.val * μ.asGroupHom g * a.val⁻¹ = μ.asGroupHom g at hh
      have hc : a.val * μ.asGroupHom g = μ.asGroupHom g * a.val := by
        exact (mul_inv_eq_iff_eq_mul).mp hh
      exact congrArg (fun z : (Module.End (ZMod 2) NaturalDual.Space)ˣ => z.val x) hc
    have hid := NaturalDual.centralizer_eq_one E hE
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro x
    exact LinearEquiv.congr_fun hid x
  have hi : Function.Injective (actionHom μ) := by
    intro g h he
    apply binary_pair_injective
    exact congrArg (imageRepresentation μ) he
  let e := MulEquiv.ofBijective (actionHom μ) ⟨hi, μ.asGroupHom.rangeRestrict_surjective⟩
  let : Finite NaturalDual.Space := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) NaturalDual.Space) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) NaturalDual.Space =>
      (f : NaturalDual.Space → NaturalDual.Space)) DFunLike.coe_injective
  have hr := primeRank_le_of_injective 2 f hf
  rw [← primeRank_equiv 2 (MulAut.congr e)] at hr
  apply hr.trans
  rw [primeRank_equiv 2 (MulAut.congr Matrix.PSL3Two.equiv)]
  exact (Matrix.PSL3Even.automorphism_two_rank_eq_of_card_two (ZMod 2) (by simp)).le

/-- A faithful larger actor inherits the bound when its normal component
has the literal natural–dual coordinates. -/
theorem doubledBinary_rank_of_marked_normal_range
    {H J U : Type*} [_root_.Group H] [_root_.Group J] [Finite H]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (hρ : Function.Injective ρ)
    (i : J →* H) [i.range.Normal]
    (q : J →* Group) (hq : Function.Surjective q)
    (E : U ≃ₗ[ZMod 2] NaturalDual.Space)
    (hE : ∀ j v, E (ρ (i j) v) = NaturalDual.action (q j) (E v)) :
    primeRank 2 H ≤ 2 := by
  let μ := NaturalDual.action
  let γ : Representation (ZMod 2) H NaturalDual.Space := E.conjRingEquiv.toMonoidHom.comp ρ
  have he (g : H) (v : U) : E (ρ g v) = γ g (E v) := by
    change E (ρ g v) = E (ρ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hγ : Function.Injective γ := E.conjRingEquiv.injective.comp hρ
  have hres (j : J) : γ (i j) = μ (q j) := by
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := E.surjective w
    rw [← he]
    exact hE j v
  have himage : i.range.map γ.asGroupHom = actionImage μ := by
    ext z
    constructor
    · rintro ⟨_,⟨j,rfl⟩,rfl⟩
      exact ⟨q j,Units.ext (hres j).symm⟩
    · rintro ⟨p,rfl⟩
      obtain ⟨j,rfl⟩ := hq p
      exact ⟨i j,⟨j,rfl⟩,Units.ext (hres j)⟩
  have hn (g : H) : γ.asGroupHom g ∈ linearNormalizer μ := by
    change γ.asGroupHom g ∈ normalizer (actionImage μ : Set _)
    rw [← himage]
    exact i.range.le_normalizer_map γ.asGroupHom
      (mem_map_of_mem _ (show g ∈ normalizer (i.range : Set H) from
        le_normalizer_of_normal (mem_top g)))
  let j : H →* linearNormalizer μ := γ.asGroupHom.codRestrict _ hn
  have hj : Function.Injective j := by
    intro x y hxy
    exact hγ (congrArg (fun z : linearNormalizer μ => z.val.val) hxy)
  let : Finite NaturalDual.Space := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) NaturalDual.Space) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) NaturalDual.Space =>
      (f : NaturalDual.Space → NaturalDual.Space)) DFunLike.coe_injective
  exact (primeRank_le_of_injective 2 j hj).trans doubledBinary_normalizer_rank

end CFSG.Quasithin.Chapter7.NormalizedSource
