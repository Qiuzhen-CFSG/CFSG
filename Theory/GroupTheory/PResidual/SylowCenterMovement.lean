module
public import Theory.GroupTheory.PResidual.PrimeToAction
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Sylow centers detect a normal coprime action

For a normal elementary two-subgroup V and a normal actor R, a nontrivial
coprime conjugation image gives a nonzero moving subgroup [V,R], disjoint
from C_V(R). The moving subgroup is normal in an ambient Sylow two-group,
so it meets that Sylow's omega-center nontrivially. Thus that omega-center
cannot centralize R.

A faithful quotient of a normal local subgroup packages the criterion: a
nontrivial odd two-residual in the quotient supplies exactly the coprime
image above, without assuming that the original residual has odd order.

Source application: DGS, Groups and Graphs (1985), 6.5, printed p.121,
the field-of-two central-case exclusion. Its literal closure application
is in DGS85/LocalStructure/BinaryCenterExclusion.
-/

open Subgroup
open scoped IsMulCommutative
public noncomputable section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial normal coprime moving subgroup meets the Sylow omega-center. -/
theorem sylow_omega_not_centralizes_of_coprime_movement
    (T : Sylow 2 G) (V R : Subgroup G) [V.Normal] [R.Normal]
    [IsElementaryAbelian 2 V]
    (hc : Nat.Coprime
      (Nat.card (V.normalizerMonoidHom.comp (inclusion
        (show R ≤ normalizer (V : Set G) from le_normalizer_of_normal))).range)
      (Nat.card V))
    (hm : ⁅V,R⁆ ≠ ⊥) : ¬ omegaCenterIn (T : Subgroup G) ≤ centralizer (R : Set G) := by
  have hVT : V ≤ (T : Subgroup G) :=
    (IsElementaryAbelian.isPGroup (p := 2) (G := V)).le_sylow_of_normal T
  obtain ⟨z,hzne⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hm ((commutator_le_left V R).trans hVT)
      le_normalizer_of_normal)
  have hzV : (z : G) ∈ V := commutator_le_left V R z.property.1
  have hzΩ : (z : G) ∈ omegaCenterIn (T : Subgroup G) :=
    (mem_omegaCenterIn_iff _ _).mpr ⟨hVT hzV,z.property.2.2,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) hzV⟩
  intro hcen
  have hz : (z : G) ∈ ⁅V,R⁆ ⊓ (V ⊓ centralizer (R : Set G)) :=
    ⟨z.property.1,hzV,hcen hzΩ⟩
  rw [(commutator_centralizer_decomposition_of_coprime_image V R
    le_normalizer_of_normal hc).2] at hz
  exact hzne (Subtype.ext (mem_bot.mp hz))


/-- A nontrivial odd residual in a faithful local action is detected by
an ambient Sylow omega-center. -/
theorem sylow_omega_not_centralizes_of_odd_residual_action
    {D : Type*} [Group D] [Finite D]
    (T : Sylow 2 G) (X V : Subgroup G) [X.Normal] [V.Normal]
    [IsElementaryAbelian 2 V]
    (q : X →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (V : Set G)).subgroupOf X)
    (ho : Nat.Coprime 2 (Nat.card (pResidual 2 D)))
    (hne : pResidual 2 D ≠ ⊥) :
    ¬ omegaCenterIn (T : Subgroup G) ≤ centralizer (X : Set G) := by
  let R := (pResidual 2 X).map X.subtype
  let : R.Normal := ConjAct.normal_of_characteristic_of_normal
  let ρ : G →* MulAut V := MulAut.conjNormal
  let f := ρ.comp X.subtype
  have hfk : f.ker = (centralizer (V : Set G)).subgroupOf X := by
    ext x
    constructor
    · intro hx v hv
      have he := congrArg (fun a : MulAut V => (a ⟨v,hv⟩ : G))
        (MonoidHom.mem_ker.mp hx)
      change (x : G) * v * (x : G)⁻¹ = v at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro hx
      apply MonoidHom.mem_ker.mpr
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      change (x : G) * (v : G) * (x : G)⁻¹ = v
      have hh : (v : G) * (x : G) = (x : G) * (v : G) := hx v v.property
      rw [←hh,mul_inv_cancel_right]
  let α : D →* MulAut V := q.liftOfSurjective hq ⟨f,by rw [hk,hfk]⟩
  have hf : f = α.comp q := by
    apply MonoidHom.ext
    intro x
    change f x = α (q x)
    dsimp only [α]
    rw [MonoidHom.liftOfRightInverse_comp_apply]
  let r := V.normalizerMonoidHom.comp (inclusion
    (show R ≤ normalizer (V : Set G) from le_normalizer_of_normal))
  have hr : r.range = (pResidual 2 D).map α := by
    have he : r = ρ.comp R.subtype := by rfl
    rw [he,MonoidHom.range_comp,range_subtype]
    change ((pResidual 2 X).map X.subtype).map ρ = _
    rw [map_map,show ρ.comp X.subtype = f from rfl,hf,←map_map,
      map_pResidual_of_surjective 2 q hq]
  have hc : Nat.Coprime (Nat.card r.range) (Nat.card V) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hn,hr]
    exact (ho.of_dvd_right ((pResidual 2 D).card_map_dvd α)).symm.pow_right n
  have hm : ⁅V,R⁆ ≠ ⊥ := by
    intro he
    have hR : R ≤ centralizer (V : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
    apply hne
    rw [←map_pResidual_of_surjective 2 q hq]
    apply (map_eq_bot_iff _).mpr
    rw [hk]
    intro x hx
    exact hR (mem_map_of_mem X.subtype hx)
  intro hz
  exact sylow_omega_not_centralizes_of_coprime_movement T V R hc hm
    (hz.trans (centralizer_le (map_subtype_le _)))

end Subgroup
