module

public import CFSG.Quasithin.Chapter15.Section03.Constructions
public import Theory.SpecificGroups.BinaryLinear.FourParabolicRadical
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry

/-!
# Cubic actions in the binary four-dimensional plane parabolic

Choose coordinates F₂² ⊕ F₂² carrying the given plane to the first
summand. The matrix (x,y) ↦ (y,x+y) has order three and no nonzero
fixed vector. Acting on both summands therefore supplies a fixed-free
cubic element of the plane parabolic, hence of its cubic-generated subgroup.
Acting only on the second summand supplies a cubic element fixing the
plane pointwise.

Every Sylow two-subgroup contained in the parabolic contains its radical.
The radical's fixed space is exactly the plane, so the second cubic element
fixes every Sylow-fixed vector. All coordinate changes are actual linear
equivalences; the statements hold for every marked plane and every such Sylow.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the repeated
natural-module calculation in 15.3.24, printed p.1129 (PDF p.1146).
-/

public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Repeated

private abbrev Vec := Fin 2 → ZMod 2
private abbrev Pair := Vec × Vec

private def cubic : BinaryLinear.GL Vec where
  toFun v := ![v 1, v 0 + v 1]
  invFun v := ![v 0 + v 1, v 0]
  left_inv := by decide
  right_inv := by decide
  map_add' := by decide
  map_smul' := by decide

private theorem cubic_order : orderOf cubic = 3 := by
  apply (orderOf_eq_prime_iff (p := 3)).mpr
  constructor
  · ext v i
    exact (by decide : ∀ v : Vec, ∀ i : Fin 2, cubic (cubic (cubic v)) i = v i) v i
  · intro he
    have hh := LinearEquiv.congr_fun he (![1, 0] : Vec)
    have hh' := congrFun hh 0
    norm_num [cubic] at hh'

private theorem cubic_fixed {v : Vec} (h : cubic v = v) : v = 0 :=
  (by decide : ∀ v : Vec, cubic v = v → v = 0) v h

private def diagonal (a b : BinaryLinear.GL Vec) : BinaryLinear.GL Pair := a.prodCongr b

private theorem diagonal_order (a : BinaryLinear.GL Vec) (ha : a ^ 3 = 1) :
    orderOf (diagonal a cubic) = 3 := by
  apply (orderOf_eq_prime_iff (p := 3)).mpr
  constructor
  · apply LinearEquiv.ext
    intro v
    apply Prod.ext
    · exact LinearEquiv.congr_fun ha v.1
    · have hc : cubic ^ 3 = 1 := by rw [← cubic_order]; exact pow_orderOf_eq_one cubic
      exact LinearEquiv.congr_fun hc v.2
  · intro he
    have he' : cubic = 1 := by
      ext v i
      have hh := congrArg Prod.snd (LinearEquiv.congr_fun he (0, v))
      exact congrFun hh i
    have := cubic_order
    rw [he', orderOf_one] at this
    omega

private def planeEquiv : FourParabolicRadical.plane ≃ₗ[ZMod 2] Vec where
  toFun v := v.val.1
  invFun v := ⟨(v, 0), by simp [FourParabolicRadical.plane]⟩
  left_inv v := by
    apply Subtype.ext
    change (v.val.1, 0) = v.val
    exact Prod.ext rfl (show v.val.2 = 0 from v.property).symm
  right_inv v := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem plane_dimension :
    Module.finrank (ZMod 2) FourParabolicRadical.plane = 2 := by
  rw [planeEquiv.finrank_eq]
  simp [Vec]

private theorem plane_coordinates (W : Submodule (ZMod 2) (Space 4))
    (hW : Module.finrank (ZMod 2) W = 2) :
    ∃ e : Pair ≃ₗ[ZMod 2] Space 4, ∀ v : Pair, e v ∈ W ↔ v.2 = 0 := by
  let f := FourParabolicRadical.spaceEquiv
  let W₀ := FourParabolicRadical.plane.map f.toLinearMap
  have hd : Module.finrank (ZMod 2) W₀ = Module.finrank (ZMod 2) W := by
    rw [f.finrank_map_eq, plane_dimension, hW]
  obtain ⟨g, hg⟩ := FourParabolicAction.exists_linearEquiv_map_eq W₀ W hd
  refine ⟨f.trans g, ?_⟩
  intro v
  change g (f v) ∈ W ↔ v.2 = 0
  rw [← hg]
  constructor
  · rintro ⟨w, ⟨u, hu, he₁⟩, he₂⟩
    change f u = w at he₁
    change g w = g (f v) at he₂
    have he : u = v := f.injective (he₁.trans (g.injective he₂))
    exact he ▸ hu
  · intro hv
    exact ⟨f v, ⟨v, hv, rfl⟩, rfl⟩

private theorem diagonal_mem_parabolic
    (W : Submodule (ZMod 2) (Space 4)) (e : Pair ≃ₗ[ZMod 2] Space 4)
    (he : ∀ v : Pair, e v ∈ W ↔ v.2 = 0) (a b : BinaryLinear.GL Vec) :
    linearGroupCongr e (diagonal a b) ∈ parabolic W := by
  intro x
  obtain ⟨v, rfl⟩ := e.surjective x
  rw [linearGroupCongr_apply, e.symm_apply_apply, he, he]
  exact b.map_eq_zero_iff

/-- The cubic-generated plane parabolic has no nonzero natural fixed vector. -/
theorem plane_theta_fixed_eq_zero (W : Submodule (ZMod 2) (Space 4))
    (hW : Module.finrank (ZMod 2) W = 2) (v : Space 4)
    (hv : ∀ g ∈ theta (parabolic W), g v = v) : v = 0 := by
  obtain ⟨e, he⟩ := plane_coordinates W hW
  let g := linearGroupCongr e (diagonal cubic cubic)
  have ho : orderOf g = 3 := (linearGroupCongr e).orderOf_eq _ |>.trans
    (diagonal_order cubic (by rw [← cubic_order]; exact pow_orderOf_eq_one cubic))
  have hg : g ∈ theta (parabolic W) :=
    subset_closure ⟨diagonal_mem_parabolic W e he cubic cubic, ho⟩
  have hfix := congrArg e.symm (hv g hg)
  change e.symm (e (diagonal cubic cubic (e.symm v))) = e.symm v at hfix
  rw [e.symm_apply_apply] at hfix
  have hz : e.symm v = 0 := Prod.ext
    (cubic_fixed (congrArg Prod.fst hfix)) (cubic_fixed (congrArg Prod.snd hfix))
  exact e.symm.map_eq_zero_iff.mp hz

/-- A genuine cubic element fixes all vectors fixed by the specified Sylow. -/
theorem exists_cubic_fixing_sylow_fixed (W : Submodule (ZMod 2) (Space 4))
    (hW : Module.finrank (ZMod 2) W = 2) (B : Sylow 2 (LinearGroup 4))
    (hB : (B : Subgroup (LinearGroup 4)) ≤ parabolic W) :
    ∃ g ∈ parabolic W, orderOf g = 3 ∧
      ∀ v : Space 4, (∀ b : B, (b : LinearGroup 4) v = v) → g v = v := by
  obtain ⟨e, he⟩ := plane_coordinates W hW
  let g := linearGroupCongr e (diagonal 1 cubic)
  have ho : orderOf g = 3 := (linearGroupCongr e).orderOf_eq _ |>.trans
    (diagonal_order 1 (one_pow 3))
  have hrad : radical W ≤ (B : Subgroup (LinearGroup 4)) := by
    have heq := B.is_maximal'
      (B.isPGroup'.to_sup_of_normal_right' (radical_two W)
        (hB.trans (parabolic_le_normalizer W))) le_sup_left
    exact heq ▸ le_sup_right
  have hW0 : W ≠ ⊥ := by
    intro hz
    have hzero : Module.finrank (ZMod 2) W = 0 := by simp [hz]
    omega
  refine ⟨g, diagonal_mem_parabolic W e he 1 cubic, ho, ?_⟩
  intro v hv
  have hvW : v ∈ W := (mem_iff_fixed_radical hW0 v).mpr
    (fun b hb => hv ⟨b, hrad hb⟩)
  have hv' : (e.symm v).2 = 0 := (he (e.symm v)).mp (by simpa only [e.apply_symm_apply] using hvW)
  have hh : diagonal 1 cubic (e.symm v) = e.symm v := by
    apply Prod.ext
    · rfl
    · change cubic (e.symm v).2 = (e.symm v).2
      rw [hv', map_zero]
  change e (diagonal 1 cubic (e.symm v)) = v
  rw [hh, e.apply_symm_apply]

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Repeated

end
