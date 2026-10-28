module
public import Theory.Representation.SmallDisplacementParabolics.PairedAction
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.SwappedCoordinates
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Sylow-central displacement in the paired natural action

The marked Sylow subgroup of GL₃(2) wr C₂ contains an element exchanging
the two summands. A commuting base element has conjugate block actions,
so its displacement rank is even. An involution exchanging the summands
has displacement rank three. Faithfulness therefore excludes rank one
for every nonidentity Sylow-central involution in this literal action.

This supplies the paired case of the rank-two witness in the actual
partner chief section of Aschbacher--Smith, original 15.2.27(2), printed
p.1119 (refs/quasithin.pdf p.1136). Individual noncentral transvections
in the paired action are not excluded.
-/

public noncomputable section
open Subgroup
namespace Representation.SmallDisplacementParabolics.PairedNatural
open RankTwo.Imprimitive

private def other : PairIndex := Multiplicative.ofAdd 1
private theorem index_cases (i : PairIndex) : i = 1 ∨ i = other := by decide +kernel +revert
private theorem other_ne_one : other ≠ 1 := by decide +kernel
private theorem other_square : other * other = 1 := by decide +kernel
private theorem other_inv : other⁻¹ = other := by decide +kernel

private def coordinates : (ThreeSpace × ThreeSpace) ≃ₗ[ZMod 2] (PairIndex → ThreeSpace) where
  toFun v := fun i => if i = 1 then v.1 else v.2
  invFun v := (v 1, v other)
  left_inv v := by simp [other_ne_one]
  right_inv v := by funext i; rcases index_cases i with rfl | rfl <;> simp [other_ne_one]
  map_add' v w := by
    funext i
    change (if i = 1 then v.1 + w.1 else v.2 + w.2) =
      (if i = 1 then v.1 else v.2) + (if i = 1 then w.1 else w.2)
    split <;> simp_all
  map_smul' c v := by
    funext i
    change (if i = 1 then c • v.1 else c • v.2) = c • (if i = 1 then v.1 else v.2)
    split <;> simp_all

private theorem coordinates_one (v : ThreeSpace × ThreeSpace) : coordinates v 1 = v.1 := by simp [coordinates]
private theorem coordinates_other (v : ThreeSpace × ThreeSpace) : coordinates v other = v.2 := by simp [coordinates,other_ne_one]

private theorem base_coordinates (a : PairedActor) (ha : a.right = 1) (v w : ThreeSpace) :
    pairedRepresentation a (coordinates (v,w)) =
      coordinates (a.left 1 v,a.left other w) := by
  funext i
  rcases index_cases i with rfl | rfl <;>
    simp [pairedRepresentation_apply,ha,coordinates_one,coordinates_other]

private theorem swapping_coordinates (a : PairedActor) (ha : a.right ≠ 1) (v w : ThreeSpace) :
    pairedRepresentation a (coordinates (v,w)) =
      coordinates (a.left 1 w,a.left other v) := by
  have he : a.right = other := (index_cases a.right).resolve_left ha
  funext i
  rcases index_cases i with rfl | rfl <;>
    simp [pairedRepresentation_apply,he,other_inv,other_square,coordinates_one,coordinates_other]

/-- An exchanging involution moves one entire three-dimensional summand. -/
theorem swapping_involution_displacement (a : PairedActor)
    (ha : a * a = 1) (hs : a.right ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range (pairedRepresentation a - 1)) = 3 := by
  have hp : pairedRepresentation a * pairedRepresentation a = 1 := by
    rw [←map_mul,ha,map_one]
  have hh := finrank_of_exchanging_coordinates coordinates (pairedRepresentation a)
    (a.left other).toLinearMap (a.left 1).toLinearMap
    (swapping_coordinates a hs) hp
  simpa [ThreeSpace] using hh

/-- Commutation with an exchanging element identifies the two block ranks. -/
theorem base_commuting_swap_displacement_even (a b : PairedActor)
    (ha : a.right = 1) (hb : b.right ≠ 1) (hc : Commute a b) :
    Module.finrank (ZMod 2) (LinearMap.range (pairedRepresentation a - 1)) =
      2 * Module.finrank (ZMod 2) (LinearMap.range ((a.left 1).toLinearMap - 1)) := by
  have he (v : ThreeSpace) : a.left other (b.left other v) = b.left other (a.left 1 v) := by
    have hh := congrArg (fun g => pairedRepresentation g (coordinates (v,0)) other) hc.eq
    simp only [map_mul,Module.End.mul_apply,swapping_coordinates b hb,
      base_coordinates a ha,coordinates_other] at hh
    exact hh
  have hr := (displacementRangeEquiv (b.left other) (a.left 1).toLinearMap
    (a.left other).toLinearMap he).finrank_eq
  have ht := (displacementRangeEquiv coordinates
    ((a.left 1).toLinearMap.prodMap (a.left other).toLinearMap)
    (pairedRepresentation a) (fun v => base_coordinates a ha v.1 v.2)).finrank_eq
  rw [finrank_block, ← hr] at ht
  simpa only [two_mul] using ht.symm

private instance : Finite (BinaryLinear.OuterCyclic.LinearGroup 3) :=
  Finite.of_injective (fun g : BinaryLinear.OuterCyclic.LinearGroup 3 => (g : ThreeSpace → ThreeSpace))
    DFunLike.coe_injective

/-- The literal projection of every full Sylow onto the top C₂ is surjective. -/
theorem exists_swapping_mem_sylow (S : Sylow 2 PairedActor) :
    ∃ b ∈ (S : Subgroup PairedActor), b.right ≠ 1 := by
  let f : PairedActor →* PairIndex := RegularWreathProduct.rightHom
  have hf : Function.Surjective f := by
    intro i
    exact ⟨RegularWreathProduct.inl i, rfl⟩
  let Q := S.mapSurjective hf
  have hp : IsPGroup 2 PairIndex := IsPGroup.of_card (n := 1) (by
    simp [PairIndex, Nat.card_eq_fintype_card])
  have he : (Q : Subgroup PairIndex) = ⊤ :=
    (Q.is_maximal' (hp.to_subgroup ⊤) le_top).symm
  have hm : other ∈ (S : Subgroup PairedActor).map f := by
    change other ∈ (Q : Subgroup PairIndex)
    rw [he]
    trivial
  obtain ⟨b,hb,he⟩ := hm
  exact ⟨b,hb, by change f b ≠ 1; rw [he]; exact other_ne_one⟩

private theorem paired_faithful : Function.Injective pairedRepresentation := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hfix (w : PairIndex → ThreeSpace) : pairedRepresentation a w = w :=
    LinearMap.congr_fun ha w
  have har : a.right = 1 := by
    by_contra hs
    have h := congrFun (hfix (coordinates (0,Pi.single 0 1))) other
    rw [swapping_coordinates a hs,coordinates_other,coordinates_other] at h
    simpa using congrFun h 0
  have hleft (i : PairIndex) : a.left i = 1 := by
    apply LinearEquiv.ext
    intro v
    have h := congrFun (hfix (fun _ => v)) i
    simpa [pairedRepresentation_apply,har] using h
  apply RegularWreathProduct.ext
  · funext i; exact hleft i
  · exact har

/-- A nonidentity involution commuting with an exchanging actor is not a transvection. -/
theorem commuting_swap_involution_displacement_ge_two (a b : PairedActor)
    (ha : a * a = 1) (hne : a ≠ 1) (hb : b.right ≠ 1) (hc : Commute a b) :
    2 ≤ Module.finrank (ZMod 2) (LinearMap.range (pairedRepresentation a - 1)) := by
  by_cases hs : a.right = 1
  · have he := base_commuting_swap_displacement_even a b hs hb hc
    have hp : 0 < Module.finrank (ZMod 2) (LinearMap.range (pairedRepresentation a - 1)) := by
      apply Nat.pos_of_ne_zero
      intro hz
      have hh := sub_eq_zero.mp (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz))
      exact hne (paired_faithful (hh.trans (map_one pairedRepresentation).symm))
    omega
  · rw [swapping_involution_displacement a ha hs]
    decide

/-- The marked full Sylow excludes rank-one displacement for its central involutions. -/
theorem sylow_central_involution_displacement_ge_two (S : Sylow 2 PairedActor)
    (a : PairedActor) (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (hc : ∀ s ∈ (S : Subgroup PairedActor), Commute a s) :
    2 ≤ Module.finrank (ZMod 2) (LinearMap.range (pairedRepresentation a - 1)) := by
  obtain ⟨b,hb,hs⟩ := exists_swapping_mem_sylow S
  exact commuting_swap_involution_displacement_ge_two a b (by simpa only [pow_two] using ha)
    hne hs (hc b hb)

end Representation.SmallDisplacementParabolics.PairedNatural
