module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.Restriction
public import Theory.GroupTheory.SubgroupProductCard
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Three-part obstruction in the two binary G₂ parabolics

The first parabolic is the product of its five-root group (order 32) and
the image of an explicit dihedral group of order six. This bounds its
order by 192. It contains the positive-root group of order 64, so nine
cannot divide its order. The known order of the second parabolic gives
the same obstruction. Restriction to the actual commutator subgroup
preserves both divisibility obstructions.

The homomorphism from the dihedral group is checked on the eight
split-octonion basis vectors. These are kernel-checked finite identities.
This proves the numerical obstruction only; containment of arbitrary
solvable Sylow overgroups in these parabolics is a separate obligation.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528). Root conventions are those of the licensed ATLAS port;
see `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public section

namespace Atlas.G2.BinaryParabolicPair.ThreeObstruction
open Subgroup Atlas.G2.Explicit Atlas.SplitOctonion
open scoped Pointwise
open Atlas.G2.BinaryCore
set_option maxRecDepth 100000

private theorem model_ext (g h : Model (ZMod 2))
    (he : ∀ i j, g.val (basisVector i) j = h.val (basisVector i) j) : g = h := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact linearMap_ext _ _ (fun i => funext (he i))

private def leviElement : DihedralGroup 3 → Model (ZMod 2)
  | .r i => cubicActor ^ i.val
  | .sr i => shortRoot * cubicActor ^ i.val

set_option maxHeartbeats 2000000 in
private def leviHom : DihedralGroup 3 →* Model (ZMod 2) where
  toFun := leviElement
  map_one' := by change cubicActor ^ 0 = 1; exact pow_zero _
  map_mul' a b := by
    apply model_ext
    exact (by decide +kernel : ∀ (a b : DihedralGroup 3) i j,
      (leviElement (a*b)).val (basisVector i) j =
      (leviElement a * leviElement b).val (basisVector i) j) a b

private theorem levi_mem (d : DihedralGroup 3) : leviHom d ∈ firstParabolic := by
  cases d with
  | r i => exact firstParabolic.pow_mem cubicActor_mem i.val
  | sr i =>
    exact firstParabolic.mul_mem (unipotent_le_firstParabolic shortRoot_mem_unipotent)
      (firstParabolic.pow_mem cubicActor_mem i.val)

private theorem first_factor (g : firstParabolic) :
    ∃ (q : Coordinates) (d : DihedralGroup 3), g.val = embedding q * leviHom d := by
  have heq : firstParabolic = core ⊔ leviHom.range := by
    apply le_antisymm
    · apply sup_le
      · rw [unipotent_eq_core_sup]
        apply sup_le le_sup_left
        apply (Subgroup.closure_le _).mpr
        rintro x (rfl : x = shortRoot)
        apply mem_sup_right
        exact ⟨.sr 0, by change shortRoot * cubicActor ^ 0 = shortRoot; simp⟩
      · apply (Subgroup.closure_le _).mpr
        rintro x (rfl : x = weylS)
        apply mem_sup_right
        refine ⟨.sr 1, ?_⟩
        change shortRoot * cubicActor ^ 1 = weylS
        rw [pow_one, cubicActor, ← mul_assoc, ← pow_two, shortRoot_sq, one_mul]
    · exact sup_le core_le_firstParabolic (by rintro _ ⟨d,rfl⟩; exact levi_mem d)
  have hn : leviHom.range ≤ normalizer (core : Set (Model (ZMod 2))) := by
    rintro _ ⟨d,rfl⟩
    exact firstParabolic_normalizes_core (levi_mem d)
  have hg : g.val ∈ (core : Set (Model (ZMod 2))) * (leviHom.range : Set (Model (ZMod 2))) := by
    rw [← coe_mul_of_right_le_normalizer_left core leviHom.range hn, ← heq]
    exact g.prop
  obtain ⟨_,⟨q,rfl⟩,_,⟨d,rfl⟩,he⟩ := hg
  exact ⟨q,d,he.symm⟩


theorem first_card_le : Nat.card firstParabolic ≤ 192 := by
  let f : Coordinates × DihedralGroup 3 → firstParabolic := fun x =>
    ⟨embedding x.1 * leviHom x.2,
      firstParabolic.mul_mem (core_le_firstParabolic ⟨x.1, rfl⟩) (levi_mem x.2)⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨q, d, he⟩ := first_factor x
    exact ⟨(q, d), Subtype.ext he.symm⟩
  have hc := Nat.card_le_card_of_surjective f hf
  simpa only [Nat.card_prod, card_coordinates, DihedralGroup.nat_card] using hc

theorem first_nine_not_dvd : ¬ 9 ∣ Nat.card firstParabolic := by
  intro h9
  have h64 : 64 ∣ Nat.card firstParabolic := by
    simpa only [card_unipotent_binary] using card_dvd_of_le unipotent_le_firstParabolic
  have hd := (show Nat.Coprime 9 64 by decide).mul_dvd_of_dvd_of_dvd h9 h64
  have hp := Nat.card_pos (α := firstParabolic)
  have hl := Nat.le_of_dvd hp hd
  have hu := first_card_le
  omega

theorem second_nine_not_dvd : ¬ 9 ∣ Nat.card secondParabolic := by
  rw [secondParabolic_card]
  decide

theorem derived_first_nine_not_dvd : ¬ 9 ∣ Nat.card derivedFirst := by
  intro hd
  apply first_nine_not_dvd
  have hc := card_dvd_of_le (show derivedFirst.map DerivedModel.subtype ≤ firstParabolic by
    rw [derivedFirst, subgroupOf_map_subtype]
    exact inf_le_left)
  rw [card_map_of_injective DerivedModel.subtype_injective] at hc
  exact hd.trans hc

theorem derived_second_nine_not_dvd : ¬ 9 ∣ Nat.card derivedSecond := by
  intro hd
  apply second_nine_not_dvd
  have hc := card_dvd_of_le (show derivedSecond.map DerivedModel.subtype ≤ secondParabolic by
    rw [derivedSecond, subgroupOf_map_subtype]
    exact inf_le_left)
  rw [card_map_of_injective DerivedModel.subtype_injective] at hc
  exact hd.trans hc

end Atlas.G2.BinaryParabolicPair.ThreeObstruction
