module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.RootPair
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Detecting split intersections from the Ree fixed group

The exceptional field twist has square one over the chosen finite field.
Its restriction to a stable two-subgroup cannot be fixed-point-free unless
that subgroup is trivial: a fixed-point-free involution would force odd order.
For a fixed conjugating element, the intersection of the two split positive
subgroups is stable. Consequently disjointness of their fixed intersections
already forces the split intersection to be trivial.

This proves the fixed-intersection consequence needed in the opposition-cell
argument, using the concrete matrix carrier and the proved two-group theorem.
It supplies the nonidentity fixed-point step underlying GLS3 2.3.7–2.3.8(c),
without assuming a Bruhat decomposition or a fixed root parametrization.
Source: `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
open Subgroup
namespace ReeF4.LocalBlockInput.PairNormalization.OppositionCell

private theorem twoGroup_eq_bot_of_fixedPointFree {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hp : IsPGroup 2 H) (a : G →* G) (ha : Function.Involutive a)
    (hs : ∀ x ∈ H, a x ∈ H) (hf : ∀ x ∈ H, a x = x → x = 1) : H = ⊥ := by
  let f : H →* H := (a.comp H.subtype).codRestrict H (fun x => hs x x.property)
  have hfree : MonoidHom.FixedPointFree f := by
    intro x hx
    apply Subtype.ext
    exact hf x x.property (congrArg Subtype.val hx)
  have hinv : Function.Involutive f := fun x => Subtype.ext (ha x)
  have hodd := hfree.odd_card_of_involutive hinv
  by_contra hne
  have : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨k, hk, he⟩ := hp.nontrivial_iff_card.mp inferInstance
  exact hodd.not_two_dvd_nat (he.symm ▸ dvd_pow_self 2 (Nat.ne_of_gt hk))


/-- Restriction to an overgroup commutes with conjugation by its elements. -/
theorem map_conj_subgroupOf {G : Type*} [Group G] (H K : Subgroup G) (n : K) :
    (H.subgroupOf K).map (MulAut.conj n).toMonoidHom =
      (H.map (MulAut.conj (n : G)).toMonoidHom).subgroupOf K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(y : G), hy, rfl⟩
  · rintro ⟨y, hy, he⟩
    have he' : (n : G) * y * (n : G)⁻¹ = (x : G) := he
    have hyK : y ∈ K := by
      have h : y = (n : G)⁻¹ * (x : G) * (n : G) := by
        rw [← he']; simp [mul_assoc]
      rw [h]
      exact K.mul_mem (K.mul_mem (K.inv_mem n.property) x.property) n.property
    exact ⟨⟨y, hyK⟩, hy, Subtype.ext he⟩


/-- Disjointness in the fixed group forces disjointness in the split group.
The twist is an involution on the split intersection, which is a two-group. -/
theorem splitUnipotent_disjoint_conjugate_of_fixed_disjoint {m : ℕ}
    (d : LocalBlockInput m) (n : d.fixedGroup)
    (hd : Disjoint (LargeLocalSeeds.standardUnipotent d)
      ((LargeLocalSeeds.standardUnipotent d).map (MulAut.conj n).toMonoidHom)) :
    Disjoint (LargeLocalSeeds.splitUnipotent m)
      ((LargeLocalSeeds.splitUnipotent m).map (MulAut.conj (n : SplitGroup m)).toMonoidHom) := by
  let H := LargeLocalSeeds.splitUnipotent m
  let K := H ⊓ H.map (MulAut.conj (n : SplitGroup m)).toMonoidHom
  have hH : ∀ x ∈ H, d.twist x ∈ H := by
    intro x hx
    have h := Subgroup.mem_map_of_mem d.twist.toMonoidHom hx
    rwa [LargeLocalSeeds.splitUnipotent_twist d] at h
  have hn : d.twist (n : SplitGroup m) = n := n.property
  have hK : ∀ x ∈ K, d.twist x ∈ K := by
    rintro x ⟨hx, y, hy, rfl⟩
    refine ⟨hH _ hx, d.twist y, hH _ hy, ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, map_mul, map_inv, hn]
  have hfree : ∀ x ∈ K, d.twist x = x → x = 1 := by
    intro x hx hfx
    let y : d.fixedGroup := ⟨x, hfx⟩
    have hy : y ∈ (LargeLocalSeeds.standardUnipotent d).map
        (MulAut.conj n).toMonoidHom := by
      rw [LargeLocalSeeds.standardUnipotent, map_conj_subgroupOf]
      exact hx.2
    exact congrArg Subtype.val (Subgroup.disjoint_def.mp hd (show y ∈ LargeLocalSeeds.standardUnipotent d from hx.1) hy)
  have hKp : IsPGroup 2 K :=
    (LargeLocalSeeds.splitUnipotent_isPGroup m).of_injective
      (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective inf_le_left)
  apply disjoint_iff.mpr
  apply twoGroup_eq_bot_of_fixedPointFree K hKp d.twist.toMonoidHom ?_ hK hfree
  intro x
  change d.twist (d.twist x) = x
  have h := DFunLike.congr_fun d.twist_sq x
  simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h

end ReeF4.LocalBlockInput.PairNormalization.OppositionCell
end
