module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.FieldFourCentrality.Setup
public import Theory.GroupAction.OddOrbitFixedPoints
public import Theory.SpecificGroups.SL2.CubicFixedVectors
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# Odd-orbit reduction of fixed-seed centrality

First, a genuine cubic actor on the natural block section shows that its
fixed points in U(L) already lie in C_U(L). This keeps the central fixed
layer and both model isomorphisms explicit.

Next, for each seed element, restrict the actual Sylow subgroup of H to the
relative subnormal block. Its orbit in the elementary conjugate closure is
odd. The orbit-product argument reduces its centrality to the preceding
fixed-layer calculation.

These are conditional reductions. Elementary abelianness and displacement
of the source conjugate closure, normalization of the first block by X,
and the actual cubic source actor still have to be constructed.

Source: Aschbacher–Smith, C.1.7–13, printed pp.123–125, and the final
centrality deduction in the proof of 15.4.20, printed p.1164.
-/

@[expose] public section

open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality
open Subgroup ChapterC MulAction
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}

/-- An actual cubic source actor detects the intrinsic central fixed layer. -/
lemma layer_fixed_of_cubic_actor (c : ContraryData κ d i j) (b : ExchangedBlock c)
    {F : Type*} [Field F] [CharP F 2]
    (m : BlockModuleModel b.first (Matrix.SL2.naturalAction F))
    (hcubic : HasCubicActor c b) :
    firstLayer b ⊓ centralizer (d.wholeX : Set G) ≤ centralizer (b.first : Set G) := by
  obtain ⟨x, l, hl, hact⟩ := hcubic
  intro u hu
  obtain ⟨v, hv, rfl⟩ := hu.1
  let w : blockU b.first := ⟨v, hv⟩
  have hconj : blockConjugate b.first l w = w := by
    apply Subtype.ext
    apply Subtype.ext
    change ((blockConjugate b.first l w : b.first) : G) = (v : G)
    rw [← hact]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hu.2 (x : G) x.property)
  have horder : orderOf (projection m l) = 3 := by
    change orderOf (m.quotientIso (QuotientGroup.mk' (pCore 2 b.first) l)) = 3
    rw [m.quotientIso.orderOf_eq, hl]
  have hfix := congrArg Multiplicative.toAdd (m.intertwining l w).symm
  rw [hconj] at hfix
  have hzero := Matrix.SL2.cubic_fixed_eq_zero (projection m l) horder
    (m.moduleIso (QuotientGroup.mk' (blockFixed b.first) w)).toAdd hfix
  have hq : QuotientGroup.mk' (blockFixed b.first) w = 1 := by
    apply m.moduleIso.injective
    rw [map_one]
    exact Multiplicative.toAdd.injective hzero
  have hw : w ∈ blockFixed b.first := (QuotientGroup.eq_one_iff w).mp hq
  apply mem_centralizer_iff.mpr
  intro a ha
  exact congrArg Subtype.val (mem_center_iff.mp hw (⟨a, ha⟩ : b.first))

/-- The actual Sylow subgroup supplies the odd orbit required for the norm argument. -/
lemma fixed_seed_centralizes_first_of_layer (c : ContraryData κ d i j)
    (b : ExchangedBlock c)
    (helem : IsElementaryAbelian 2 (seedClosure c))
    (hdisp : ⁅seedClosure c, b.first⁆ ≤ firstLayer b)
    (hnorm : d.wholeX ≤ normalizer (b.first : Set G))
    (hfixed : firstLayer b ⊓ centralizer (d.wholeX : Set G) ≤ centralizer (b.first : Set G)) :
    d.Z ⊓ centralizer (d.wholeX : Set G) ≤ centralizer (b.first : Set G) := by
  let V := seedClosure c
  let := helem
  let ρ : c.H →* MulAut V :=
    V.normalizerMonoidHom.comp (inclusion (normalizes_seedClosure c))
  let : MulDistribMulAction c.H V := MulDistribMulAction.compHom V ρ
  let L := b.first.subgroupOf c.H
  let X := d.wholeX.subgroupOf c.H
  have hXL : X ≤ normalizer L := by
    intro x hx l
    exact hnorm hx (l : G)
  intro z hz
  let v : V := ⟨z, Z_le_seedClosure c hz.1⟩
  have hvX (x : X) : (x : c.H) • v = v := by
    apply Subtype.ext
    change ((x : c.H) : G) * z * (((x : c.H) : G))⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_iff.mp hz.2 ((x : c.H) : G) x.property)
  obtain ⟨P, hP⟩ := c.sylow.exists_subgroupOf_eq_of_subnormal L b.relative_block.subnormal
  have hPS : (P : Subgroup L) ≤ stabilizer L v := by
    intro l hl
    rw [hP] at hl
    apply Subtype.ext
    change (((l : L) : c.H) : G) * z * ((((l : L) : c.H) : G))⁻¹ = z
    have hlU : (((l : L) : c.H) : G) ∈ c.U := by
      rw [← c.sylow_image]
      exact ⟨l, hl, rfl⟩
    rw [mem_centralizer_iff.mp (c.fixed_seed_centralizes_U hz) _ hlU,
      mul_inv_cancel_right]
  have hodd : Odd (Nat.card (orbit L v)) := by
    have hi : ¬ 2 ∣ (stabilizer L v).index :=
      fun hd => P.not_dvd_index (hd.trans (index_dvd_of_le hPS))
    rw [Nat.card_congr (orbitEquivQuotientStabilizer L v)]
    exact Nat.not_even_iff_odd.mp (fun h => hi h.two_dvd)
  have hv2 : v ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 V) v
  have hdispl (l : L) : ((l : c.H) • v) / v ∈ (firstLayer b).subgroupOf V := by
    change (((l : c.H) : G) * z * (((l : c.H) : G))⁻¹) / z ∈ firstLayer b
    apply hdisp
    rw [commutator_comm]
    simpa only [commutatorElement_def, div_eq_mul_inv] using
      (commutator_mem_commutator
        (show ((l : c.H) : G) ∈ b.first from l.property)
        (show z ∈ seedClosure c from v.property))
  have hdFixed (w : V) (hw : w ∈ (firstLayer b).subgroupOf V)
      (hwX : ∀ x : X, (x : c.H) • w = w) :
      ∀ l : L, (l : c.H) • w = w := by
    have hwC : (w : G) ∈ centralizer (d.wholeX : Set G) := by
      apply mem_centralizer_iff.mpr
      intro x hx
      have he := congrArg Subtype.val (hwX ⟨⟨x, c.X_le_H hx⟩, hx⟩)
      change x * (w : G) * x⁻¹ = (w : G) at he
      exact mul_inv_eq_iff_eq_mul.mp he
    have hc := hfixed ⟨hw, hwC⟩
    intro l
    apply Subtype.ext
    change ((l : c.H) : G) * (w : G) * (((l : c.H) : G))⁻¹ = (w : G)
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_iff.mp hc ((l : c.H) : G) l.property)
  have hf := Theory.GroupAction.OddOrbitFixedPoints.fixed_of_odd_orbit L X hXL
    ((firstLayer b).subgroupOf V) v hvX hv2 hodd hdispl hdFixed
  apply mem_centralizer_iff.mpr
  intro l hl
  have he := congrArg Subtype.val (hf ⟨⟨l, b.first_le hl⟩, hl⟩)
  change l * z * l⁻¹ = z at he
  exact mul_inv_eq_iff_eq_mul.mp he

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality
