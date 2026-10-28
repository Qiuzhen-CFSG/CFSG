module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.QuotientBasisSource
public import Theory.GroupTheory.NormalizerQuotientOuterPair
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms

/-!
# The actual cyclic outer coordinates of the paired linear source

Conjugation on the first block modulo its two-core gives a cyclic outer
coordinate on its index-two stabilizer. An element outside the stabilizer
supplies the second coordinate by conjugation. Their joint kernel is the
original two-residual: the linear quotient is centerless, the two factors
commute, and the completed torus geometry places O₂(H) inside L₀.

This discharges the field-coordinate premise in Aschbacher--Smith, the
proof of 2.4.7 on printed p.540, using the actual original block and maps.
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter2
private theorem linear_outer_cyclic {L : Type*} [Group L] [Finite L] {n : ℕ}
    (hL : CFSG.Quasithin.ChapterC.IsL2EvenBlock L n) :
    center (L ⧸ pCore 2 L) = ⊥ ∧ IsCyclic (MulAut.Outer (L ⧸ pCore 2 L)) := by
  obtain ⟨F, _, _, hF, _, _, ⟨m⟩, _⟩ := hL.2.2
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let e : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group F :=
    m.quotientIso.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL
  have hc : center (L ⧸ pCore 2 L) = ⊥ := by
    apply eq_bot_iff.mpr
    intro k hk
    have hh := (centerCongr m.quotientIso ⟨k,hk⟩).property
    change m.quotientIso k ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) at hh
    rw [Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot, mem_bot] at hh
    exact mem_bot.mpr (m.quotientIso.injective (hh.trans m.quotientIso.map_one.symm))
  let : IsCyclic (MulAut.Outer (Theory.PSL2.Group F)) := Theory.PSL2.outer_isCyclic F
  exact ⟨hc,(MulAut.outerCongr e).isCyclic.mpr inferInstance⟩


open LinearDouble ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {M₀ : Subgroup G} {n : ℕ}

theorem DoubleLinearSourceSetup.outer_pair
    (c : DoubleLinearSourceSetup d M₀ n) (td : SourceTorusData c)
    (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n) :
    let B := normalizer (d.block : Set d.H)
    let : B.Normal := normal_of_index_eq_two c.parabolic_stabilizer_index
    let C := MulAut.Outer (d.block ⧸ pCore 2 d.block)
    IsCyclic C ∧ ∃ f : B →* C,
      d.L0.subgroupOf B ≤ f.ker ∧
      ∀ x : d.H, x ∉ B → ∀ b : B,
        f b = 1 → f (MulAut.conjNormal x b) = 1 → (b:d.H) ∈ d.L0 := by
  let B := normalizer (d.block : Set d.H)
  let : B.Normal := normal_of_index_eq_two c.parabolic_stabilizer_index
  let : d.L0.Normal := d.L0_normal
  let J := c.second.subgroupOf d.H
  have hsecond : c.second ≤ d.H := (le_sup_right.trans_eq c.join).trans (map_subtype_le _)
  have hjoin : d.block ⊔ J = d.L0 := by
    apply map_injective d.H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hsecond]
    exact c.join
  have hcomm : J ≤ centralizer (d.block : Set d.H) := by
    intro j hj l hl
    apply Subtype.ext
    exact c.commutes hj (l:G) (mem_map_of_mem d.H.subtype hl)
  have hLN : d.block ≤ d.L0 := le_sup_left.trans_eq hjoin
  have hcore : pCore 2 d.H ≤ d.L0 := by
    intro y hy
    apply (mem_map_iff_mem d.H.subtype_injective).mp
    have hQ : twoCore d.H ≤ d.L0.map d.H.subtype := by
      rw [td.geometry.core,←c.join]
      exact sup_le_sup (map_subtype_le _) (map_subtype_le _)
    exact hQ (mem_map_of_mem d.H.subtype hy)
  have hq : IsPGroup 2 (d.H ⧸ d.L0) := by
    exact (isPGroup_quotient_pResidual (G:=d.H) 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq d.L0_eq_residual.symm)
  have htype : ChapterC.IsL2EvenBlock d.block n :=
    hL.of_mulEquiv (d.block.equivMapOfInjective d.H.subtype d.H.subtype_injective).symm
  obtain ⟨hc,hcyc⟩ := linear_outer_cyclic htype
  let f := (QuotientGroup.mk' (MulAut.innerSubgroup (d.block ⧸ pCore 2 d.block))).comp
    (normalizerPCoreQuotientAction d.block)
  refine ⟨hcyc,f,normalizerPCoreQuotient_outer_kernel d.block J d.L0 hjoin hcomm
    c.residual_le_parabolic_stabilizer,?_⟩
  intro x hx b hb₁ hb₂
  exact normalizerPCoreQuotient_inner_pair d.block J d.L0 hLN hjoin hcomm hq hcore hc x
    (c.parabolic_outside_exchanges_intrinsic x hx)
    (c.parabolic_outside_exchanges_intrinsic x⁻¹ (by simpa only [inv_mem_iff] using hx))
    b ((QuotientGroup.eq_one_iff _).mp hb₁) ((QuotientGroup.eq_one_iff _).mp hb₂)

end CFSG.Quasithin.Chapter2
