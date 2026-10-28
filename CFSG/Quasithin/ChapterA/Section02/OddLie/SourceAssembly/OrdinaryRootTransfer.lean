module
public import Theory.SpecificGroups.SL2.OrdinaryCentralLift
public import Theory.GroupTheory.NonsolvableTwoLocal
public import CFSG.Quasithin.ChapterA.Section02.OddLie.RootCoverTransfer
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.CubicObstruction

/-!
# Ordinary root transfer in source A.2.17

Away from the exceptional SL₂ orders 3 and 9, universality lifts the
actual root subgroup through a central quotient. Its full centralizer
image gives the source complementary rank bounds using quasithinness of
the original group, without any restriction on the kernel prime.
-/

open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
variable {G H F : Type*} [Group G] [Finite G] [Group H] [Field F] [Finite F]

/-- Ordinary SL₂ universality bounds the actual quotient centralizer without
a defining-prime-free hypothesis on the central kernel. -/
public theorem ordinary_root_centralizer_rank_le_one
    {r s : ℕ} [Fact r.Prime] [CharP F r] [Fact s.Prime]
    (hr : r ≠ 2) (hs : Odd s) (hF : Odd (Nat.card F))
    (hgt : 3 < Nat.card F) (h9 : Nat.card F ≠ 9)
    (π : G →* H) (hπ : Function.Surjective π) (hc : π.ker ≤ center G)
    (j : SL(2,F) →* H) (hj : Function.Injective j) (hqt : IsQuasithin G)
    (hdiv : s ∣ Nat.card SL(2,F)) :
    primeRank s (centralizer (j.range : Set H)) ≤ 1 := by
  obtain ⟨k,hk,_,hC⟩ := SpecialLinearGroup.exists_ordinary_lift_centralizer_image
    hF hgt h9 π hπ hc j hj
  let eC := MulEquiv.subgroupCongr hC
  let f := eC.toMonoidHom.comp (π.subgroupMap (centralizer (k.range : Set G)))
  have hf : Function.Surjective f :=
    eC.surjective.comp (π.subgroupMap_surjective (centralizer (k.range : Set G)))
  exact (RootCoverTransfer.sl2_complementary_primeRank_le_one hr hs hF k hk
    (centralizer (k.range : Set G)) le_rfl hdiv
    (fun z hz hz2 => Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hqt _
      (Theory.GroupTheory.isTwoLocal_involution_centralizer (orderOf_eq_prime hz2 hz))
      s Fact.out hs) f hf).2

/-- The literal ordinary root subgroup yields the source field-degree and
both complementary rank bounds in any central quotient of the original QT
group, including central kernels divisible by the defining prime. -/
public theorem ordinary_root_source_bounds
    {r e : ℕ} [Fact r.Prime] [CharP F r]
    (hr : Odd r) (he : 1 ≤ e) (hcard : Nat.card F = r^e)
    (hgt : 3 < Nat.card F) (h9 : Nat.card F ≠ 9)
    (π : G →* H) (hπ : Function.Surjective π) (hc : π.ker ≤ center G)
    (j : SL(2,F) →* H) (hj : Function.Injective j) (hqt : IsQuasithin G) :
    e ≤ 2 ∧ primeRank r (centralizer (j.range : Set H)) ≤ 1 ∧
      primeRank 3 (centralizer (j.range : Set H)) ≤ 1 := by
  have hF : Odd (Nat.card F) := hcard ▸ hr.pow
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  obtain ⟨k,hk,_⟩ := SpecialLinearGroup.exists_ordinary_central_lift hF hgt h9 π hπ hc j hj
  obtain ⟨hz,hz2⟩ := SpecialLinearGroup.map_neg_one_isInvolution hr2 k hk
  have he2 := (SpecialLinearGroup.fieldExponent_le_primeRank_centralizer hcard k hk).trans
    (Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hqt _
      (Theory.GroupTheory.isTwoLocal_involution_centralizer (orderOf_eq_prime hz2 hz))
      r Fact.out hr)
  refine ⟨he2,ordinary_root_centralizer_rank_le_one hr2 hr hF hgt h9 π hπ hc j hj hqt ?_,
    ordinary_root_centralizer_rank_le_one hr2 (by decide : Odd 3) hF hgt h9 π hπ hc j hj hqt ?_⟩
  · rw [GorensteinWalter.sl2_card_formula F,hcard]
    exact dvd_mul_of_dvd_left (dvd_pow_self r (by omega)) _
  · rw [← ClassicalOrthogonal.Fundamental.cubicSL_order (F := F)]
    exact orderOf_dvd_natCard _
end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
