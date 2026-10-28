module

public import Theory.GroupTheory.ExponentFourSylowSections
public import Theory.SpecificGroups.Classical.SmallSylowEightOrders
public import CFSG.Quasithin.ClassicalModels

/-!
# The odd PSL2 profile under a split Sylow of order sixteen

The actual quotient map transfers the fourth-power identity of C2 times
D8 to a Sylow subgroup of the component quotient. Its genuine dihedral
presentation then has rotation order at most four. The quotient Sylow
has order at most eight and the precise field congruences follow from
its actual order formula.

Source: Aschbacher--Smith F.6.18(8)--(9), printed p.310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.ClassicalSmallSylow
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve
variable {G : Type*} [Group G] [Finite G]

/-- The original central quotient cannot have a larger odd-PSL2 Sylow,
since its order-eight rotation would violate the ambient power identity. -/
theorem odd_pslTwo_central_quotient_sylow_le_eight
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) {q : ℕ} (hq : GorensteinWalter.IsOddPrimePower q)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 q)
    (P : Sylow 2 (K ⧸ center K)) : Nat.card P ≤ 8 := by
  obtain ⟨F, _, _, hF, ⟨j⟩⟩ := hm
  let S := P.mapSurjective (f := j.toMonoidHom) j.surjective
  let a : P ≃* S := j.subgroupMap (P : Subgroup (K ⧸ center K))
  obtain ⟨m, _, ⟨eS⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F
    (hF ▸ hq) S
  let b := a.trans eS
  have hb : (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) ^ 4 = 1 := by
    have hx := split_sixteen_sylow_section_pow_four T eT K
      (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective (center K)) P
      (b.symm (DihedralGroup.r 1))
    simpa only [map_pow, b.apply_symm_apply, map_one] using congrArg b hx
  have hd := orderOf_dvd_of_pow_eq_one hb
  rw [DihedralGroup.orderOf_r_one] at hd
  have hm4 : 2 ^ m ≤ 4 := Nat.le_of_dvd (by decide) hd
  rw [Nat.card_congr b.toEquiv, DihedralGroup.nat_card]
  omega

/-- The exact field congruence alternatives on the original component quotient. -/
theorem odd_pslTwo_central_quotient_profile
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) {q : ℕ} (hq : GorensteinWalter.IsOddPrimePower q)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 q)
    (P : Sylow 2 (K ⧸ center K)) :
    (Nat.card P = 4 ∧ (q % 8 = 3 ∨ q % 8 = 5)) ∨
    (Nat.card P = 8 ∧ (q % 16 = 7 ∨ q % 16 = 9)) := by
  have hp := odd_pslTwo_central_quotient_sylow_le_eight T eT K hq hm P
  obtain ⟨F, _, _, hF, ⟨j⟩⟩ := hm
  let S := P.mapSurjective (f := j.toMonoidHom) j.surjective
  let a : P ≃* S := j.subgroupMap (P : Subgroup (K ⧸ center K))
  have ha : Nat.card S = Nat.card P := Nat.card_congr a.symm.toEquiv
  simpa only [hF, ha] using psl2_small_sylow_parameters (hF ▸ hq) S (ha ▸ hp)

end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve
