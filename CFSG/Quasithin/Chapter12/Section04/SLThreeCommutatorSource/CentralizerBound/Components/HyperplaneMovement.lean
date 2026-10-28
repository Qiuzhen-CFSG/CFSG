module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Preparation
public import Mathlib.GroupTheory.IndexNormal

/-!
# Involutions move the escaping hyperplane

A hyperplane invariant under an automorphism has trivial induced action on
its binary quotient, so it contains the displacement. For an involution in
the marked SL₃(2) action the displacement is its fixed plane, which contains
the original fixed line. The escaping hyperplane misses that line.
Source: Aschbacher--Smith, 12.4.8, printed p.815, using B.4.8(2).
-/
public section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter12.Section04.SmallFusion
open CFSG.Quasithin.ChapterE
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

/-- A lift of a marked involution cannot stabilize the escaping hyperplane. -/
theorem Configuration.involution_moves_hyperplane (c : Configuration T L V U)
    (l : L)
    (hb : orderOf (c.extension.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) = 2) :
    (l : G) ∉ normalizer (U : Set G) := by
  let _ := c.chosen.elementary
  let E := c.extension
  let b := E.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)
  let R := U.subgroupOf V
  have hi : R.index = 2 := by
    change U.relIndex V = 2
    rw [relIndex_eq_two_pow_quotient_finrank,← subgroupCorank_eq_quotient_finrank,c.corank,pow_one]
  intro hn
  have hdelta (v : Additive V) : ((E.action b v - v).toMul : G) ∈ U := by
    change (E.action b v).toMul / v.toMul ∈ R
    rw [div_eq_mul_inv]
    apply (R.mul_mem_iff_of_index_two hi).mpr
    change ((E.action b v).toMul : G) ∈ U ↔ (v.toMul⁻¹ : G) ∈ U
    rw [E.conjugation]
    exact ((mem_normalizer_iff.mp hn (v.toMul : G)).symm).trans U.inv_mem_iff.symm
  have hout := (escaping_subspaces c.hypothesis c.structural E c.fixed_nontrivial
    c.normalizer_action c.le_module c.corank c.escape).2.1
  apply hout
  intro z hz
  let zV : Additive V := Additive.ofMul ⟨z,hz.1⟩
  have hfix : zV ∈ BinaryOffender.fixedSpace E.action (zpowers b) :=
    fun a => (E.mem_fixed_iff zV).mpr hz.2 a
  rw [← (involution_linear_plane E c.fixed_nontrivial b hb).1] at hfix
  obtain ⟨v,hv⟩ := hfix
  have he := congrArg (fun w : Additive V => (w.toMul : G)) hv
  change ((E.action b v - v).toMul : G) = z at he
  exact he ▸ hdelta v
end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
