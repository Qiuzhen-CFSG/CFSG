module
public import Theory.SpecificGroups.SL3.PerfectCore
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.InitialAction

/-!
# The intrinsic two-core is the whole MS commutator outside field four

For n>2, perfection of the original component and its full SL₃ quotient
force O₂(K)=[O₂(K),K]. Indeed K/[O₂(K),K] is a perfect central cover of
SL₃ whose kernel is a two-group, and the ordinary scalar-cover theorem
removes it. The checked equality between intrinsic and ambient core
commutators therefore gives the literal msQ=O₂(K).

This applies even when msQ is nonabelian and uses no section-model premise.
Any failure of this equality in the nonbinary campaign is confined to n=2.
The original Chapter4 nonblock and Chapter11 point consumers use this
identification of their whole cores. Whole natural/dual recognition and
Sylow radical inequalities remain separate obligations.
Source: Aschbacher--Smith I.1.3, printed p.407, C.1.34, pp.136--137,
and original4.3.8--10 and11.1.5.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.IntrinsicCore
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)

include h in
omit [Finite G] in
private theorem component_perfect : Group.IsPerfect K := by
  let := h.component.2.perfect
  let e : K.subgroupOf (K ⊔ R) ≃* K := subgroupOfEquivOfLe (show K ≤ K ⊔ R from le_sup_left)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

include h hn in
/-- The common quotient uses the original MS commutator, through the literal
component inclusion. -/
theorem blockU_map_eq_msQ : (blockU K).map K.subtype = msQ K R := by
  rw [msQ_eq_intrinsic h hn,blockU,map_commutator,
    ←MonoidHom.range_eq_map,K.range_subtype]
  rfl

include h hn in
/-- Outside field four the actual MS commutator equals the entire intrinsic
two-core, with no abelianity or section-model premise. -/
theorem msQ_eq_componentCore (h4 : n ≠ 2) : msQ K R = K.pCoreIn 2 := by
  let := component_perfect h
  have h2F : Nat.card F ≠ 2 := by
    rw [h.field_card]
    have hh : 2^1 < 2^n := Nat.pow_lt_pow_right (by decide) hn
    omega
  have h4F : Nat.card F ≠ 4 := by
    rw [h.field_card]
    have hh : 2^2 < 2^n := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  have he : blockU K = pCore 2 K :=
    Matrix.SL3.PerfectCore.commutator_eq_core (Classical.choice h.model) h2F h4F
  rw [←blockU_map_eq_msQ h hn,he]
  rfl

include h hn in
/-- In the nonbinary campaign a larger intrinsic two-core is confined to
field four; it cannot occur at a larger field. -/
theorem degree_eq_two_of_core_ne (hne : msQ K R ≠ K.pCoreIn 2) : n = 2 := by
  by_contra h4
  exact hne (msQ_eq_componentCore h hn h4)

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.IntrinsicCore
